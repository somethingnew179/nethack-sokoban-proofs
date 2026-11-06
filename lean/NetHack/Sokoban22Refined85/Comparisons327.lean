/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons326
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare45780 (p : Pattern) (guard : d8100 p = 1) : d3226 p ≤ (0 : Int) + d351 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45779 p hg
    simpa only [d8100, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44919 p hg
    simpa only [d8100, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45781 (p : Pattern) (guard : d8106 p = 1) : d3238 p ≤ (0 : Int) + d352 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3238, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45780 p hg
    simpa only [d8106, d3238, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3238, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44967 p hg
    simpa only [d8106, d3238, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45782 (p : Pattern) (guard : d5847 p = 1) : d3250 p ≤ (0 : Int) + d315 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3250, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35654 p hg
    simpa only [d5847, d3250, d315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3250, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5847, d3250, d315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45783 (p : Pattern) (guard : d5854 p = 1) : d3250 p ≤ (0 : Int) + d320 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45782 p hg
    simpa only [d5854, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26644 p hg
    simpa only [d5854, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45784 (p : Pattern) (guard : d8099 p = 1) : d3250 p ≤ (0 : Int) + d321 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45783 p hg
    simpa only [d8099, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26644 p hg
    simpa only [d8099, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45785 (p : Pattern) (guard : d8105 p = 1) : d3250 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45784 p hg
    simpa only [d8105, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26644 p hg
    simpa only [d8105, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45786 (p : Pattern) (guard : d8111 p = 1) : d3275 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3275, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45785 p hg
    simpa only [d8111, d3275, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3275, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44989 p hg
    simpa only [d8111, d3275, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45787 (p : Pattern) (guard : d8112 p = 1) : d3306 p ≤ (0 : Int) + d355 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3306, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45781 p hg
    simpa only [d8112, d3306, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3306, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45786 p hg
    simpa only [d8112, d3306, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45788 (p : Pattern) (guard : d5847 p = 1) : d3239 p ≤ (0 : Int) + d356 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3239, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35661 p hg
    simpa only [d5847, d3239, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3239, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5847, d3239, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45789 (p : Pattern) (guard : d5854 p = 1) : d3239 p ≤ (0 : Int) + d357 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45788 p hg
    simpa only [d5854, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26627 p hg
    simpa only [d5854, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45790 (p : Pattern) (guard : d8099 p = 1) : d3239 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45789 p hg
    simpa only [d8099, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26627 p hg
    simpa only [d8099, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45791 (p : Pattern) (guard : d8105 p = 1) : d3239 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45790 p hg
    simpa only [d8105, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26627 p hg
    simpa only [d8105, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45792 (p : Pattern) (guard : d8111 p = 1) : d3241 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3241, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45791 p hg
    simpa only [d8111, d3241, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3241, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44970 p hg
    simpa only [d8111, d3241, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45793 (p : Pattern) (guard : d8117 p = 1) : d3277 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3277, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45792 p hg
    simpa only [d8117, d3277, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3277, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44992 p hg
    simpa only [d8117, d3277, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45794 (p : Pattern) (guard : d8118 p = 1) : d3307 p ≤ (0 : Int) + d362 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3307, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45787 p hg
    simpa only [d8118, d3307, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3307, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45793 p hg
    simpa only [d8118, d3307, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45795 (p : Pattern) (guard : d8117 p = 1) : d3282 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3282, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45635 p hg
    simpa only [d8117, d3282, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3282, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44995 p hg
    simpa only [d8117, d3282, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45796 (p : Pattern) (guard : d8123 p = 1) : d3285 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d3285, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45795 p hg
    simpa only [d8123, d3285, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d3285, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44997 p hg
    simpa only [d8123, d3285, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45797 (p : Pattern) (guard : d8124 p = 1) : d3308 p ≤ (0 : Int) + d395 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d3308, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45794 p hg
    simpa only [d8124, d3308, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d3308, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45796 p hg
    simpa only [d8124, d3308, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45798 (p : Pattern) (guard : d8111 p = 1) : d3255 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3255, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45676 p hg
    simpa only [d8111, d3255, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3255, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44978 p hg
    simpa only [d8111, d3255, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45799 (p : Pattern) (guard : d0 p = 1) : d3287 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare45800 (p : Pattern) (guard : d8117 p = 1) : d3288 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3288, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45798 p hg
    simpa only [d8117, d3288, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3288, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45799 p hg
    simpa only [d8117, d3288, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45801 (p : Pattern) (guard : d0 p = 1) : d3289 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare45802 (p : Pattern) (guard : d8123 p = 1) : d3290 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d3290, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45800 p hg
    simpa only [d8123, d3290, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d3290, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45801 p hg
    simpa only [d8123, d3290, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45803 (p : Pattern) (guard : d0 p = 1) : d3295 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare45804 (p : Pattern) (guard : d8129 p = 1) : d3296 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d3296, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45802 p hg
    simpa only [d8129, d3296, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d3296, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45803 p hg
    simpa only [d8129, d3296, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45805 (p : Pattern) (guard : d8130 p = 1) : d3329 p ≤ (0 : Int) + d397 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d3329, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45797 p hg
    simpa only [d8130, d3329, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d3329, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45804 p hg
    simpa only [d8130, d3329, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45806 (p : Pattern) (guard : d8131 p = 1) : d3330 p ≤ (0 : Int) + d419 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d3330, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45776 p hg
    simpa only [d8131, d3330, d419, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d3330, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45805 p hg
    simpa only [d8131, d3330, d419, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45807 (p : Pattern) (guard : d0 p = 1) : d3241 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare45808 (p : Pattern) (guard : d8117 p = 1) : d3242 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45651 p hg
    simpa only [d8117, d3242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45807 p hg
    simpa only [d8117, d3242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45809 (p : Pattern) (guard : d8118 p = 1) : d3299 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3299, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45678 p hg
    simpa only [d8118, d3299, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3299, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45808 p hg
    simpa only [d8118, d3299, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45810 (p : Pattern) (guard : d0 p = 1) : d3247 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare45811 (p : Pattern) (guard : d8123 p = 1) : d3248 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d3248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45808 p hg
    simpa only [d8123, d3248, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d3248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45810 p hg
    simpa only [d8123, d3248, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45812 (p : Pattern) (guard : d8124 p = 1) : d3300 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d3300, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45809 p hg
    simpa only [d8124, d3300, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d3300, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45811 p hg
    simpa only [d8124, d3300, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45813 (p : Pattern) (guard : d8129 p = 1) : d3304 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d3304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45656 p hg
    simpa only [d8129, d3304, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d3304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8129, d3304, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45814 (p : Pattern) (guard : d8130 p = 1) : d3305 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d3305, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45812 p hg
    simpa only [d8130, d3305, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d3305, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45813 p hg
    simpa only [d8130, d3305, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45815 (p : Pattern) (guard : d5847 p = 1) : d3226 p ≤ (0 : Int) + d329 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3226, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34137 p hg
    simpa only [d5847, d3226, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3226, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5847, d3226, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45816 (p : Pattern) (guard : d5854 p = 1) : d3226 p ≤ (0 : Int) + d330 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45815 p hg
    simpa only [d5854, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26609 p hg
    simpa only [d5854, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45817 (p : Pattern) (guard : d8099 p = 1) : d3226 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45816 p hg
    simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26609 p hg
    simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45818 (p : Pattern) (guard : d8105 p = 1) : d3226 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45817 p hg
    simpa only [d8105, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26609 p hg
    simpa only [d8105, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45819 (p : Pattern) (guard : d8111 p = 1) : d3238 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3238, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45818 p hg
    simpa only [d8111, d3238, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3238, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45650 p hg
    simpa only [d8111, d3238, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45820 (p : Pattern) (guard : d8117 p = 1) : d3306 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3306, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45819 p hg
    simpa only [d8117, d3306, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3306, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45663 p hg
    simpa only [d8117, d3306, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45821 (p : Pattern) (guard : d0 p = 1) : d3277 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare45822 (p : Pattern) (guard : d8123 p = 1) : d3307 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d3307, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45820 p hg
    simpa only [d8123, d3307, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d3307, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45821 p hg
    simpa only [d8123, d3307, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45823 (p : Pattern) (guard : d0 p = 1) : d3285 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare45824 (p : Pattern) (guard : d8129 p = 1) : d3308 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d3308, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45822 p hg
    simpa only [d8129, d3308, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d3308, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45823 p hg
    simpa only [d8129, d3308, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45825 (p : Pattern) (guard : d0 p = 1) : d3311 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare45826 (p : Pattern) (guard : d8135 p = 1) : d3312 p ≤ (0 : Int) + d421 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d3312, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45824 p hg
    simpa only [d8135, d3312, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d3312, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45825 p hg
    simpa only [d8135, d3312, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45827 (p : Pattern) (guard : d8136 p = 1) : d3313 p ≤ (0 : Int) + d422 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d3313, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45814 p hg
    simpa only [d8136, d3313, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d3313, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45826 p hg
    simpa only [d8136, d3313, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45828 (p : Pattern) (guard : d8137 p = 1) : d3331 p ≤ (0 : Int) + d423 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d3331, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45806 p hg
    simpa only [d8137, d3331, d423, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d3331, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45827 p hg
    simpa only [d8137, d3331, d423, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45829 (p : Pattern) (guard : d8112 p = 1) : d3238 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45578 p hg
    simpa only [d8112, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45819 p hg
    simpa only [d8112, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45830 (p : Pattern) (guard : d8117 p = 1) : d3242 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3242, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45677 p hg
    simpa only [d8117, d3242, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3242, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45807 p hg
    simpa only [d8117, d3242, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45831 (p : Pattern) (guard : d8118 p = 1) : d3299 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3299, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45829 p hg
    simpa only [d8118, d3299, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3299, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45830 p hg
    simpa only [d8118, d3299, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45832 (p : Pattern) (guard : d8124 p = 1) : d3300 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d3300, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45831 p hg
    simpa only [d8124, d3300, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d3300, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45811 p hg
    simpa only [d8124, d3300, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45833 (p : Pattern) (guard : d8130 p = 1) : d3305 p ≤ (0 : Int) + d399 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d3305, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45832 p hg
    simpa only [d8130, d3305, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d3305, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45813 p hg
    simpa only [d8130, d3305, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45834 (p : Pattern) (guard : d5847 p = 1) : d3226 p ≤ (0 : Int) + d356 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3226, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34173 p hg
    simpa only [d5847, d3226, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3226, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5847, d3226, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45835 (p : Pattern) (guard : d5854 p = 1) : d3226 p ≤ (0 : Int) + d357 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45834 p hg
    simpa only [d5854, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26609 p hg
    simpa only [d5854, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45836 (p : Pattern) (guard : d8099 p = 1) : d3226 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45835 p hg
    simpa only [d8099, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26609 p hg
    simpa only [d8099, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45837 (p : Pattern) (guard : d8105 p = 1) : d3226 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45836 p hg
    simpa only [d8105, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26609 p hg
    simpa only [d8105, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45838 (p : Pattern) (guard : d8111 p = 1) : d3238 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3238, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45837 p hg
    simpa only [d8111, d3238, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3238, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45650 p hg
    simpa only [d8111, d3238, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45839 (p : Pattern) (guard : d8117 p = 1) : d3306 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3306, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45838 p hg
    simpa only [d8117, d3306, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3306, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45663 p hg
    simpa only [d8117, d3306, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45840 (p : Pattern) (guard : d8123 p = 1) : d3307 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d3307, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45839 p hg
    simpa only [d8123, d3307, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d3307, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45821 p hg
    simpa only [d8123, d3307, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45841 (p : Pattern) (guard : d8129 p = 1) : d3308 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d3308, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45840 p hg
    simpa only [d8129, d3308, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d3308, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45823 p hg
    simpa only [d8129, d3308, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45842 (p : Pattern) (guard : d8135 p = 1) : d3312 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d3312, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45841 p hg
    simpa only [d8135, d3312, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d3312, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45825 p hg
    simpa only [d8135, d3312, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45843 (p : Pattern) (guard : d8136 p = 1) : d3313 p ≤ (0 : Int) + d424 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d3313, d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45833 p hg
    simpa only [d8136, d3313, d424, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d3313, d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45842 p hg
    simpa only [d8136, d3313, d424, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45844 (p : Pattern) (guard : d8142 p = 1) : d3332 p ≤ (0 : Int) + d425 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8136 p = 1 := by simpa only [d8142, d3332, d425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45843 p hg
    simpa only [d8142, d3332, d425, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8141 p = 1 := by simpa only [d8142, d3332, d425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37397 p hg
    simpa only [d8142, d3332, d425, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45845 (p : Pattern) (guard : d8143 p = 1) : d3333 p ≤ (0 : Int) + d426 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8137 p = 1 := by simpa only [d8143, d3333, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45828 p hg
    simpa only [d8143, d3333, d426, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8142 p = 1 := by simpa only [d8143, d3333, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45844 p hg
    simpa only [d8143, d3333, d426, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45846 (p : Pattern) (guard : d8144 p = 1) : d3334 p ≤ (0 : Int) + d427 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8138 p = 1 := by simpa only [d8144, d3334, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45759 p hg
    simpa only [d8144, d3334, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8143 p = 1 := by simpa only [d8144, d3334, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45845 p hg
    simpa only [d8144, d3334, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45847 (p : Pattern) (guard : d8085 p = 1) : d3359 p ≤ (0 : Int) + d430 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d3359, d430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45156 p hg
    simpa only [d8085, d3359, d430, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d3359, d430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45279 p hg
    simpa only [d8085, d3359, d430, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45848 (p : Pattern) (guard : d8090 p = 1) : d3360 p ≤ (0 : Int) + d431 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d3360, d431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45847 p hg
    simpa only [d8090, d3360, d431, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d3360, d431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45318 p hg
    simpa only [d8090, d3360, d431, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45849 (p : Pattern) (guard : d8095 p = 1) : d3361 p ≤ (0 : Int) + d432 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d3361, d432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45848 p hg
    simpa only [d8095, d3361, d432, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d3361, d432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45281 p hg
    simpa only [d8095, d3361, d432, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45850 (p : Pattern) (guard : d8100 p = 1) : d3362 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3362, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45319 p hg
    simpa only [d8100, d3362, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3362, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d3362, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45851 (p : Pattern) (guard : d8101 p = 1) : d3363 p ≤ (0 : Int) + d433 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3363, d433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45849 p hg
    simpa only [d8101, d3363, d433, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3363, d433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45850 p hg
    simpa only [d8101, d3363, d433, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45852 (p : Pattern) (guard : d8084 p = 1) : d3358 p ≤ (0 : Int) + d339 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d3358, d339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35107 p hg
    simpa only [d8084, d3358, d339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d3358, d339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d8084, d3358, d339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45853 (p : Pattern) (guard : d8089 p = 1) : d3358 p ≤ (0 : Int) + d340 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45852 p hg
    simpa only [d8089, d340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45164 p hg
    simpa only [d8089, d340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45854 (p : Pattern) (guard : d8094 p = 1) : d3358 p ≤ (0 : Int) + d341 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45853 p hg
    simpa only [d8094, d341, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45444 p hg
    simpa only [d8094, d341, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45855 (p : Pattern) (guard : d8100 p = 1) : d3358 p ≤ (0 : Int) + d342 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45854 p hg
    simpa only [d8100, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45228 p hg
    simpa only [d8100, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45856 (p : Pattern) (guard : d8105 p = 1) : d3362 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d3362, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45445 p hg
    simpa only [d8105, d3362, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d3362, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d3362, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45857 (p : Pattern) (guard : d8106 p = 1) : d3364 p ≤ (0 : Int) + d344 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3364, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45855 p hg
    simpa only [d8106, d3364, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3364, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45856 p hg
    simpa only [d8106, d3364, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45858 (p : Pattern) (guard : d8107 p = 1) : d3365 p ≤ (0 : Int) + d434 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3365, d434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45851 p hg
    simpa only [d8107, d3365, d434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3365, d434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45857 p hg
    simpa only [d8107, d3365, d434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45859 (p : Pattern) (guard : d8084 p = 1) : d3358 p ≤ (0 : Int) + d348 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d3358, d348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35121 p hg
    simpa only [d8084, d3358, d348, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d3358, d348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d8084, d3358, d348, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45860 (p : Pattern) (guard : d8089 p = 1) : d3358 p ≤ (0 : Int) + d349 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45859 p hg
    simpa only [d8089, d349, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45164 p hg
    simpa only [d8089, d349, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45861 (p : Pattern) (guard : d8094 p = 1) : d3358 p ≤ (0 : Int) + d350 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45860 p hg
    simpa only [d8094, d350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45176 p hg
    simpa only [d8094, d350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45862 (p : Pattern) (guard : d8100 p = 1) : d3358 p ≤ (0 : Int) + d351 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45861 p hg
    simpa only [d8100, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45228 p hg
    simpa only [d8100, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45863 (p : Pattern) (guard : d8106 p = 1) : d3364 p ≤ (0 : Int) + d352 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3364, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45862 p hg
    simpa only [d8106, d3364, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3364, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45295 p hg
    simpa only [d8106, d3364, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45864 (p : Pattern) (guard : d5847 p = 1) : d3366 p ≤ (0 : Int) + d315 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3366, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35713 p hg
    simpa only [d5847, d3366, d315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3366, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5847, d3366, d315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45865 (p : Pattern) (guard : d5854 p = 1) : d3366 p ≤ (0 : Int) + d320 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45864 p hg
    simpa only [d5854, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26786 p hg
    simpa only [d5854, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45866 (p : Pattern) (guard : d8099 p = 1) : d3366 p ≤ (0 : Int) + d321 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45865 p hg
    simpa only [d8099, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26786 p hg
    simpa only [d8099, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45867 (p : Pattern) (guard : d8105 p = 1) : d3366 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45866 p hg
    simpa only [d8105, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26786 p hg
    simpa only [d8105, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45868 (p : Pattern) (guard : d8111 p = 1) : d3368 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3368, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45867 p hg
    simpa only [d8111, d3368, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3368, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45299 p hg
    simpa only [d8111, d3368, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45869 (p : Pattern) (guard : d8112 p = 1) : d3369 p ≤ (0 : Int) + d355 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3369, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45863 p hg
    simpa only [d8112, d3369, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3369, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45868 p hg
    simpa only [d8112, d3369, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45870 (p : Pattern) (guard : d8113 p = 1) : d3370 p ≤ (0 : Int) + d435 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d3370, d435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45858 p hg
    simpa only [d8113, d3370, d435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d3370, d435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45869 p hg
    simpa only [d8113, d3370, d435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45871 (p : Pattern) (guard : d5847 p = 1) : d3366 p ≤ (0 : Int) + d356 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3366, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35721 p hg
    simpa only [d5847, d3366, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3366, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5847, d3366, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45872 (p : Pattern) (guard : d5854 p = 1) : d3366 p ≤ (0 : Int) + d357 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45871 p hg
    simpa only [d5854, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26786 p hg
    simpa only [d5854, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45873 (p : Pattern) (guard : d8099 p = 1) : d3366 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45872 p hg
    simpa only [d8099, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26786 p hg
    simpa only [d8099, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45874 (p : Pattern) (guard : d8105 p = 1) : d3366 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45873 p hg
    simpa only [d8105, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26786 p hg
    simpa only [d8105, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45875 (p : Pattern) (guard : d8111 p = 1) : d3368 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3368, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45874 p hg
    simpa only [d8111, d3368, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3368, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45299 p hg
    simpa only [d8111, d3368, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45876 (p : Pattern) (guard : d8112 p = 1) : d3369 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3369, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45403 p hg
    simpa only [d8112, d3369, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3369, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45875 p hg
    simpa only [d8112, d3369, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45877 (p : Pattern) (guard : d8117 p = 1) : d3371 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3371, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45270 p hg
    simpa only [d8117, d3371, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3371, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8117, d3371, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45878 (p : Pattern) (guard : d8118 p = 1) : d3372 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3372, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45876 p hg
    simpa only [d8118, d3372, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3372, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45877 p hg
    simpa only [d8118, d3372, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45879 (p : Pattern) (guard : d8119 p = 1) : d3373 p ≤ (0 : Int) + d436 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d3373, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45870 p hg
    simpa only [d8119, d3373, d436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d3373, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45878 p hg
    simpa only [d8119, d3373, d436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45880 (p : Pattern) (guard : d8106 p = 1) : d3376 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3376, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45358 p hg
    simpa only [d8106, d3376, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3376, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45260 p hg
    simpa only [d8106, d3376, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45881 (p : Pattern) (guard : d8111 p = 1) : d3379 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3379, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45465 p hg
    simpa only [d8111, d3379, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3379, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45311 p hg
    simpa only [d8111, d3379, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45882 (p : Pattern) (guard : d8112 p = 1) : d3380 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3380, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45880 p hg
    simpa only [d8112, d3380, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3380, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45881 p hg
    simpa only [d8112, d3380, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45883 (p : Pattern) (guard : d8111 p = 1) : d3381 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3381, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45446 p hg
    simpa only [d8111, d3381, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3381, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8111, d3381, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45884 (p : Pattern) (guard : d8117 p = 1) : d3383 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3383, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45883 p hg
    simpa only [d8117, d3383, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3383, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45392 p hg
    simpa only [d8117, d3383, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45885 (p : Pattern) (guard : d8118 p = 1) : d3384 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3384, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45882 p hg
    simpa only [d8118, d3384, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3384, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45884 p hg
    simpa only [d8118, d3384, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45886 (p : Pattern) (guard : d8124 p = 1) : d3387 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d3387, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45885 p hg
    simpa only [d8124, d3387, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d3387, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45396 p hg
    simpa only [d8124, d3387, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45887 (p : Pattern) (guard : d8125 p = 1) : d3388 p ≤ (0 : Int) + d437 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d3388, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45879 p hg
    simpa only [d8125, d3388, d437, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d3388, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45886 p hg
    simpa only [d8125, d3388, d437, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45888 (p : Pattern) (guard : d8084 p = 1) : d3389 p ≤ (0 : Int) + d326 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d3389, d326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35200 p hg
    simpa only [d8084, d3389, d326, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d3389, d326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19939 p hg
    simpa only [d8084, d3389, d326, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45889 (p : Pattern) (guard : d8089 p = 1) : d3390 p ≤ (0 : Int) + d328 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d3390, d328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45888 p hg
    simpa only [d8089, d3390, d328, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d3390, d328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45443 p hg
    simpa only [d8089, d3390, d328, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45890 (p : Pattern) (guard : d8094 p = 1) : d3391 p ≤ (0 : Int) + d331 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d3391, d331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45889 p hg
    simpa only [d8094, d3391, d331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d3391, d331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45463 p hg
    simpa only [d8094, d3391, d331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45891 (p : Pattern) (guard : d8100 p = 1) : d3392 p ≤ (0 : Int) + d334 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3392, d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45890 p hg
    simpa only [d8100, d3392, d334, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3392, d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45445 p hg
    simpa only [d8100, d3392, d334, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45892 (p : Pattern) (guard : d8105 p = 1) : d3362 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d3362, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45464 p hg
    simpa only [d8105, d3362, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d3362, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d3362, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45893 (p : Pattern) (guard : d8106 p = 1) : d3393 p ≤ (0 : Int) + d337 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3393, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45891 p hg
    simpa only [d8106, d3393, d337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3393, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45892 p hg
    simpa only [d8106, d3393, d337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45894 (p : Pattern) (guard : d5847 p = 1) : d3374 p ≤ (0 : Int) + d364 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3374, d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35751 p hg
    simpa only [d5847, d3374, d364, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3374, d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5847, d3374, d364, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45895 (p : Pattern) (guard : d5854 p = 1) : d3374 p ≤ (0 : Int) + d365 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45894 p hg
    simpa only [d5854, d365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26796 p hg
    simpa only [d5854, d365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45896 (p : Pattern) (guard : d8099 p = 1) : d3374 p ≤ (0 : Int) + d366 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45895 p hg
    simpa only [d8099, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26796 p hg
    simpa only [d8099, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45897 (p : Pattern) (guard : d8105 p = 1) : d3374 p ≤ (0 : Int) + d367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45896 p hg
    simpa only [d8105, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26796 p hg
    simpa only [d8105, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45898 (p : Pattern) (guard : d8111 p = 1) : d3394 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3394, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45897 p hg
    simpa only [d8111, d3394, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3394, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45326 p hg
    simpa only [d8111, d3394, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45899 (p : Pattern) (guard : d8112 p = 1) : d3395 p ≤ (0 : Int) + d415 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3395, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45893 p hg
    simpa only [d8112, d3395, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3395, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45898 p hg
    simpa only [d8112, d3395, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45900 (p : Pattern) (guard : d5847 p = 1) : d3366 p ≤ (0 : Int) + d317 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3366, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35758 p hg
    simpa only [d5847, d3366, d317, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3366, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5847, d3366, d317, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45901 (p : Pattern) (guard : d5854 p = 1) : d3366 p ≤ (0 : Int) + d318 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45900 p hg
    simpa only [d5854, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26786 p hg
    simpa only [d5854, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45902 (p : Pattern) (guard : d8099 p = 1) : d3366 p ≤ (0 : Int) + d323 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45901 p hg
    simpa only [d8099, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26786 p hg
    simpa only [d8099, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45903 (p : Pattern) (guard : d8105 p = 1) : d3366 p ≤ (0 : Int) + d324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45902 p hg
    simpa only [d8105, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26786 p hg
    simpa only [d8105, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45904 (p : Pattern) (guard : d8111 p = 1) : d3368 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3368, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45903 p hg
    simpa only [d8111, d3368, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3368, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45299 p hg
    simpa only [d8111, d3368, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45905 (p : Pattern) (guard : d8117 p = 1) : d3481 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3481, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45904 p hg
    simpa only [d8117, d3481, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3481, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35764 p hg
    simpa only [d8117, d3481, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45906 (p : Pattern) (guard : d8118 p = 1) : d3482 p ≤ (0 : Int) + d416 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3482, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45899 p hg
    simpa only [d8118, d3482, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3482, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45905 p hg
    simpa only [d8118, d3482, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45907 (p : Pattern) (guard : d8117 p = 1) : d3481 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3481, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45868 p hg
    simpa only [d8117, d3481, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3481, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35767 p hg
    simpa only [d8117, d3481, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45908 (p : Pattern) (guard : d8123 p = 1) : d3483 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d3483, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45907 p hg
    simpa only [d8123, d3483, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d3483, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d3483, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45909 (p : Pattern) (guard : d8124 p = 1) : d3484 p ≤ (0 : Int) + d417 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d3484, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45906 p hg
    simpa only [d8124, d3484, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d3484, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45908 p hg
    simpa only [d8124, d3484, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45910 (p : Pattern) (guard : d5847 p = 1) : d3358 p ≤ (0 : Int) + d356 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3358, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35771 p hg
    simpa only [d5847, d3358, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3358, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5847, d3358, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45911 (p : Pattern) (guard : d5854 p = 1) : d3358 p ≤ (0 : Int) + d357 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45910 p hg
    simpa only [d5854, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26774 p hg
    simpa only [d5854, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45912 (p : Pattern) (guard : d8099 p = 1) : d3358 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45911 p hg
    simpa only [d8099, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26774 p hg
    simpa only [d8099, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45913 (p : Pattern) (guard : d8105 p = 1) : d3358 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45912 p hg
    simpa only [d8105, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26774 p hg
    simpa only [d8105, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45914 (p : Pattern) (guard : d8111 p = 1) : d3379 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3379, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45913 p hg
    simpa only [d8111, d3379, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3379, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45311 p hg
    simpa only [d8111, d3379, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45915 (p : Pattern) (guard : d8117 p = 1) : d3402 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3402, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45914 p hg
    simpa only [d8117, d3402, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3402, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45420 p hg
    simpa only [d8117, d3402, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45916 (p : Pattern) (guard : d0 p = 1) : d3485 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare45917 (p : Pattern) (guard : d8123 p = 1) : d3486 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d3486, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45915 p hg
    simpa only [d8123, d3486, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d3486, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45916 p hg
    simpa only [d8123, d3486, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45918 (p : Pattern) (guard : d0 p = 1) : d3487 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare45919 (p : Pattern) (guard : d8129 p = 1) : d3488 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d3488, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45917 p hg
    simpa only [d8129, d3488, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d3488, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45918 p hg
    simpa only [d8129, d3488, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
