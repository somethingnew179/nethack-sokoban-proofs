/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons327
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare45920 (p : Pattern) (guard : d8130 p = 1) : d3489 p ≤ (0 : Int) + d418 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d3489, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45909 p hg
    simpa only [d8130, d3489, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d3489, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45919 p hg
    simpa only [d8130, d3489, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45921 (p : Pattern) (guard : d8131 p = 1) : d3490 p ≤ (0 : Int) + d438 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d3490, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45887 p hg
    simpa only [d8131, d3490, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d3490, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45920 p hg
    simpa only [d8131, d3490, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45922 (p : Pattern) (guard : d8111 p = 1) : d3364 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3364, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45913 p hg
    simpa only [d8111, d3364, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3364, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45428 p hg
    simpa only [d8111, d3364, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45923 (p : Pattern) (guard : d8112 p = 1) : d3364 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45403 p hg
    simpa only [d8112, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45922 p hg
    simpa only [d8112, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45924 (p : Pattern) (guard : d8117 p = 1) : d3369 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3369, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45466 p hg
    simpa only [d8117, d3369, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3369, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45431 p hg
    simpa only [d8117, d3369, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45925 (p : Pattern) (guard : d8118 p = 1) : d3410 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3410, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45923 p hg
    simpa only [d8118, d3410, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3410, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45924 p hg
    simpa only [d8118, d3410, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45926 (p : Pattern) (guard : d8117 p = 1) : d3369 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3369, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45447 p hg
    simpa only [d8117, d3369, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3369, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45431 p hg
    simpa only [d8117, d3369, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45927 (p : Pattern) (guard : d8123 p = 1) : d3372 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d3372, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45926 p hg
    simpa only [d8123, d3372, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d3372, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45434 p hg
    simpa only [d8123, d3372, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45928 (p : Pattern) (guard : d8124 p = 1) : d3411 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d3411, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45925 p hg
    simpa only [d8124, d3411, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d3411, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45927 p hg
    simpa only [d8124, d3411, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45929 (p : Pattern) (guard : d8130 p = 1) : d3416 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d3416, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45928 p hg
    simpa only [d8130, d3416, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d3416, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45441 p hg
    simpa only [d8130, d3416, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45930 (p : Pattern) (guard : d5847 p = 1) : d3358 p ≤ (0 : Int) + d315 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3358, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35792 p hg
    simpa only [d5847, d3358, d315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3358, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5847, d3358, d315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45931 (p : Pattern) (guard : d5854 p = 1) : d3358 p ≤ (0 : Int) + d320 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45930 p hg
    simpa only [d5854, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26774 p hg
    simpa only [d5854, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45932 (p : Pattern) (guard : d8099 p = 1) : d3358 p ≤ (0 : Int) + d321 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45931 p hg
    simpa only [d8099, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26774 p hg
    simpa only [d8099, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45933 (p : Pattern) (guard : d8105 p = 1) : d3358 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45932 p hg
    simpa only [d8105, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26774 p hg
    simpa only [d8105, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45934 (p : Pattern) (guard : d8111 p = 1) : d3364 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3364, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45933 p hg
    simpa only [d8111, d3364, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3364, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45428 p hg
    simpa only [d8111, d3364, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45935 (p : Pattern) (guard : d0 p = 1) : d3394 p ≤ (0 : Int) + d373 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare45936 (p : Pattern) (guard : d8117 p = 1) : d3417 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3417, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45934 p hg
    simpa only [d8117, d3417, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3417, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45935 p hg
    simpa only [d8117, d3417, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45937 (p : Pattern) (guard : d0 p = 1) : d3481 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare45938 (p : Pattern) (guard : d8123 p = 1) : d3491 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d3491, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45936 p hg
    simpa only [d8123, d3491, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d3491, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45937 p hg
    simpa only [d8123, d3491, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45939 (p : Pattern) (guard : d0 p = 1) : d3483 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare45940 (p : Pattern) (guard : d8129 p = 1) : d3492 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d3492, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45938 p hg
    simpa only [d8129, d3492, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d3492, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45939 p hg
    simpa only [d8129, d3492, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45941 (p : Pattern) (guard : d8135 p = 1) : d3493 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d3493, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45940 p hg
    simpa only [d8135, d3493, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d3493, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45454 p hg
    simpa only [d8135, d3493, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45942 (p : Pattern) (guard : d8136 p = 1) : d3494 p ≤ (0 : Int) + d439 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d3494, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45929 p hg
    simpa only [d8136, d3494, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d3494, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45941 p hg
    simpa only [d8136, d3494, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45943 (p : Pattern) (guard : d8137 p = 1) : d3495 p ≤ (0 : Int) + d440 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d3495, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45921 p hg
    simpa only [d8137, d3495, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d3495, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45942 p hg
    simpa only [d8137, d3495, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45944 (p : Pattern) (guard : d8112 p = 1) : d3364 p ≤ (0 : Int) + d355 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45863 p hg
    simpa only [d8112, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45934 p hg
    simpa only [d8112, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45945 (p : Pattern) (guard : d8117 p = 1) : d3369 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3369, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45922 p hg
    simpa only [d8117, d3369, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3369, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45431 p hg
    simpa only [d8117, d3369, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45946 (p : Pattern) (guard : d8118 p = 1) : d3410 p ≤ (0 : Int) + d362 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3410, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45944 p hg
    simpa only [d8118, d3410, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3410, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45945 p hg
    simpa only [d8118, d3410, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45947 (p : Pattern) (guard : d8123 p = 1) : d3372 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d3372, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45924 p hg
    simpa only [d8123, d3372, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d3372, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45434 p hg
    simpa only [d8123, d3372, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45948 (p : Pattern) (guard : d8124 p = 1) : d3411 p ≤ (0 : Int) + d395 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d3411, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45946 p hg
    simpa only [d8124, d3411, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d3411, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45947 p hg
    simpa only [d8124, d3411, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45949 (p : Pattern) (guard : d8117 p = 1) : d3413 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3413, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45327 p hg
    simpa only [d8117, d3413, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3413, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45438 p hg
    simpa only [d8117, d3413, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45950 (p : Pattern) (guard : d8123 p = 1) : d3414 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d3414, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45949 p hg
    simpa only [d8123, d3414, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d3414, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d3414, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45951 (p : Pattern) (guard : d8129 p = 1) : d3415 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d3415, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45950 p hg
    simpa only [d8129, d3415, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d3415, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8129, d3415, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45952 (p : Pattern) (guard : d8130 p = 1) : d3416 p ≤ (0 : Int) + d397 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d3416, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45948 p hg
    simpa only [d8130, d3416, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d3416, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45951 p hg
    simpa only [d8130, d3416, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45953 (p : Pattern) (guard : d5847 p = 1) : d3358 p ≤ (0 : Int) + d317 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3358, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35815 p hg
    simpa only [d5847, d3358, d317, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3358, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5847, d3358, d317, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45954 (p : Pattern) (guard : d5854 p = 1) : d3358 p ≤ (0 : Int) + d318 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45953 p hg
    simpa only [d5854, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26774 p hg
    simpa only [d5854, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45955 (p : Pattern) (guard : d8099 p = 1) : d3358 p ≤ (0 : Int) + d323 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45954 p hg
    simpa only [d8099, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26774 p hg
    simpa only [d8099, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45956 (p : Pattern) (guard : d8105 p = 1) : d3358 p ≤ (0 : Int) + d324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45955 p hg
    simpa only [d8105, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26774 p hg
    simpa only [d8105, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45957 (p : Pattern) (guard : d8111 p = 1) : d3364 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3364, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45956 p hg
    simpa only [d8111, d3364, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3364, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45428 p hg
    simpa only [d8111, d3364, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45958 (p : Pattern) (guard : d0 p = 1) : d3394 p ≤ (0 : Int) + d370 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare45959 (p : Pattern) (guard : d8117 p = 1) : d3417 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3417, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45957 p hg
    simpa only [d8117, d3417, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3417, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45958 p hg
    simpa only [d8117, d3417, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45960 (p : Pattern) (guard : d0 p = 1) : d3481 p ≤ (0 : Int) + d374 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare45961 (p : Pattern) (guard : d8123 p = 1) : d3491 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d3491, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45959 p hg
    simpa only [d8123, d3491, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d3491, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45960 p hg
    simpa only [d8123, d3491, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45962 (p : Pattern) (guard : d8129 p = 1) : d3492 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d3492, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45961 p hg
    simpa only [d8129, d3492, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d3492, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45939 p hg
    simpa only [d8129, d3492, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45963 (p : Pattern) (guard : d8135 p = 1) : d3493 p ≤ (0 : Int) + d399 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d3493, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45962 p hg
    simpa only [d8135, d3493, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d3493, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45454 p hg
    simpa only [d8135, d3493, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45964 (p : Pattern) (guard : d8136 p = 1) : d3494 p ≤ (0 : Int) + d400 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d3494, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45952 p hg
    simpa only [d8136, d3494, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d3494, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45963 p hg
    simpa only [d8136, d3494, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45965 (p : Pattern) (guard : d8123 p = 1) : d3426 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d3426, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45877 p hg
    simpa only [d8123, d3426, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d3426, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d3426, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45966 (p : Pattern) (guard : d8129 p = 1) : d3427 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d3427, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45965 p hg
    simpa only [d8129, d3427, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d3427, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8129, d3427, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45967 (p : Pattern) (guard : d8135 p = 1) : d3428 p ≤ (0 : Int) + d421 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d3428, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45966 p hg
    simpa only [d8135, d3428, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d3428, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8135, d3428, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45968 (p : Pattern) (guard : d8141 p = 1) : d3429 p ≤ (0 : Int) + d441 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8135 p = 1 := by simpa only [d8141, d3429, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45967 p hg
    simpa only [d8141, d3429, d441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8141, d3429, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8141, d3429, d441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45969 (p : Pattern) (guard : d8142 p = 1) : d3496 p ≤ (0 : Int) + d442 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8136 p = 1 := by simpa only [d8142, d3496, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45964 p hg
    simpa only [d8142, d3496, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8141 p = 1 := by simpa only [d8142, d3496, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45968 p hg
    simpa only [d8142, d3496, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45970 (p : Pattern) (guard : d8143 p = 1) : d3497 p ≤ (0 : Int) + d443 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8137 p = 1 := by simpa only [d8143, d3497, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45943 p hg
    simpa only [d8143, d3497, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8142 p = 1 := by simpa only [d8143, d3497, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45969 p hg
    simpa only [d8143, d3497, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45971 (p : Pattern) (guard : d8112 p = 1) : d3364 p ≤ (0 : Int) + d346 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45857 p hg
    simpa only [d8112, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45957 p hg
    simpa only [d8112, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45972 (p : Pattern) (guard : d0 p = 1) : d3368 p ≤ (0 : Int) + d373 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare45973 (p : Pattern) (guard : d8117 p = 1) : d3369 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3369, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45934 p hg
    simpa only [d8117, d3369, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3369, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45972 p hg
    simpa only [d8117, d3369, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45974 (p : Pattern) (guard : d8118 p = 1) : d3410 p ≤ (0 : Int) + d402 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3410, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45971 p hg
    simpa only [d8118, d3410, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3410, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45973 p hg
    simpa only [d8118, d3410, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45975 (p : Pattern) (guard : d8123 p = 1) : d3372 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d3372, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45945 p hg
    simpa only [d8123, d3372, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d3372, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45434 p hg
    simpa only [d8123, d3372, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45976 (p : Pattern) (guard : d8124 p = 1) : d3411 p ≤ (0 : Int) + d404 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d3411, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45974 p hg
    simpa only [d8124, d3411, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d3411, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45975 p hg
    simpa only [d8124, d3411, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45977 (p : Pattern) (guard : d0 p = 1) : d3498 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare45978 (p : Pattern) (guard : d8117 p = 1) : d3499 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3499, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45364 p hg
    simpa only [d8117, d3499, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3499, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45977 p hg
    simpa only [d8117, d3499, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45979 (p : Pattern) (guard : d8123 p = 1) : d3500 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d3500, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45978 p hg
    simpa only [d8123, d3500, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d3500, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45916 p hg
    simpa only [d8123, d3500, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45980 (p : Pattern) (guard : d0 p = 1) : d3503 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare45981 (p : Pattern) (guard : d8129 p = 1) : d3504 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d3504, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45979 p hg
    simpa only [d8129, d3504, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d3504, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45980 p hg
    simpa only [d8129, d3504, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45982 (p : Pattern) (guard : d8130 p = 1) : d3505 p ≤ (0 : Int) + d406 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d3505, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45976 p hg
    simpa only [d8130, d3505, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d3505, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45981 p hg
    simpa only [d8130, d3505, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45983 (p : Pattern) (guard : d5847 p = 1) : d3358 p ≤ (0 : Int) + d364 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3358, d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35833 p hg
    simpa only [d5847, d3358, d364, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3358, d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5847, d3358, d364, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45984 (p : Pattern) (guard : d5854 p = 1) : d3358 p ≤ (0 : Int) + d365 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45983 p hg
    simpa only [d5854, d365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26774 p hg
    simpa only [d5854, d365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45985 (p : Pattern) (guard : d8099 p = 1) : d3358 p ≤ (0 : Int) + d366 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45984 p hg
    simpa only [d8099, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26774 p hg
    simpa only [d8099, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45986 (p : Pattern) (guard : d8105 p = 1) : d3358 p ≤ (0 : Int) + d367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45985 p hg
    simpa only [d8105, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26774 p hg
    simpa only [d8105, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45987 (p : Pattern) (guard : d8111 p = 1) : d3364 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3364, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45986 p hg
    simpa only [d8111, d3364, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3364, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45428 p hg
    simpa only [d8111, d3364, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45988 (p : Pattern) (guard : d0 p = 1) : d3394 p ≤ (0 : Int) + d360 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare45989 (p : Pattern) (guard : d8117 p = 1) : d3417 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3417, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45987 p hg
    simpa only [d8117, d3417, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3417, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45988 p hg
    simpa only [d8117, d3417, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45990 (p : Pattern) (guard : d0 p = 1) : d3481 p ≤ (0 : Int) + d371 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare45991 (p : Pattern) (guard : d8123 p = 1) : d3491 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d3491, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45989 p hg
    simpa only [d8123, d3491, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d3491, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45990 p hg
    simpa only [d8123, d3491, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45992 (p : Pattern) (guard : d0 p = 1) : d3483 p ≤ (0 : Int) + d375 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare45993 (p : Pattern) (guard : d8129 p = 1) : d3492 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d3492, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45991 p hg
    simpa only [d8129, d3492, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d3492, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45992 p hg
    simpa only [d8129, d3492, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45994 (p : Pattern) (guard : d0 p = 1) : d3510 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare45995 (p : Pattern) (guard : d8135 p = 1) : d3511 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d3511, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45993 p hg
    simpa only [d8135, d3511, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d3511, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45994 p hg
    simpa only [d8135, d3511, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45996 (p : Pattern) (guard : d8136 p = 1) : d3512 p ≤ (0 : Int) + d408 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d3512, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45982 p hg
    simpa only [d8136, d3512, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d3512, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45995 p hg
    simpa only [d8136, d3512, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45997 (p : Pattern) (guard : d0 p = 1) : d3364 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare45998 (p : Pattern) (guard : d8117 p = 1) : d3364 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45922 p hg
    simpa only [d8117, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45997 p hg
    simpa only [d8117, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45999 (p : Pattern) (guard : d0 p = 1) : d3513 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare46000 (p : Pattern) (guard : d8123 p = 1) : d3514 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d3514, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45998 p hg
    simpa only [d8123, d3514, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d3514, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45999 p hg
    simpa only [d8123, d3514, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46001 (p : Pattern) (guard : d8129 p = 1) : d3515 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d3515, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46000 p hg
    simpa only [d8129, d3515, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d3515, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45452 p hg
    simpa only [d8129, d3515, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46002 (p : Pattern) (guard : d8135 p = 1) : d3516 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d3516, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46001 p hg
    simpa only [d8135, d3516, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d3516, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45454 p hg
    simpa only [d8135, d3516, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46003 (p : Pattern) (guard : d0 p = 1) : d3521 p ≤ (0 : Int) + d411 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare46004 (p : Pattern) (guard : d8141 p = 1) : d3522 p ≤ (0 : Int) + d412 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8135 p = 1 := by simpa only [d8141, d3522, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46002 p hg
    simpa only [d8141, d3522, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8141, d3522, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46003 p hg
    simpa only [d8141, d3522, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46005 (p : Pattern) (guard : d8142 p = 1) : d3523 p ≤ (0 : Int) + d413 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8136 p = 1 := by simpa only [d8142, d3523, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45996 p hg
    simpa only [d8142, d3523, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8141 p = 1 := by simpa only [d8142, d3523, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46004 p hg
    simpa only [d8142, d3523, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46006 (p : Pattern) (guard : d0 p = 1) : d3364 p ≤ (0 : Int) + d373 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare46007 (p : Pattern) (guard : d8117 p = 1) : d3364 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45934 p hg
    simpa only [d8117, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46006 p hg
    simpa only [d8117, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46008 (p : Pattern) (guard : d0 p = 1) : d3524 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare46009 (p : Pattern) (guard : d8123 p = 1) : d3525 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d3525, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46007 p hg
    simpa only [d8123, d3525, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d3525, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46008 p hg
    simpa only [d8123, d3525, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46010 (p : Pattern) (guard : d0 p = 1) : d3527 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare46011 (p : Pattern) (guard : d8129 p = 1) : d3528 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d3528, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46009 p hg
    simpa only [d8129, d3528, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d3528, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46010 p hg
    simpa only [d8129, d3528, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46012 (p : Pattern) (guard : d0 p = 1) : d3531 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare46013 (p : Pattern) (guard : d8135 p = 1) : d3532 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d3532, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46011 p hg
    simpa only [d8135, d3532, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d3532, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46012 p hg
    simpa only [d8135, d3532, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46014 (p : Pattern) (guard : d0 p = 1) : d3521 p ≤ (0 : Int) + d421 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare46015 (p : Pattern) (guard : d8141 p = 1) : d3533 p ≤ (0 : Int) + d422 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8135 p = 1 := by simpa only [d8141, d3533, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46013 p hg
    simpa only [d8141, d3533, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8141, d3533, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46014 p hg
    simpa only [d8141, d3533, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46016 (p : Pattern) (guard : d8147 p = 1) : d3534 p ≤ (0 : Int) + d444 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8141 p = 1 := by simpa only [d8147, d3534, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46015 p hg
    simpa only [d8147, d3534, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8147, d3534, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8147, d3534, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46017 (p : Pattern) (guard : d8148 p = 1) : d3535 p ≤ (0 : Int) + d445 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8142 p = 1 := by simpa only [d8148, d3535, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46005 p hg
    simpa only [d8148, d3535, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8147 p = 1 := by simpa only [d8148, d3535, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46016 p hg
    simpa only [d8148, d3535, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46018 (p : Pattern) (guard : d8149 p = 1) : d3536 p ≤ (0 : Int) + d446 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8143 p = 1 := by simpa only [d8149, d3536, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45970 p hg
    simpa only [d8149, d3536, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8148 p = 1 := by simpa only [d8149, d3536, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46017 p hg
    simpa only [d8149, d3536, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46019 (p : Pattern) (guard : d8150 p = 1) : d3537 p ≤ (0 : Int) + d447 p := by
  cases selected : p 71 with
  | false =>
    have hg : d8144 p = 1 := by simpa only [d8150, d3537, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45846 p hg
    simpa only [d8150, d3537, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8149 p = 1 := by simpa only [d8150, d3537, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46018 p hg
    simpa only [d8150, d3537, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46020 (p : Pattern) (guard : d8151 p = 1) : d3538 p ≤ (0 : Int) + d447 p := by
  cases selected : p 49 with
  | false =>
    have hg : d8145 p = 1 := by simpa only [d8151, d3538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45690 p hg
    simpa only [d8151, d3538, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8150 p = 1 := by simpa only [d8151, d3538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46019 p hg
    simpa only [d8151, d3538, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46021 (p : Pattern) (guard : d8152 p = 1) : d3539 p ≤ (0 : Int) + d447 p := by
  cases selected : p 48 with
  | false =>
    have hg : d8146 p = 1 := by simpa only [d8152, d3539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45476 p hg
    simpa only [d8152, d3539, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8151 p = 1 := by simpa only [d8152, d3539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46020 p hg
    simpa only [d8152, d3539, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46022 (p : Pattern) (guard : d8109 p = 1) : d376 p ≤ (0 : Int) + d376 p := by
  omega
theorem compare46023 (p : Pattern) (guard : d8110 p = 1) : d710 p ≤ (0 : Int) + d377 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8104 p = 1 := by simpa only [d8110, d710, d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34402 p hg
    simpa only [d8110, d710, d377, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8109 p = 1 := by simpa only [d8110, d710, d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46022 p hg
    simpa only [d8110, d710, d377, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46024 (p : Pattern) (guard : d8114 p = 1) : d391 p ≤ (0 : Int) + d391 p := by
  omega
theorem compare46025 (p : Pattern) (guard : d8115 p = 1) : d711 p ≤ (0 : Int) + d392 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8109 p = 1 := by simpa only [d8115, d711, d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34517 p hg
    simpa only [d8115, d711, d392, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8114 p = 1 := by simpa only [d8115, d711, d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46024 p hg
    simpa only [d8115, d711, d392, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46026 (p : Pattern) (guard : d8116 p = 1) : d712 p ≤ (0 : Int) + d393 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8110 p = 1 := by simpa only [d8116, d712, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46023 p hg
    simpa only [d8116, d712, d393, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8115 p = 1 := by simpa only [d8116, d712, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46025 p hg
    simpa only [d8116, d712, d393, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46027 (p : Pattern) (guard : d8114 p = 1) : d396 p ≤ (0 : Int) + d396 p := by
  omega
theorem compare46028 (p : Pattern) (guard : d8115 p = 1) : d713 p ≤ (0 : Int) + d397 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8109 p = 1 := by simpa only [d8115, d713, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34562 p hg
    simpa only [d8115, d713, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8114 p = 1 := by simpa only [d8115, d713, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46027 p hg
    simpa only [d8115, d713, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46029 (p : Pattern) (guard : d8119 p = 1) : d12 p ≤ (0 : Int) + d12 p := by
  omega
theorem compare46030 (p : Pattern) (guard : d8120 p = 1) : d714 p ≤ (0 : Int) + d399 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d714, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34609 p hg
    simpa only [d8120, d714, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d714, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46029 p hg
    simpa only [d8120, d714, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46031 (p : Pattern) (guard : d8121 p = 1) : d715 p ≤ (0 : Int) + d400 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8115 p = 1 := by simpa only [d8121, d715, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46028 p hg
    simpa only [d8121, d715, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8120 p = 1 := by simpa only [d8121, d715, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46030 p hg
    simpa only [d8121, d715, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46032 (p : Pattern) (guard : d8122 p = 1) : d716 p ≤ (0 : Int) + d401 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8116 p = 1 := by simpa only [d8122, d716, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46026 p hg
    simpa only [d8122, d716, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8121 p = 1 := by simpa only [d8122, d716, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46031 p hg
    simpa only [d8122, d716, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46033 (p : Pattern) (guard : d8114 p = 1) : d405 p ≤ (0 : Int) + d405 p := by
  omega
theorem compare46034 (p : Pattern) (guard : d8115 p = 1) : d717 p ≤ (0 : Int) + d406 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8109 p = 1 := by simpa only [d8115, d717, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38106 p hg
    simpa only [d8115, d717, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8114 p = 1 := by simpa only [d8115, d717, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46033 p hg
    simpa only [d8115, d717, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46035 (p : Pattern) (guard : d8120 p = 1) : d714 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d714, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41383 p hg
    simpa only [d8120, d714, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d714, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46029 p hg
    simpa only [d8120, d714, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46036 (p : Pattern) (guard : d8121 p = 1) : d718 p ≤ (0 : Int) + d408 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8115 p = 1 := by simpa only [d8121, d718, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46034 p hg
    simpa only [d8121, d718, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8120 p = 1 := by simpa only [d8121, d718, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46035 p hg
    simpa only [d8121, d718, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46037 (p : Pattern) (guard : d8120 p = 1) : d719 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d719, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38120 p hg
    simpa only [d8120, d719, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d719, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46029 p hg
    simpa only [d8120, d719, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46038 (p : Pattern) (guard : d8126 p = 1) : d720 p ≤ (0 : Int) + d412 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d720, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46037 p hg
    simpa only [d8126, d720, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d720, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41388 p hg
    simpa only [d8126, d720, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46039 (p : Pattern) (guard : d8127 p = 1) : d721 p ≤ (0 : Int) + d413 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8121 p = 1 := by simpa only [d8127, d721, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46036 p hg
    simpa only [d8127, d721, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8126 p = 1 := by simpa only [d8127, d721, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46038 p hg
    simpa only [d8127, d721, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46040 (p : Pattern) (guard : d8128 p = 1) : d722 p ≤ (0 : Int) + d414 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8122 p = 1 := by simpa only [d8128, d722, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46032 p hg
    simpa only [d8128, d722, d414, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8127 p = 1 := by simpa only [d8128, d722, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46039 p hg
    simpa only [d8128, d722, d414, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46041 (p : Pattern) (guard : d8114 p = 1) : d409 p ≤ (0 : Int) + d409 p := by
  omega
theorem compare46042 (p : Pattern) (guard : d8115 p = 1) : d723 p ≤ (0 : Int) + d418 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8109 p = 1 := by simpa only [d8115, d723, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34634 p hg
    simpa only [d8115, d723, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8114 p = 1 := by simpa only [d8115, d723, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46041 p hg
    simpa only [d8115, d723, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46043 (p : Pattern) (guard : d8119 p = 1) : d396 p ≤ (0 : Int) + d396 p := by
  omega
theorem compare46044 (p : Pattern) (guard : d8120 p = 1) : d724 p ≤ (0 : Int) + d397 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d724, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34673 p hg
    simpa only [d8120, d724, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d724, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46043 p hg
    simpa only [d8120, d724, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46045 (p : Pattern) (guard : d8121 p = 1) : d725 p ≤ (0 : Int) + d419 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8115 p = 1 := by simpa only [d8121, d725, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46042 p hg
    simpa only [d8121, d725, d419, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8120 p = 1 := by simpa only [d8121, d725, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46044 p hg
    simpa only [d8121, d725, d419, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46046 (p : Pattern) (guard : d8120 p = 1) : d726 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d726, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34706 p hg
    simpa only [d8120, d726, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d726, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46029 p hg
    simpa only [d8120, d726, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46047 (p : Pattern) (guard : d8125 p = 1) : d714 p ≤ (0 : Int) + d421 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d714, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34732 p hg
    simpa only [d8125, d714, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d714, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36298 p hg
    simpa only [d8125, d714, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46048 (p : Pattern) (guard : d8126 p = 1) : d727 p ≤ (0 : Int) + d422 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d727, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46046 p hg
    simpa only [d8126, d727, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d727, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46047 p hg
    simpa only [d8126, d727, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46049 (p : Pattern) (guard : d8127 p = 1) : d728 p ≤ (0 : Int) + d423 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8121 p = 1 := by simpa only [d8127, d728, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46045 p hg
    simpa only [d8127, d728, d423, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8126 p = 1 := by simpa only [d8127, d728, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46048 p hg
    simpa only [d8127, d728, d423, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46050 (p : Pattern) (guard : d8120 p = 1) : d726 p ≤ (0 : Int) + d399 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d726, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38134 p hg
    simpa only [d8120, d726, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d726, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46029 p hg
    simpa only [d8120, d726, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46051 (p : Pattern) (guard : d8125 p = 1) : d714 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d714, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41394 p hg
    simpa only [d8125, d714, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d714, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36298 p hg
    simpa only [d8125, d714, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46052 (p : Pattern) (guard : d8126 p = 1) : d727 p ≤ (0 : Int) + d424 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d727, d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46050 p hg
    simpa only [d8126, d727, d424, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d727, d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46051 p hg
    simpa only [d8126, d727, d424, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46053 (p : Pattern) (guard : d8132 p = 1) : d729 p ≤ (0 : Int) + d425 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d729, d425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46052 p hg
    simpa only [d8132, d729, d425, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d729, d425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36499 p hg
    simpa only [d8132, d729, d425, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46054 (p : Pattern) (guard : d8133 p = 1) : d730 p ≤ (0 : Int) + d426 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8127 p = 1 := by simpa only [d8133, d730, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46049 p hg
    simpa only [d8133, d730, d426, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8132 p = 1 := by simpa only [d8133, d730, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46053 p hg
    simpa only [d8133, d730, d426, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46055 (p : Pattern) (guard : d8134 p = 1) : d731 p ≤ (0 : Int) + d427 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8128 p = 1 := by simpa only [d8134, d731, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46040 p hg
    simpa only [d8134, d731, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8133 p = 1 := by simpa only [d8134, d731, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46054 p hg
    simpa only [d8134, d731, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46056 (p : Pattern) (guard : d8114 p = 1) : d398 p ≤ (0 : Int) + d398 p := by
  omega
theorem compare46057 (p : Pattern) (guard : d8115 p = 1) : d732 p ≤ (0 : Int) + d437 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8109 p = 1 := by simpa only [d8115, d732, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34770 p hg
    simpa only [d8115, d732, d437, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8114 p = 1 := by simpa only [d8115, d732, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46056 p hg
    simpa only [d8115, d732, d437, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46058 (p : Pattern) (guard : d8119 p = 1) : d409 p ≤ (0 : Int) + d409 p := by
  omega
theorem compare46059 (p : Pattern) (guard : d8120 p = 1) : d733 p ≤ (0 : Int) + d418 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d733, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34809 p hg
    simpa only [d8120, d733, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d733, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46058 p hg
    simpa only [d8120, d733, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
