/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons270
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare37940 (p : Pattern) (guard : d8100 p = 1) : d3745 p ≤ (0 : Int) + d334 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3745, d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37937 p hg
    simpa only [d8100, d3745, d334, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3745, d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37939 p hg
    simpa only [d8100, d3745, d334, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37941 (p : Pattern) (guard : d5854 p = 1) : d3741 p ≤ (0 : Int) + d330 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d3741, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37387 p hg
    simpa only [d5854, d3741, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d3741, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29476 p hg
    simpa only [d5854, d3741, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37942 (p : Pattern) (guard : d8099 p = 1) : d3742 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d3742, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37941 p hg
    simpa only [d8099, d3742, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d3742, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29476 p hg
    simpa only [d8099, d3742, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37943 (p : Pattern) (guard : d8105 p = 1) : d3743 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d3743, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37942 p hg
    simpa only [d8105, d3743, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d3743, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d3743, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37944 (p : Pattern) (guard : d8106 p = 1) : d3746 p ≤ (0 : Int) + d337 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3746, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37940 p hg
    simpa only [d8106, d3746, d337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3746, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37943 p hg
    simpa only [d8106, d3746, d337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37945 (p : Pattern) (guard : d5843 p = 1) : d115 p ≤ (0 : Int) + d34 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d115, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35207 p hg
    simpa only [d5843, d115, d34, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d115, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5843, d115, d34, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37946 (p : Pattern) (guard : d5847 p = 1) : d115 p ≤ (0 : Int) + d364 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37945 p hg
    simpa only [d5847, d364, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17806 p hg
    simpa only [d5847, d364, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37947 (p : Pattern) (guard : d5854 p = 1) : d115 p ≤ (0 : Int) + d365 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37946 p hg
    simpa only [d5854, d365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17806 p hg
    simpa only [d5854, d365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37948 (p : Pattern) (guard : d8099 p = 1) : d115 p ≤ (0 : Int) + d366 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37947 p hg
    simpa only [d8099, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17806 p hg
    simpa only [d8099, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37949 (p : Pattern) (guard : d8105 p = 1) : d3796 p ≤ (0 : Int) + d367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d3796, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37948 p hg
    simpa only [d8105, d3796, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d3796, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37320 p hg
    simpa only [d8105, d3796, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37950 (p : Pattern) (guard : d8111 p = 1) : d3801 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3801, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37949 p hg
    simpa only [d8111, d3801, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3801, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37322 p hg
    simpa only [d8111, d3801, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37951 (p : Pattern) (guard : d8112 p = 1) : d3802 p ≤ (0 : Int) + d415 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3802, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37944 p hg
    simpa only [d8112, d3802, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3802, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37950 p hg
    simpa only [d8112, d3802, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37952 (p : Pattern) (guard : d5843 p = 1) : d106 p ≤ (0 : Int) + d119 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d106, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1415 p hg
    simpa only [d5843, d106, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d106, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5843, d106, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37953 (p : Pattern) (guard : d5847 p = 1) : d106 p ≤ (0 : Int) + d317 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37952 p hg
    simpa only [d5847, d317, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17797 p hg
    simpa only [d5847, d317, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37954 (p : Pattern) (guard : d5854 p = 1) : d106 p ≤ (0 : Int) + d318 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37953 p hg
    simpa only [d5854, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17797 p hg
    simpa only [d5854, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37955 (p : Pattern) (guard : d8099 p = 1) : d106 p ≤ (0 : Int) + d323 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37954 p hg
    simpa only [d8099, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17797 p hg
    simpa only [d8099, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37956 (p : Pattern) (guard : d8105 p = 1) : d3751 p ≤ (0 : Int) + d324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d3751, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37955 p hg
    simpa only [d8105, d3751, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d3751, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37284 p hg
    simpa only [d8105, d3751, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37957 (p : Pattern) (guard : d8111 p = 1) : d3756 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3756, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37956 p hg
    simpa only [d8111, d3756, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3756, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37286 p hg
    simpa only [d8111, d3756, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37958 (p : Pattern) (guard : d8117 p = 1) : d3944 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3944, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37957 p hg
    simpa only [d8117, d3944, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3944, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35764 p hg
    simpa only [d8117, d3944, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37959 (p : Pattern) (guard : d8118 p = 1) : d3945 p ≤ (0 : Int) + d416 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3945, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37951 p hg
    simpa only [d8118, d3945, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3945, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37958 p hg
    simpa only [d8118, d3945, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37960 (p : Pattern) (guard : d8117 p = 1) : d3944 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3944, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37914 p hg
    simpa only [d8117, d3944, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3944, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35767 p hg
    simpa only [d8117, d3944, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37961 (p : Pattern) (guard : d8123 p = 1) : d3946 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d3946, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37960 p hg
    simpa only [d8123, d3946, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d3946, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d3946, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37962 (p : Pattern) (guard : d8124 p = 1) : d3947 p ≤ (0 : Int) + d417 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d3947, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37959 p hg
    simpa only [d8124, d3947, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d3947, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37961 p hg
    simpa only [d8124, d3947, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37963 (p : Pattern) (guard : d5843 p = 1) : d102 p ≤ (0 : Int) + d23 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d102, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35084 p hg
    simpa only [d5843, d102, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d102, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5843, d102, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37964 (p : Pattern) (guard : d5847 p = 1) : d102 p ≤ (0 : Int) + d356 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37963 p hg
    simpa only [d5847, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17788 p hg
    simpa only [d5847, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37965 (p : Pattern) (guard : d5854 p = 1) : d102 p ≤ (0 : Int) + d357 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37964 p hg
    simpa only [d5854, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17788 p hg
    simpa only [d5854, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37966 (p : Pattern) (guard : d8099 p = 1) : d102 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37965 p hg
    simpa only [d8099, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17788 p hg
    simpa only [d8099, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37967 (p : Pattern) (guard : d8105 p = 1) : d3766 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d3766, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37966 p hg
    simpa only [d8105, d3766, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d3766, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37299 p hg
    simpa only [d8105, d3766, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37968 (p : Pattern) (guard : d8111 p = 1) : d3779 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3779, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37967 p hg
    simpa only [d8111, d3779, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3779, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37195 p hg
    simpa only [d8111, d3779, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37969 (p : Pattern) (guard : d8117 p = 1) : d3810 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3810, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37968 p hg
    simpa only [d8117, d3810, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3810, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37336 p hg
    simpa only [d8117, d3810, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37970 (p : Pattern) (guard : d0 p = 1) : d3948 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37971 (p : Pattern) (guard : d8123 p = 1) : d3949 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d3949, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37969 p hg
    simpa only [d8123, d3949, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d3949, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37970 p hg
    simpa only [d8123, d3949, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37972 (p : Pattern) (guard : d0 p = 1) : d3950 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37973 (p : Pattern) (guard : d8129 p = 1) : d3951 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d3951, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37971 p hg
    simpa only [d8129, d3951, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d3951, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37972 p hg
    simpa only [d8129, d3951, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37974 (p : Pattern) (guard : d8130 p = 1) : d3952 p ≤ (0 : Int) + d418 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d3952, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37962 p hg
    simpa only [d8130, d3952, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d3952, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37973 p hg
    simpa only [d8130, d3952, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37975 (p : Pattern) (guard : d8131 p = 1) : d3953 p ≤ (0 : Int) + d438 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d3953, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37934 p hg
    simpa only [d8131, d3953, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d3953, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37974 p hg
    simpa only [d8131, d3953, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37976 (p : Pattern) (guard : d8100 p = 1) : d3820 p ≤ (0 : Int) + d367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3820, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37313 p hg
    simpa only [d8100, d3820, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3820, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37344 p hg
    simpa only [d8100, d3820, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37977 (p : Pattern) (guard : d8106 p = 1) : d3822 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3822, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37976 p hg
    simpa only [d8106, d3822, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3822, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37346 p hg
    simpa only [d8106, d3822, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37978 (p : Pattern) (guard : d8111 p = 1) : d3827 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3827, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37967 p hg
    simpa only [d8111, d3827, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3827, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37348 p hg
    simpa only [d8111, d3827, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37979 (p : Pattern) (guard : d8112 p = 1) : d3828 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3828, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37977 p hg
    simpa only [d8112, d3828, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3828, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37978 p hg
    simpa only [d8112, d3828, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37980 (p : Pattern) (guard : d8111 p = 1) : d3830 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3830, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37390 p hg
    simpa only [d8111, d3830, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3830, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37351 p hg
    simpa only [d8111, d3830, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37981 (p : Pattern) (guard : d8117 p = 1) : d3833 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3833, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37980 p hg
    simpa only [d8117, d3833, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3833, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37353 p hg
    simpa only [d8117, d3833, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37982 (p : Pattern) (guard : d8118 p = 1) : d3834 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3834, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37979 p hg
    simpa only [d8118, d3834, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3834, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37981 p hg
    simpa only [d8118, d3834, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37983 (p : Pattern) (guard : d8111 p = 1) : d3830 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3830, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37368 p hg
    simpa only [d8111, d3830, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3830, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37351 p hg
    simpa only [d8111, d3830, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37984 (p : Pattern) (guard : d8117 p = 1) : d3833 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3833, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37983 p hg
    simpa only [d8117, d3833, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3833, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37353 p hg
    simpa only [d8117, d3833, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37985 (p : Pattern) (guard : d8123 p = 1) : d3835 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d3835, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37984 p hg
    simpa only [d8123, d3835, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d3835, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37356 p hg
    simpa only [d8123, d3835, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37986 (p : Pattern) (guard : d8124 p = 1) : d3836 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d3836, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37982 p hg
    simpa only [d8124, d3836, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d3836, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37985 p hg
    simpa only [d8124, d3836, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37987 (p : Pattern) (guard : d8130 p = 1) : d3843 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d3843, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37986 p hg
    simpa only [d8130, d3843, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d3843, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37363 p hg
    simpa only [d8130, d3843, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37988 (p : Pattern) (guard : d5843 p = 1) : d102 p ≤ (0 : Int) + d190 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d102, d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35090 p hg
    simpa only [d5843, d102, d190, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d102, d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5843, d102, d190, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37989 (p : Pattern) (guard : d5847 p = 1) : d102 p ≤ (0 : Int) + d315 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37988 p hg
    simpa only [d5847, d315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17788 p hg
    simpa only [d5847, d315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37990 (p : Pattern) (guard : d5854 p = 1) : d102 p ≤ (0 : Int) + d320 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37989 p hg
    simpa only [d5854, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17788 p hg
    simpa only [d5854, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37991 (p : Pattern) (guard : d8099 p = 1) : d102 p ≤ (0 : Int) + d321 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37990 p hg
    simpa only [d8099, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17788 p hg
    simpa only [d8099, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37992 (p : Pattern) (guard : d8105 p = 1) : d3766 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d3766, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37991 p hg
    simpa only [d8105, d3766, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d3766, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37299 p hg
    simpa only [d8105, d3766, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37993 (p : Pattern) (guard : d8111 p = 1) : d3827 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3827, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37992 p hg
    simpa only [d8111, d3827, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3827, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37348 p hg
    simpa only [d8111, d3827, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37994 (p : Pattern) (guard : d0 p = 1) : d3837 p ≤ (0 : Int) + d373 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37995 (p : Pattern) (guard : d8117 p = 1) : d3844 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3844, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37993 p hg
    simpa only [d8117, d3844, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3844, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37994 p hg
    simpa only [d8117, d3844, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37996 (p : Pattern) (guard : d0 p = 1) : d3954 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37997 (p : Pattern) (guard : d8123 p = 1) : d3955 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d3955, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37995 p hg
    simpa only [d8123, d3955, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d3955, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37996 p hg
    simpa only [d8123, d3955, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37998 (p : Pattern) (guard : d0 p = 1) : d3956 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37999 (p : Pattern) (guard : d8129 p = 1) : d3957 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d3957, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37997 p hg
    simpa only [d8129, d3957, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d3957, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37998 p hg
    simpa only [d8129, d3957, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38000 (p : Pattern) (guard : d8135 p = 1) : d3958 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d3958, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37999 p hg
    simpa only [d8135, d3958, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d3958, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37376 p hg
    simpa only [d8135, d3958, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38001 (p : Pattern) (guard : d8136 p = 1) : d3959 p ≤ (0 : Int) + d439 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d3959, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37987 p hg
    simpa only [d8136, d3959, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d3959, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38000 p hg
    simpa only [d8136, d3959, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38002 (p : Pattern) (guard : d8137 p = 1) : d3960 p ≤ (0 : Int) + d440 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d3960, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37975 p hg
    simpa only [d8137, d3960, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d3960, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38001 p hg
    simpa only [d8137, d3960, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38003 (p : Pattern) (guard : d8100 p = 1) : d3820 p ≤ (0 : Int) + d351 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3820, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37906 p hg
    simpa only [d8100, d3820, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3820, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37344 p hg
    simpa only [d8100, d3820, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38004 (p : Pattern) (guard : d8106 p = 1) : d3822 p ≤ (0 : Int) + d352 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3822, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38003 p hg
    simpa only [d8106, d3822, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3822, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37346 p hg
    simpa only [d8106, d3822, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38005 (p : Pattern) (guard : d8112 p = 1) : d3828 p ≤ (0 : Int) + d355 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3828, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38004 p hg
    simpa only [d8112, d3828, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3828, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37993 p hg
    simpa only [d8112, d3828, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38006 (p : Pattern) (guard : d8111 p = 1) : d3830 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3830, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37967 p hg
    simpa only [d8111, d3830, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3830, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37351 p hg
    simpa only [d8111, d3830, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38007 (p : Pattern) (guard : d8117 p = 1) : d3833 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3833, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38006 p hg
    simpa only [d8117, d3833, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3833, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37353 p hg
    simpa only [d8117, d3833, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38008 (p : Pattern) (guard : d8118 p = 1) : d3834 p ≤ (0 : Int) + d362 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3834, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38005 p hg
    simpa only [d8118, d3834, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3834, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38007 p hg
    simpa only [d8118, d3834, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38009 (p : Pattern) (guard : d8123 p = 1) : d3835 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d3835, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37981 p hg
    simpa only [d8123, d3835, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d3835, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37356 p hg
    simpa only [d8123, d3835, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38010 (p : Pattern) (guard : d8124 p = 1) : d3836 p ≤ (0 : Int) + d395 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d3836, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38008 p hg
    simpa only [d8124, d3836, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d3836, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38009 p hg
    simpa only [d8124, d3836, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38011 (p : Pattern) (guard : d8117 p = 1) : d3840 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3840, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37212 p hg
    simpa only [d8117, d3840, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3840, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37360 p hg
    simpa only [d8117, d3840, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38012 (p : Pattern) (guard : d8123 p = 1) : d3841 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d3841, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38011 p hg
    simpa only [d8123, d3841, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d3841, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d3841, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38013 (p : Pattern) (guard : d8129 p = 1) : d3842 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d3842, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38012 p hg
    simpa only [d8129, d3842, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d3842, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8129, d3842, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38014 (p : Pattern) (guard : d8130 p = 1) : d3843 p ≤ (0 : Int) + d397 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d3843, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38010 p hg
    simpa only [d8130, d3843, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d3843, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38013 p hg
    simpa only [d8130, d3843, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38015 (p : Pattern) (guard : d5843 p = 1) : d102 p ≤ (0 : Int) + d119 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d102, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1403 p hg
    simpa only [d5843, d102, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d102, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5843, d102, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38016 (p : Pattern) (guard : d5847 p = 1) : d102 p ≤ (0 : Int) + d317 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38015 p hg
    simpa only [d5847, d317, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17788 p hg
    simpa only [d5847, d317, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38017 (p : Pattern) (guard : d5854 p = 1) : d102 p ≤ (0 : Int) + d318 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38016 p hg
    simpa only [d5854, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17788 p hg
    simpa only [d5854, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38018 (p : Pattern) (guard : d8099 p = 1) : d102 p ≤ (0 : Int) + d323 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38017 p hg
    simpa only [d8099, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17788 p hg
    simpa only [d8099, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38019 (p : Pattern) (guard : d8105 p = 1) : d3766 p ≤ (0 : Int) + d324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d3766, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38018 p hg
    simpa only [d8105, d3766, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d3766, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37299 p hg
    simpa only [d8105, d3766, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38020 (p : Pattern) (guard : d8111 p = 1) : d3827 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3827, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38019 p hg
    simpa only [d8111, d3827, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3827, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37348 p hg
    simpa only [d8111, d3827, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38021 (p : Pattern) (guard : d0 p = 1) : d3837 p ≤ (0 : Int) + d370 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare38022 (p : Pattern) (guard : d8117 p = 1) : d3844 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3844, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38020 p hg
    simpa only [d8117, d3844, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3844, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38021 p hg
    simpa only [d8117, d3844, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38023 (p : Pattern) (guard : d0 p = 1) : d3954 p ≤ (0 : Int) + d374 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare38024 (p : Pattern) (guard : d8123 p = 1) : d3955 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d3955, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38022 p hg
    simpa only [d8123, d3955, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d3955, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38023 p hg
    simpa only [d8123, d3955, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38025 (p : Pattern) (guard : d8129 p = 1) : d3957 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d3957, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38024 p hg
    simpa only [d8129, d3957, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d3957, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37998 p hg
    simpa only [d8129, d3957, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38026 (p : Pattern) (guard : d8135 p = 1) : d3958 p ≤ (0 : Int) + d399 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d3958, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38025 p hg
    simpa only [d8135, d3958, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d3958, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37376 p hg
    simpa only [d8135, d3958, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38027 (p : Pattern) (guard : d8136 p = 1) : d3959 p ≤ (0 : Int) + d400 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d3959, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38014 p hg
    simpa only [d8136, d3959, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d3959, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38026 p hg
    simpa only [d8136, d3959, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38028 (p : Pattern) (guard : d8123 p = 1) : d3856 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d3856, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37924 p hg
    simpa only [d8123, d3856, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d3856, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d3856, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38029 (p : Pattern) (guard : d8129 p = 1) : d3857 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d3857, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38028 p hg
    simpa only [d8129, d3857, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d3857, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8129, d3857, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38030 (p : Pattern) (guard : d8135 p = 1) : d3858 p ≤ (0 : Int) + d421 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d3858, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38029 p hg
    simpa only [d8135, d3858, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d3858, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8135, d3858, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38031 (p : Pattern) (guard : d8141 p = 1) : d3859 p ≤ (0 : Int) + d441 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8135 p = 1 := by simpa only [d8141, d3859, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38030 p hg
    simpa only [d8141, d3859, d441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8141, d3859, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8141, d3859, d441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38032 (p : Pattern) (guard : d8142 p = 1) : d3961 p ≤ (0 : Int) + d442 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8136 p = 1 := by simpa only [d8142, d3961, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38027 p hg
    simpa only [d8142, d3961, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8141 p = 1 := by simpa only [d8142, d3961, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38031 p hg
    simpa only [d8142, d3961, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38033 (p : Pattern) (guard : d8143 p = 1) : d3962 p ≤ (0 : Int) + d443 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8137 p = 1 := by simpa only [d8143, d3962, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38002 p hg
    simpa only [d8143, d3962, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8142 p = 1 := by simpa only [d8143, d3962, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38032 p hg
    simpa only [d8143, d3962, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38034 (p : Pattern) (guard : d8100 p = 1) : d3820 p ≤ (0 : Int) + d342 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3820, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37897 p hg
    simpa only [d8100, d3820, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3820, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37344 p hg
    simpa only [d8100, d3820, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38035 (p : Pattern) (guard : d8105 p = 1) : d3821 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d3821, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37939 p hg
    simpa only [d8105, d3821, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d3821, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d3821, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38036 (p : Pattern) (guard : d8106 p = 1) : d3822 p ≤ (0 : Int) + d344 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3822, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38034 p hg
    simpa only [d8106, d3822, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3822, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38035 p hg
    simpa only [d8106, d3822, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38037 (p : Pattern) (guard : d0 p = 1) : d3819 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare38038 (p : Pattern) (guard : d8105 p = 1) : d3820 p ≤ (0 : Int) + d324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d3820, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38018 p hg
    simpa only [d8105, d3820, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d3820, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38037 p hg
    simpa only [d8105, d3820, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38039 (p : Pattern) (guard : d0 p = 1) : d3821 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare38040 (p : Pattern) (guard : d8111 p = 1) : d3822 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3822, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38038 p hg
    simpa only [d8111, d3822, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3822, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38039 p hg
    simpa only [d8111, d3822, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38041 (p : Pattern) (guard : d8112 p = 1) : d3822 p ≤ (0 : Int) + d346 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38036 p hg
    simpa only [d8112, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38040 p hg
    simpa only [d8112, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38042 (p : Pattern) (guard : d0 p = 1) : d3825 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare38043 (p : Pattern) (guard : d8105 p = 1) : d3963 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d3963, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37991 p hg
    simpa only [d8105, d3963, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d3963, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38042 p hg
    simpa only [d8105, d3963, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38044 (p : Pattern) (guard : d0 p = 1) : d3964 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare38045 (p : Pattern) (guard : d8111 p = 1) : d3965 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3965, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38043 p hg
    simpa only [d8111, d3965, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3965, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38044 p hg
    simpa only [d8111, d3965, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38046 (p : Pattern) (guard : d0 p = 1) : d3832 p ≤ (0 : Int) + d373 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare38047 (p : Pattern) (guard : d8117 p = 1) : d3966 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3966, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38045 p hg
    simpa only [d8117, d3966, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3966, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38046 p hg
    simpa only [d8117, d3966, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38048 (p : Pattern) (guard : d8118 p = 1) : d3967 p ≤ (0 : Int) + d402 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3967, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38041 p hg
    simpa only [d8118, d3967, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3967, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38047 p hg
    simpa only [d8118, d3967, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38049 (p : Pattern) (guard : d8117 p = 1) : d3968 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3968, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37978 p hg
    simpa only [d8117, d3968, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3968, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37353 p hg
    simpa only [d8117, d3968, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38050 (p : Pattern) (guard : d8123 p = 1) : d3969 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d3969, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38049 p hg
    simpa only [d8123, d3969, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d3969, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37356 p hg
    simpa only [d8123, d3969, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38051 (p : Pattern) (guard : d8124 p = 1) : d3970 p ≤ (0 : Int) + d404 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d3970, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38048 p hg
    simpa only [d8124, d3970, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d3970, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38050 p hg
    simpa only [d8124, d3970, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38052 (p : Pattern) (guard : d0 p = 1) : d3971 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare38053 (p : Pattern) (guard : d8117 p = 1) : d3972 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3972, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37254 p hg
    simpa only [d8117, d3972, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3972, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38052 p hg
    simpa only [d8117, d3972, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38054 (p : Pattern) (guard : d8123 p = 1) : d3973 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d3973, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38053 p hg
    simpa only [d8123, d3973, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d3973, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37970 p hg
    simpa only [d8123, d3973, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38055 (p : Pattern) (guard : d0 p = 1) : d3976 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare38056 (p : Pattern) (guard : d8129 p = 1) : d3977 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d3977, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38054 p hg
    simpa only [d8129, d3977, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d3977, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38055 p hg
    simpa only [d8129, d3977, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38057 (p : Pattern) (guard : d8130 p = 1) : d3978 p ≤ (0 : Int) + d406 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d3978, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38051 p hg
    simpa only [d8130, d3978, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d3978, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38056 p hg
    simpa only [d8130, d3978, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38058 (p : Pattern) (guard : d5843 p = 1) : d102 p ≤ (0 : Int) + d34 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d102, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35143 p hg
    simpa only [d5843, d102, d34, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d102, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5843, d102, d34, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38059 (p : Pattern) (guard : d5847 p = 1) : d102 p ≤ (0 : Int) + d364 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38058 p hg
    simpa only [d5847, d364, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17788 p hg
    simpa only [d5847, d364, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38060 (p : Pattern) (guard : d5854 p = 1) : d102 p ≤ (0 : Int) + d365 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38059 p hg
    simpa only [d5854, d365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17788 p hg
    simpa only [d5854, d365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38061 (p : Pattern) (guard : d8099 p = 1) : d102 p ≤ (0 : Int) + d366 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38060 p hg
    simpa only [d8099, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17788 p hg
    simpa only [d8099, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38062 (p : Pattern) (guard : d8105 p = 1) : d3963 p ≤ (0 : Int) + d367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d3963, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38061 p hg
    simpa only [d8105, d3963, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d3963, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38042 p hg
    simpa only [d8105, d3963, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38063 (p : Pattern) (guard : d8111 p = 1) : d3965 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3965, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38062 p hg
    simpa only [d8111, d3965, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3965, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38044 p hg
    simpa only [d8111, d3965, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38064 (p : Pattern) (guard : d0 p = 1) : d3983 p ≤ (0 : Int) + d360 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare38065 (p : Pattern) (guard : d8117 p = 1) : d3984 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3984, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38063 p hg
    simpa only [d8117, d3984, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3984, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38064 p hg
    simpa only [d8117, d3984, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38066 (p : Pattern) (guard : d0 p = 1) : d3990 p ≤ (0 : Int) + d371 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare38067 (p : Pattern) (guard : d8123 p = 1) : d3991 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d3991, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38065 p hg
    simpa only [d8123, d3991, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d3991, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38066 p hg
    simpa only [d8123, d3991, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38068 (p : Pattern) (guard : d0 p = 1) : d3995 p ≤ (0 : Int) + d375 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare38069 (p : Pattern) (guard : d8129 p = 1) : d3996 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d3996, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38067 p hg
    simpa only [d8129, d3996, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d3996, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38068 p hg
    simpa only [d8129, d3996, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38070 (p : Pattern) (guard : d0 p = 1) : d4001 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare38071 (p : Pattern) (guard : d8135 p = 1) : d4002 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d4002, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38069 p hg
    simpa only [d8135, d4002, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d4002, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38070 p hg
    simpa only [d8135, d4002, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38072 (p : Pattern) (guard : d8136 p = 1) : d4003 p ≤ (0 : Int) + d408 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d4003, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38057 p hg
    simpa only [d8136, d4003, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d4003, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38071 p hg
    simpa only [d8136, d4003, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38073 (p : Pattern) (guard : d0 p = 1) : d3830 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare38074 (p : Pattern) (guard : d8117 p = 1) : d4004 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d4004, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37978 p hg
    simpa only [d8117, d4004, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d4004, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38073 p hg
    simpa only [d8117, d4004, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38075 (p : Pattern) (guard : d0 p = 1) : d4005 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare38076 (p : Pattern) (guard : d8123 p = 1) : d4006 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d4006, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38074 p hg
    simpa only [d8123, d4006, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d4006, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38075 p hg
    simpa only [d8123, d4006, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38077 (p : Pattern) (guard : d8129 p = 1) : d4007 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d4007, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38076 p hg
    simpa only [d8129, d4007, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d4007, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37374 p hg
    simpa only [d8129, d4007, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38078 (p : Pattern) (guard : d8135 p = 1) : d4008 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d4008, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38077 p hg
    simpa only [d8135, d4008, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d4008, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37376 p hg
    simpa only [d8135, d4008, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38079 (p : Pattern) (guard : d0 p = 1) : d4018 p ≤ (0 : Int) + d411 p := by
  change (0 : Int) = 1 at guard
  omega
end NetHack.Sokoban22Refined85
