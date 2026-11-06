/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons264
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare37100 (p : Pattern) (guard : d8119 p = 1) : d3792 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d3792, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37093 p hg
    simpa only [d8119, d3792, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d3792, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37099 p hg
    simpa only [d8119, d3792, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37101 (p : Pattern) (guard : d8120 p = 1) : d3793 p ≤ (0 : Int) + d437 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d3793, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37054 p hg
    simpa only [d8120, d3793, d437, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d3793, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37100 p hg
    simpa only [d8120, d3793, d437, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37102 (p : Pattern) (guard : d1 p = 1) : d102 p ≤ (0 : Int) + d326 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1248 p hg
    simpa only [d326, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4579 p hg
    simpa only [d326, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37103 (p : Pattern) (guard : d8085 p = 1) : d102 p ≤ (0 : Int) + d328 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37102 p hg
    simpa only [d8085, d328, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37002 p hg
    simpa only [d8085, d328, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37104 (p : Pattern) (guard : d8090 p = 1) : d102 p ≤ (0 : Int) + d331 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37103 p hg
    simpa only [d8090, d331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37072 p hg
    simpa only [d8090, d331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37105 (p : Pattern) (guard : d8089 p = 1) : d3737 p ≤ (0 : Int) + d332 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d3737, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37002 p hg
    simpa only [d8089, d3737, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d3737, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36988 p hg
    simpa only [d8089, d3737, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37106 (p : Pattern) (guard : d8094 p = 1) : d3738 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d3738, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37105 p hg
    simpa only [d8094, d3738, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d3738, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37007 p hg
    simpa only [d8094, d3738, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37107 (p : Pattern) (guard : d8095 p = 1) : d3745 p ≤ (0 : Int) + d334 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d3745, d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37104 p hg
    simpa only [d8095, d3745, d334, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d3745, d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37106 p hg
    simpa only [d8095, d3745, d334, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37108 (p : Pattern) (guard : d8089 p = 1) : d3741 p ≤ (0 : Int) + d330 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d3741, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37071 p hg
    simpa only [d8089, d3741, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d3741, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36994 p hg
    simpa only [d8089, d3741, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37109 (p : Pattern) (guard : d8094 p = 1) : d3742 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d3742, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37108 p hg
    simpa only [d8094, d3742, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d3742, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37011 p hg
    simpa only [d8094, d3742, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37110 (p : Pattern) (guard : d8100 p = 1) : d3743 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3743, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37109 p hg
    simpa only [d8100, d3743, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3743, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d3743, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37111 (p : Pattern) (guard : d8101 p = 1) : d3746 p ≤ (0 : Int) + d337 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3746, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37107 p hg
    simpa only [d8101, d3746, d337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3746, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37110 p hg
    simpa only [d8101, d3746, d337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37112 (p : Pattern) (guard : d1 p = 1) : d115 p ≤ (0 : Int) + d34 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d115, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35207 p hg
    simpa only [d115, d34, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d115, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d115, d34, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37113 (p : Pattern) (guard : d8084 p = 1) : d115 p ≤ (0 : Int) + d364 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37112 p hg
    simpa only [d8084, d364, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35165 p hg
    simpa only [d8084, d364, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37114 (p : Pattern) (guard : d5847 p = 1) : d115 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35165 p hg
    simpa only [d5847, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17806 p hg
    simpa only [d5847, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37115 (p : Pattern) (guard : d8089 p = 1) : d115 p ≤ (0 : Int) + d365 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37113 p hg
    simpa only [d8089, d365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37114 p hg
    simpa only [d8089, d365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37116 (p : Pattern) (guard : d5854 p = 1) : d115 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37114 p hg
    simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17806 p hg
    simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37117 (p : Pattern) (guard : d8094 p = 1) : d115 p ≤ (0 : Int) + d366 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37115 p hg
    simpa only [d8094, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37116 p hg
    simpa only [d8094, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37118 (p : Pattern) (guard : d5854 p = 1) : d3794 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d3794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37114 p hg
    simpa only [d5854, d3794, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d3794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29551 p hg
    simpa only [d5854, d3794, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37119 (p : Pattern) (guard : d8099 p = 1) : d3795 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d3795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37118 p hg
    simpa only [d8099, d3795, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d3795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29551 p hg
    simpa only [d8099, d3795, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37120 (p : Pattern) (guard : d8100 p = 1) : d3796 p ≤ (0 : Int) + d367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3796, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37117 p hg
    simpa only [d8100, d3796, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3796, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37119 p hg
    simpa only [d8100, d3796, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37121 (p : Pattern) (guard : d5854 p = 1) : d3798 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d3798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37114 p hg
    simpa only [d5854, d3798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d3798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29556 p hg
    simpa only [d5854, d3798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37122 (p : Pattern) (guard : d8099 p = 1) : d3799 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d3799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37121 p hg
    simpa only [d8099, d3799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d3799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29556 p hg
    simpa only [d8099, d3799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37123 (p : Pattern) (guard : d8105 p = 1) : d3800 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d3800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37122 p hg
    simpa only [d8105, d3800, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d3800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d3800, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37124 (p : Pattern) (guard : d8106 p = 1) : d3801 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3801, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37120 p hg
    simpa only [d8106, d3801, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3801, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37123 p hg
    simpa only [d8106, d3801, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37125 (p : Pattern) (guard : d8107 p = 1) : d3802 p ≤ (0 : Int) + d415 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3802, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37111 p hg
    simpa only [d8107, d3802, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3802, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37124 p hg
    simpa only [d8107, d3802, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37126 (p : Pattern) (guard : d8084 p = 1) : d106 p ≤ (0 : Int) + d317 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1416 p hg
    simpa only [d8084, d317, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35130 p hg
    simpa only [d8084, d317, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37127 (p : Pattern) (guard : d8089 p = 1) : d106 p ≤ (0 : Int) + d318 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37126 p hg
    simpa only [d8089, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37027 p hg
    simpa only [d8089, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37128 (p : Pattern) (guard : d8094 p = 1) : d106 p ≤ (0 : Int) + d323 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37127 p hg
    simpa only [d8094, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37029 p hg
    simpa only [d8094, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37129 (p : Pattern) (guard : d8100 p = 1) : d3751 p ≤ (0 : Int) + d324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3751, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37128 p hg
    simpa only [d8100, d3751, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3751, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37032 p hg
    simpa only [d8100, d3751, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37130 (p : Pattern) (guard : d8106 p = 1) : d3756 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3756, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37129 p hg
    simpa only [d8106, d3756, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3756, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37036 p hg
    simpa only [d8106, d3756, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37131 (p : Pattern) (guard : d5847 p = 1) : d57 p ≤ (0 : Int) + d329 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19992 p hg
    simpa only [d5847, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17706 p hg
    simpa only [d5847, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37132 (p : Pattern) (guard : d5854 p = 1) : d57 p ≤ (0 : Int) + d330 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37131 p hg
    simpa only [d5854, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17706 p hg
    simpa only [d5854, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37133 (p : Pattern) (guard : d8099 p = 1) : d57 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37132 p hg
    simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17706 p hg
    simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37134 (p : Pattern) (guard : d8105 p = 1) : d3634 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d3634, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37133 p hg
    simpa only [d8105, d3634, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d3634, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36411 p hg
    simpa only [d8105, d3634, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37135 (p : Pattern) (guard : d8111 p = 1) : d3636 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3636, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37134 p hg
    simpa only [d8111, d3636, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3636, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36468 p hg
    simpa only [d8111, d3636, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37136 (p : Pattern) (guard : d8112 p = 1) : d3803 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3803, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37130 p hg
    simpa only [d8112, d3803, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3803, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37135 p hg
    simpa only [d8112, d3803, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37137 (p : Pattern) (guard : d8113 p = 1) : d3804 p ≤ (0 : Int) + d416 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d3804, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37125 p hg
    simpa only [d8113, d3804, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d3804, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37136 p hg
    simpa only [d8113, d3804, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37138 (p : Pattern) (guard : d5847 p = 1) : d39 p ≤ (0 : Int) + d327 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19939 p hg
    simpa only [d5847, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17682 p hg
    simpa only [d5847, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37139 (p : Pattern) (guard : d5854 p = 1) : d39 p ≤ (0 : Int) + d332 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37138 p hg
    simpa only [d5854, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17682 p hg
    simpa only [d5854, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37140 (p : Pattern) (guard : d8099 p = 1) : d39 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37139 p hg
    simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17682 p hg
    simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37141 (p : Pattern) (guard : d8105 p = 1) : d3638 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d3638, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37140 p hg
    simpa only [d8105, d3638, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d3638, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36416 p hg
    simpa only [d8105, d3638, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37142 (p : Pattern) (guard : d8111 p = 1) : d3639 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3639, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37141 p hg
    simpa only [d8111, d3639, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3639, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36471 p hg
    simpa only [d8111, d3639, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37143 (p : Pattern) (guard : d8112 p = 1) : d3805 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3805, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37037 p hg
    simpa only [d8112, d3805, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3805, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37142 p hg
    simpa only [d8112, d3805, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37144 (p : Pattern) (guard : d8118 p = 1) : d3806 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3806, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37143 p hg
    simpa only [d8118, d3806, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3806, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34734 p hg
    simpa only [d8118, d3806, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37145 (p : Pattern) (guard : d8119 p = 1) : d3807 p ≤ (0 : Int) + d417 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d3807, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37137 p hg
    simpa only [d8119, d3807, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d3807, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37144 p hg
    simpa only [d8119, d3807, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37146 (p : Pattern) (guard : d8084 p = 1) : d102 p ≤ (0 : Int) + d356 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35085 p hg
    simpa only [d8084, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35093 p hg
    simpa only [d8084, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37147 (p : Pattern) (guard : d8089 p = 1) : d102 p ≤ (0 : Int) + d357 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37146 p hg
    simpa only [d8089, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37003 p hg
    simpa only [d8089, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37148 (p : Pattern) (guard : d8094 p = 1) : d102 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37147 p hg
    simpa only [d8094, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37073 p hg
    simpa only [d8094, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37149 (p : Pattern) (guard : d8100 p = 1) : d3766 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3766, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37148 p hg
    simpa only [d8100, d3766, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3766, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37076 p hg
    simpa only [d8100, d3766, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37150 (p : Pattern) (guard : d8106 p = 1) : d3779 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3779, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37149 p hg
    simpa only [d8106, d3779, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3779, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37082 p hg
    simpa only [d8106, d3779, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37151 (p : Pattern) (guard : d8099 p = 1) : d115 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37116 p hg
    simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17806 p hg
    simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37152 (p : Pattern) (guard : d0 p = 1) : d3771 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37153 (p : Pattern) (guard : d8105 p = 1) : d3808 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d3808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37151 p hg
    simpa only [d8105, d3808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d3808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37152 p hg
    simpa only [d8105, d3808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37154 (p : Pattern) (guard : d8111 p = 1) : d3809 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37153 p hg
    simpa only [d8111, d3809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8111, d3809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37155 (p : Pattern) (guard : d8112 p = 1) : d3810 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3810, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37150 p hg
    simpa only [d8112, d3810, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3810, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37154 p hg
    simpa only [d8112, d3810, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37156 (p : Pattern) (guard : d8117 p = 1) : d3811 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37091 p hg
    simpa only [d8117, d3811, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36737 p hg
    simpa only [d8117, d3811, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37157 (p : Pattern) (guard : d8118 p = 1) : d3812 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3812, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37155 p hg
    simpa only [d8118, d3812, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3812, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37156 p hg
    simpa only [d8118, d3812, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37158 (p : Pattern) (guard : d0 p = 1) : d3650 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37159 (p : Pattern) (guard : d8117 p = 1) : d3813 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37091 p hg
    simpa only [d8117, d3813, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37158 p hg
    simpa only [d8117, d3813, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37160 (p : Pattern) (guard : d8123 p = 1) : d3814 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d3814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37159 p hg
    simpa only [d8123, d3814, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d3814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d3814, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37161 (p : Pattern) (guard : d8124 p = 1) : d3815 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d3815, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37157 p hg
    simpa only [d8124, d3815, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d3815, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37160 p hg
    simpa only [d8124, d3815, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37162 (p : Pattern) (guard : d8125 p = 1) : d3816 p ≤ (0 : Int) + d418 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d3816, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37145 p hg
    simpa only [d8125, d3816, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d3816, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37161 p hg
    simpa only [d8125, d3816, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37163 (p : Pattern) (guard : d8126 p = 1) : d3817 p ≤ (0 : Int) + d438 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d3817, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37101 p hg
    simpa only [d8126, d3817, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d3817, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37162 p hg
    simpa only [d8126, d3817, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37164 (p : Pattern) (guard : d5854 p = 1) : d3818 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d3818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36988 p hg
    simpa only [d5854, d3818, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d3818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29509 p hg
    simpa only [d5854, d3818, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37165 (p : Pattern) (guard : d8094 p = 1) : d3819 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d3819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37059 p hg
    simpa only [d8094, d3819, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d3819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37164 p hg
    simpa only [d8094, d3819, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37166 (p : Pattern) (guard : d8095 p = 1) : d3820 p ≤ (0 : Int) + d367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d3820, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37043 p hg
    simpa only [d8095, d3820, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d3820, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37165 p hg
    simpa only [d8095, d3820, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37167 (p : Pattern) (guard : d8100 p = 1) : d3821 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37008 p hg
    simpa only [d8100, d3821, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d3821, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37168 (p : Pattern) (guard : d8101 p = 1) : d3822 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3822, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37166 p hg
    simpa only [d8101, d3822, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3822, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37167 p hg
    simpa only [d8101, d3822, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37169 (p : Pattern) (guard : d8099 p = 1) : d3825 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d3825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37075 p hg
    simpa only [d8099, d3825, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d3825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31861 p hg
    simpa only [d8099, d3825, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37170 (p : Pattern) (guard : d8105 p = 1) : d3826 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d3826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37169 p hg
    simpa only [d8105, d3826, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d3826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d3826, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37171 (p : Pattern) (guard : d8106 p = 1) : d3827 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3827, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37149 p hg
    simpa only [d8106, d3827, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3827, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37170 p hg
    simpa only [d8106, d3827, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37172 (p : Pattern) (guard : d8107 p = 1) : d3828 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3828, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37168 p hg
    simpa only [d8107, d3828, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3828, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37171 p hg
    simpa only [d8107, d3828, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37173 (p : Pattern) (guard : d8105 p = 1) : d3829 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d3829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37076 p hg
    simpa only [d8105, d3829, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d3829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d3829, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37174 (p : Pattern) (guard : d8106 p = 1) : d3830 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3830, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37077 p hg
    simpa only [d8106, d3830, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3830, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37173 p hg
    simpa only [d8106, d3830, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37175 (p : Pattern) (guard : d0 p = 1) : d3831 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37176 (p : Pattern) (guard : d8111 p = 1) : d3832 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37090 p hg
    simpa only [d8111, d3832, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37175 p hg
    simpa only [d8111, d3832, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37177 (p : Pattern) (guard : d8112 p = 1) : d3833 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3833, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37174 p hg
    simpa only [d8112, d3833, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3833, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37176 p hg
    simpa only [d8112, d3833, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37178 (p : Pattern) (guard : d8113 p = 1) : d3834 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d3834, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37172 p hg
    simpa only [d8113, d3834, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d3834, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37177 p hg
    simpa only [d8113, d3834, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37179 (p : Pattern) (guard : d8106 p = 1) : d3830 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3830, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37086 p hg
    simpa only [d8106, d3830, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3830, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37173 p hg
    simpa only [d8106, d3830, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37180 (p : Pattern) (guard : d8112 p = 1) : d3833 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3833, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37179 p hg
    simpa only [d8112, d3833, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3833, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37176 p hg
    simpa only [d8112, d3833, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37181 (p : Pattern) (guard : d8117 p = 1) : d3759 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36469 p hg
    simpa only [d8117, d3759, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8117, d3759, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37182 (p : Pattern) (guard : d8118 p = 1) : d3835 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3835, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37180 p hg
    simpa only [d8118, d3835, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3835, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37181 p hg
    simpa only [d8118, d3835, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37183 (p : Pattern) (guard : d8119 p = 1) : d3836 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d3836, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37178 p hg
    simpa only [d8119, d3836, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d3836, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37182 p hg
    simpa only [d8119, d3836, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37184 (p : Pattern) (guard : d8089 p = 1) : d115 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37063 p hg
    simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37114 p hg
    simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37185 (p : Pattern) (guard : d8094 p = 1) : d115 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37184 p hg
    simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37116 p hg
    simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37186 (p : Pattern) (guard : d5854 p = 1) : d3768 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d3768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37114 p hg
    simpa only [d5854, d3768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d3768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29515 p hg
    simpa only [d5854, d3768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37187 (p : Pattern) (guard : d8099 p = 1) : d3771 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d3771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37186 p hg
    simpa only [d8099, d3771, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d3771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31797 p hg
    simpa only [d8099, d3771, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37188 (p : Pattern) (guard : d8100 p = 1) : d3808 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37185 p hg
    simpa only [d8100, d3808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37187 p hg
    simpa only [d8100, d3808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37189 (p : Pattern) (guard : d8105 p = 1) : d3772 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d3772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37187 p hg
    simpa only [d8105, d3772, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d3772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d3772, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37190 (p : Pattern) (guard : d8106 p = 1) : d3837 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37188 p hg
    simpa only [d8106, d3837, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37189 p hg
    simpa only [d8106, d3837, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37191 (p : Pattern) (guard : d5854 p = 1) : d119 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37079 p hg
    simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17810 p hg
    simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37192 (p : Pattern) (guard : d8099 p = 1) : d119 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37191 p hg
    simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17810 p hg
    simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37193 (p : Pattern) (guard : d0 p = 1) : d3777 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37194 (p : Pattern) (guard : d8105 p = 1) : d3838 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d3838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37192 p hg
    simpa only [d8105, d3838, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d3838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37193 p hg
    simpa only [d8105, d3838, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37195 (p : Pattern) (guard : d0 p = 1) : d3778 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37196 (p : Pattern) (guard : d8111 p = 1) : d3839 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37194 p hg
    simpa only [d8111, d3839, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37195 p hg
    simpa only [d8111, d3839, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37197 (p : Pattern) (guard : d8112 p = 1) : d3840 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37190 p hg
    simpa only [d8112, d3840, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37196 p hg
    simpa only [d8112, d3840, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37198 (p : Pattern) (guard : d8118 p = 1) : d3841 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37197 p hg
    simpa only [d8118, d3841, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34734 p hg
    simpa only [d8118, d3841, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37199 (p : Pattern) (guard : d8124 p = 1) : d3842 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d3842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37198 p hg
    simpa only [d8124, d3842, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d3842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34736 p hg
    simpa only [d8124, d3842, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37200 (p : Pattern) (guard : d8125 p = 1) : d3843 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d3843, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37183 p hg
    simpa only [d8125, d3843, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d3843, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37199 p hg
    simpa only [d8125, d3843, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37201 (p : Pattern) (guard : d8084 p = 1) : d102 p ≤ (0 : Int) + d315 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36981 p hg
    simpa only [d8084, d315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35093 p hg
    simpa only [d8084, d315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37202 (p : Pattern) (guard : d8089 p = 1) : d102 p ≤ (0 : Int) + d320 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37201 p hg
    simpa only [d8089, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37003 p hg
    simpa only [d8089, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37203 (p : Pattern) (guard : d8094 p = 1) : d102 p ≤ (0 : Int) + d321 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37202 p hg
    simpa only [d8094, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37073 p hg
    simpa only [d8094, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37204 (p : Pattern) (guard : d8100 p = 1) : d3766 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3766, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37203 p hg
    simpa only [d8100, d3766, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3766, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37076 p hg
    simpa only [d8100, d3766, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37205 (p : Pattern) (guard : d8106 p = 1) : d3827 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3827, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37204 p hg
    simpa only [d8106, d3827, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3827, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37170 p hg
    simpa only [d8106, d3827, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37206 (p : Pattern) (guard : d5843 p = 1) : d115 p ≤ (0 : Int) + d39 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d115, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35277 p hg
    simpa only [d5843, d115, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d115, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5843, d115, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37207 (p : Pattern) (guard : d5847 p = 1) : d115 p ≤ (0 : Int) + d327 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37206 p hg
    simpa only [d5847, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17806 p hg
    simpa only [d5847, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37208 (p : Pattern) (guard : d5854 p = 1) : d115 p ≤ (0 : Int) + d332 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37207 p hg
    simpa only [d5854, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17806 p hg
    simpa only [d5854, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37209 (p : Pattern) (guard : d8099 p = 1) : d115 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37208 p hg
    simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17806 p hg
    simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37210 (p : Pattern) (guard : d8105 p = 1) : d3808 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d3808, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37209 p hg
    simpa only [d8105, d3808, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d3808, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37152 p hg
    simpa only [d8105, d3808, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37211 (p : Pattern) (guard : d0 p = 1) : d3772 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37212 (p : Pattern) (guard : d8111 p = 1) : d3837 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3837, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37210 p hg
    simpa only [d8111, d3837, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3837, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37211 p hg
    simpa only [d8111, d3837, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37213 (p : Pattern) (guard : d8112 p = 1) : d3844 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3844, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37205 p hg
    simpa only [d8112, d3844, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3844, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37212 p hg
    simpa only [d8112, d3844, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37214 (p : Pattern) (guard : d8117 p = 1) : d3845 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37176 p hg
    simpa only [d8117, d3845, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36782 p hg
    simpa only [d8117, d3845, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37215 (p : Pattern) (guard : d8118 p = 1) : d3846 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3846, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37213 p hg
    simpa only [d8118, d3846, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3846, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37214 p hg
    simpa only [d8118, d3846, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37216 (p : Pattern) (guard : d0 p = 1) : d3639 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37217 (p : Pattern) (guard : d8117 p = 1) : d3847 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37176 p hg
    simpa only [d8117, d3847, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37216 p hg
    simpa only [d8117, d3847, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37218 (p : Pattern) (guard : d8123 p = 1) : d3848 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d3848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37217 p hg
    simpa only [d8123, d3848, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d3848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d3848, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37219 (p : Pattern) (guard : d8124 p = 1) : d3849 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d3849, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37215 p hg
    simpa only [d8124, d3849, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d3849, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37218 p hg
    simpa only [d8124, d3849, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37220 (p : Pattern) (guard : d8117 p = 1) : d3850 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37196 p hg
    simpa only [d8117, d3850, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8117, d3850, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37221 (p : Pattern) (guard : d8123 p = 1) : d3851 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d3851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37220 p hg
    simpa only [d8123, d3851, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d3851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d3851, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37222 (p : Pattern) (guard : d8129 p = 1) : d3852 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d3852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37221 p hg
    simpa only [d8129, d3852, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d3852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8129, d3852, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37223 (p : Pattern) (guard : d8130 p = 1) : d3853 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d3853, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37219 p hg
    simpa only [d8130, d3853, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d3853, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37222 p hg
    simpa only [d8130, d3853, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37224 (p : Pattern) (guard : d8131 p = 1) : d3854 p ≤ (0 : Int) + d439 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d3854, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37200 p hg
    simpa only [d8131, d3854, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d3854, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37223 p hg
    simpa only [d8131, d3854, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37225 (p : Pattern) (guard : d8132 p = 1) : d3855 p ≤ (0 : Int) + d440 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d3855, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37163 p hg
    simpa only [d8132, d3855, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d3855, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37224 p hg
    simpa only [d8132, d3855, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37226 (p : Pattern) (guard : d8095 p = 1) : d3820 p ≤ (0 : Int) + d351 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d3820, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37019 p hg
    simpa only [d8095, d3820, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d3820, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37165 p hg
    simpa only [d8095, d3820, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37227 (p : Pattern) (guard : d8101 p = 1) : d3822 p ≤ (0 : Int) + d352 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3822, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37226 p hg
    simpa only [d8101, d3822, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3822, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37167 p hg
    simpa only [d8101, d3822, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37228 (p : Pattern) (guard : d8107 p = 1) : d3828 p ≤ (0 : Int) + d355 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3828, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37227 p hg
    simpa only [d8107, d3828, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3828, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37205 p hg
    simpa only [d8107, d3828, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37229 (p : Pattern) (guard : d8106 p = 1) : d3830 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3830, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37149 p hg
    simpa only [d8106, d3830, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3830, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37173 p hg
    simpa only [d8106, d3830, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37230 (p : Pattern) (guard : d8112 p = 1) : d3833 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3833, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37229 p hg
    simpa only [d8112, d3833, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3833, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37176 p hg
    simpa only [d8112, d3833, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37231 (p : Pattern) (guard : d8113 p = 1) : d3834 p ≤ (0 : Int) + d362 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d3834, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37228 p hg
    simpa only [d8113, d3834, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d3834, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37230 p hg
    simpa only [d8113, d3834, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37232 (p : Pattern) (guard : d8118 p = 1) : d3835 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3835, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37177 p hg
    simpa only [d8118, d3835, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3835, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37181 p hg
    simpa only [d8118, d3835, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37233 (p : Pattern) (guard : d8119 p = 1) : d3836 p ≤ (0 : Int) + d395 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d3836, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37231 p hg
    simpa only [d8119, d3836, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d3836, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37232 p hg
    simpa only [d8119, d3836, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37234 (p : Pattern) (guard : d1 p = 1) : d115 p ≤ (0 : Int) + d39 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d115, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35277 p hg
    simpa only [d115, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d115, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d115, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37235 (p : Pattern) (guard : d8084 p = 1) : d115 p ≤ (0 : Int) + d327 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37234 p hg
    simpa only [d8084, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35165 p hg
    simpa only [d8084, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37236 (p : Pattern) (guard : d8089 p = 1) : d115 p ≤ (0 : Int) + d332 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37235 p hg
    simpa only [d8089, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37114 p hg
    simpa only [d8089, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37237 (p : Pattern) (guard : d8094 p = 1) : d115 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37236 p hg
    simpa only [d8094, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37116 p hg
    simpa only [d8094, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37238 (p : Pattern) (guard : d8100 p = 1) : d3808 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3808, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37237 p hg
    simpa only [d8100, d3808, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3808, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37187 p hg
    simpa only [d8100, d3808, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37239 (p : Pattern) (guard : d8106 p = 1) : d3837 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3837, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37238 p hg
    simpa only [d8106, d3837, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3837, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37189 p hg
    simpa only [d8106, d3837, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
