/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons319
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare44800 (p : Pattern) (guard : d8102 p = 1) : d3242 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d3242, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44625 p hg
    simpa only [d8102, d3242, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d3242, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44692 p hg
    simpa only [d8102, d3242, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44801 (p : Pattern) (guard : d1 p = 1) : d3244 p ≤ (0 : Int) + d329 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d3244, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34762 p hg
    simpa only [d3244, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d3244, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d3244, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44802 (p : Pattern) (guard : d8085 p = 1) : d3244 p ≤ (0 : Int) + d330 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44801 p hg
    simpa only [d8085, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44404 p hg
    simpa only [d8085, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44803 (p : Pattern) (guard : d8090 p = 1) : d3244 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44802 p hg
    simpa only [d8090, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44408 p hg
    simpa only [d8090, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44804 (p : Pattern) (guard : d8095 p = 1) : d3244 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44803 p hg
    simpa only [d8095, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44461 p hg
    simpa only [d8095, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44805 (p : Pattern) (guard : d8101 p = 1) : d3246 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3246, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44804 p hg
    simpa only [d8101, d3246, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3246, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44492 p hg
    simpa only [d8101, d3246, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44806 (p : Pattern) (guard : d8107 p = 1) : d3247 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3247, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44805 p hg
    simpa only [d8107, d3247, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3247, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34455 p hg
    simpa only [d8107, d3247, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44807 (p : Pattern) (guard : d8108 p = 1) : d3248 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d3248, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44800 p hg
    simpa only [d8108, d3248, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d3248, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44806 p hg
    simpa only [d8108, d3248, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44808 (p : Pattern) (guard : d8109 p = 1) : d3342 p ≤ (0 : Int) + d436 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8103 p = 1 := by simpa only [d8109, d3342, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44799 p hg
    simpa only [d8109, d3342, d436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8108 p = 1 := by simpa only [d8109, d3342, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44807 p hg
    simpa only [d8109, d3342, d436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44809 (p : Pattern) (guard : d8096 p = 1) : d3252 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d3252, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44578 p hg
    simpa only [d8096, d3252, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d3252, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44481 p hg
    simpa only [d8096, d3252, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44810 (p : Pattern) (guard : d8101 p = 1) : d3255 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3255, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44743 p hg
    simpa only [d8101, d3255, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3255, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44568 p hg
    simpa only [d8101, d3255, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44811 (p : Pattern) (guard : d8102 p = 1) : d3256 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d3256, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44809 p hg
    simpa only [d8102, d3256, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d3256, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44810 p hg
    simpa only [d8102, d3256, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44812 (p : Pattern) (guard : d8101 p = 1) : d3259 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3259, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44700 p hg
    simpa only [d8101, d3259, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3259, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44514 p hg
    simpa only [d8101, d3259, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44813 (p : Pattern) (guard : d8107 p = 1) : d3261 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3261, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44812 p hg
    simpa only [d8107, d3261, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3261, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44670 p hg
    simpa only [d8107, d3261, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44814 (p : Pattern) (guard : d8108 p = 1) : d3262 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d3262, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44811 p hg
    simpa only [d8108, d3262, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d3262, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44813 p hg
    simpa only [d8108, d3262, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44815 (p : Pattern) (guard : d8114 p = 1) : d3268 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d3268, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44814 p hg
    simpa only [d8114, d3268, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d3268, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44676 p hg
    simpa only [d8114, d3268, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44816 (p : Pattern) (guard : d8115 p = 1) : d3343 p ≤ (0 : Int) + d437 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8109 p = 1 := by simpa only [d8115, d3343, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44808 p hg
    simpa only [d8115, d3343, d437, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8114 p = 1 := by simpa only [d8115, d3343, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44815 p hg
    simpa only [d8115, d3343, d437, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44817 (p : Pattern) (guard : d8086 p = 1) : d3234 p ≤ (0 : Int) + d331 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d3234, d331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44355 p hg
    simpa only [d8086, d3234, d331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d3234, d331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44741 p hg
    simpa only [d8086, d3234, d331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44818 (p : Pattern) (guard : d8091 p = 1) : d3235 p ≤ (0 : Int) + d334 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d3235, d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44817 p hg
    simpa only [d8091, d3235, d334, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d3235, d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44699 p hg
    simpa only [d8091, d3235, d334, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44819 (p : Pattern) (guard : d8095 p = 1) : d3230 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d3230, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44742 p hg
    simpa only [d8095, d3230, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d3230, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34367 p hg
    simpa only [d8095, d3230, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44820 (p : Pattern) (guard : d8096 p = 1) : d3236 p ≤ (0 : Int) + d337 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d3236, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44818 p hg
    simpa only [d8096, d3236, d337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d3236, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44819 p hg
    simpa only [d8096, d3236, d337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44821 (p : Pattern) (guard : d1 p = 1) : d3250 p ≤ (0 : Int) + d364 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d3250, d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34783 p hg
    simpa only [d3250, d364, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d3250, d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d3250, d364, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44822 (p : Pattern) (guard : d8085 p = 1) : d3250 p ≤ (0 : Int) + d365 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44821 p hg
    simpa only [d8085, d365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44421 p hg
    simpa only [d8085, d365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44823 (p : Pattern) (guard : d8090 p = 1) : d3250 p ≤ (0 : Int) + d366 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44822 p hg
    simpa only [d8090, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44478 p hg
    simpa only [d8090, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44824 (p : Pattern) (guard : d8095 p = 1) : d3250 p ≤ (0 : Int) + d367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44823 p hg
    simpa only [d8095, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44526 p hg
    simpa only [d8095, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44825 (p : Pattern) (guard : d8101 p = 1) : d3275 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3275, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44824 p hg
    simpa only [d8101, d3275, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3275, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44584 p hg
    simpa only [d8101, d3275, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44826 (p : Pattern) (guard : d8102 p = 1) : d3344 p ≤ (0 : Int) + d415 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d3344, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44820 p hg
    simpa only [d8102, d3344, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d3344, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44825 p hg
    simpa only [d8102, d3344, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44827 (p : Pattern) (guard : d8085 p = 1) : d3239 p ≤ (0 : Int) + d318 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44375 p hg
    simpa only [d8085, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44378 p hg
    simpa only [d8085, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44828 (p : Pattern) (guard : d8090 p = 1) : d3239 p ≤ (0 : Int) + d323 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44827 p hg
    simpa only [d8090, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44382 p hg
    simpa only [d8090, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44829 (p : Pattern) (guard : d8095 p = 1) : d3239 p ≤ (0 : Int) + d324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44828 p hg
    simpa only [d8095, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44452 p hg
    simpa only [d8095, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44830 (p : Pattern) (guard : d8101 p = 1) : d3241 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3241, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44829 p hg
    simpa only [d8101, d3241, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3241, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44551 p hg
    simpa only [d8101, d3241, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44831 (p : Pattern) (guard : d8084 p = 1) : d3244 p ≤ (0 : Int) + d329 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d3244, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34762 p hg
    simpa only [d8084, d3244, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d3244, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d8084, d3244, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44832 (p : Pattern) (guard : d8089 p = 1) : d3244 p ≤ (0 : Int) + d330 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44831 p hg
    simpa only [d8089, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44407 p hg
    simpa only [d8089, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44833 (p : Pattern) (guard : d8094 p = 1) : d3244 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44832 p hg
    simpa only [d8094, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44460 p hg
    simpa only [d8094, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44834 (p : Pattern) (guard : d8100 p = 1) : d3244 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44833 p hg
    simpa only [d8100, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44530 p hg
    simpa only [d8100, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44835 (p : Pattern) (guard : d8106 p = 1) : d3246 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3246, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44834 p hg
    simpa only [d8106, d3246, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3246, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44592 p hg
    simpa only [d8106, d3246, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44836 (p : Pattern) (guard : d8107 p = 1) : d3277 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3277, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44830 p hg
    simpa only [d8107, d3277, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3277, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44835 p hg
    simpa only [d8107, d3277, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44837 (p : Pattern) (guard : d8108 p = 1) : d3345 p ≤ (0 : Int) + d416 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d3345, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44826 p hg
    simpa only [d8108, d3345, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d3345, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44836 p hg
    simpa only [d8108, d3345, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44838 (p : Pattern) (guard : d8084 p = 1) : d3279 p ≤ (0 : Int) + d327 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d3279, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34801 p hg
    simpa only [d8084, d3279, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d3279, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d8084, d3279, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44839 (p : Pattern) (guard : d8089 p = 1) : d3279 p ≤ (0 : Int) + d332 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44838 p hg
    simpa only [d8089, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44499 p hg
    simpa only [d8089, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44840 (p : Pattern) (guard : d8094 p = 1) : d3279 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44839 p hg
    simpa only [d8094, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44502 p hg
    simpa only [d8094, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44841 (p : Pattern) (guard : d8100 p = 1) : d3279 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44840 p hg
    simpa only [d8100, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44535 p hg
    simpa only [d8100, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44842 (p : Pattern) (guard : d8106 p = 1) : d3281 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3281, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44841 p hg
    simpa only [d8106, d3281, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3281, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44596 p hg
    simpa only [d8106, d3281, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44843 (p : Pattern) (guard : d8107 p = 1) : d3282 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3282, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44797 p hg
    simpa only [d8107, d3282, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3282, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44842 p hg
    simpa only [d8107, d3282, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44844 (p : Pattern) (guard : d8113 p = 1) : d3285 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d3285, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44843 p hg
    simpa only [d8113, d3285, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d3285, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44601 p hg
    simpa only [d8113, d3285, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44845 (p : Pattern) (guard : d8114 p = 1) : d3346 p ≤ (0 : Int) + d417 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d3346, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44837 p hg
    simpa only [d8114, d3346, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d3346, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44844 p hg
    simpa only [d8114, d3346, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44846 (p : Pattern) (guard : d8101 p = 1) : d3255 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3255, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44773 p hg
    simpa only [d8101, d3255, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3255, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44568 p hg
    simpa only [d8101, d3255, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44847 (p : Pattern) (guard : d8107 p = 1) : d3288 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3288, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44846 p hg
    simpa only [d8107, d3288, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3288, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44704 p hg
    simpa only [d8107, d3288, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44848 (p : Pattern) (guard : d8113 p = 1) : d3290 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d3290, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44847 p hg
    simpa only [d8113, d3290, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d3290, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44708 p hg
    simpa only [d8113, d3290, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44849 (p : Pattern) (guard : d8119 p = 1) : d3296 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d3296, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44848 p hg
    simpa only [d8119, d3296, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d3296, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44716 p hg
    simpa only [d8119, d3296, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44850 (p : Pattern) (guard : d8120 p = 1) : d3347 p ≤ (0 : Int) + d418 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d3347, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44845 p hg
    simpa only [d8120, d3347, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d3347, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44849 p hg
    simpa only [d8120, d3347, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44851 (p : Pattern) (guard : d8121 p = 1) : d3348 p ≤ (0 : Int) + d438 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8115 p = 1 := by simpa only [d8121, d3348, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44816 p hg
    simpa only [d8121, d3348, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8120 p = 1 := by simpa only [d8121, d3348, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44850 p hg
    simpa only [d8121, d3348, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44852 (p : Pattern) (guard : d8102 p = 1) : d3238 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44625 p hg
    simpa only [d8102, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44774 p hg
    simpa only [d8102, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44853 (p : Pattern) (guard : d8107 p = 1) : d3242 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3242, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44744 p hg
    simpa only [d8107, d3242, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3242, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44725 p hg
    simpa only [d8107, d3242, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44854 (p : Pattern) (guard : d8108 p = 1) : d3299 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d3299, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44852 p hg
    simpa only [d8108, d3299, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d3299, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44853 p hg
    simpa only [d8108, d3299, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44855 (p : Pattern) (guard : d8113 p = 1) : d3248 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d3248, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44767 p hg
    simpa only [d8113, d3248, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d3248, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44728 p hg
    simpa only [d8113, d3248, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44856 (p : Pattern) (guard : d8114 p = 1) : d3300 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d3300, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44854 p hg
    simpa only [d8114, d3300, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d3300, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44855 p hg
    simpa only [d8114, d3300, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44857 (p : Pattern) (guard : d8120 p = 1) : d3305 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d3305, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44856 p hg
    simpa only [d8120, d3305, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d3305, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44739 p hg
    simpa only [d8120, d3305, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44858 (p : Pattern) (guard : d8085 p = 1) : d3226 p ≤ (0 : Int) + d320 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44341 p hg
    simpa only [d8085, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44360 p hg
    simpa only [d8085, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44859 (p : Pattern) (guard : d8090 p = 1) : d3226 p ≤ (0 : Int) + d321 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44858 p hg
    simpa only [d8090, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44430 p hg
    simpa only [d8090, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44860 (p : Pattern) (guard : d8095 p = 1) : d3226 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44859 p hg
    simpa only [d8095, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44663 p hg
    simpa only [d8095, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44861 (p : Pattern) (guard : d8101 p = 1) : d3238 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3238, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44860 p hg
    simpa only [d8101, d3238, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3238, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44720 p hg
    simpa only [d8101, d3238, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44862 (p : Pattern) (guard : d8084 p = 1) : d3250 p ≤ (0 : Int) + d327 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d3250, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34521 p hg
    simpa only [d8084, d3250, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d3250, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d8084, d3250, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44863 (p : Pattern) (guard : d8089 p = 1) : d3250 p ≤ (0 : Int) + d332 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44862 p hg
    simpa only [d8089, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44477 p hg
    simpa only [d8089, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44864 (p : Pattern) (guard : d8094 p = 1) : d3250 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44863 p hg
    simpa only [d8094, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44525 p hg
    simpa only [d8094, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44865 (p : Pattern) (guard : d8100 p = 1) : d3250 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44864 p hg
    simpa only [d8100, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44702 p hg
    simpa only [d8100, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44866 (p : Pattern) (guard : d8106 p = 1) : d3275 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3275, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44865 p hg
    simpa only [d8106, d3275, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3275, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44745 p hg
    simpa only [d8106, d3275, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44867 (p : Pattern) (guard : d8107 p = 1) : d3306 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3306, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44861 p hg
    simpa only [d8107, d3306, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3306, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44866 p hg
    simpa only [d8107, d3306, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44868 (p : Pattern) (guard : d8113 p = 1) : d3307 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d3307, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44867 p hg
    simpa only [d8113, d3307, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d3307, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44750 p hg
    simpa only [d8113, d3307, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44869 (p : Pattern) (guard : d8119 p = 1) : d3308 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d3308, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44868 p hg
    simpa only [d8119, d3308, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d3308, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44758 p hg
    simpa only [d8119, d3308, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44870 (p : Pattern) (guard : d8125 p = 1) : d3312 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d3312, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44869 p hg
    simpa only [d8125, d3312, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d3312, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44762 p hg
    simpa only [d8125, d3312, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44871 (p : Pattern) (guard : d8126 p = 1) : d3313 p ≤ (0 : Int) + d439 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d3313, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44857 p hg
    simpa only [d8126, d3313, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d3313, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44870 p hg
    simpa only [d8126, d3313, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44872 (p : Pattern) (guard : d8127 p = 1) : d3349 p ≤ (0 : Int) + d440 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8121 p = 1 := by simpa only [d8127, d3349, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44851 p hg
    simpa only [d8127, d3349, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8126 p = 1 := by simpa only [d8127, d3349, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44871 p hg
    simpa only [d8127, d3349, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44873 (p : Pattern) (guard : d8102 p = 1) : d3238 p ≤ (0 : Int) + d355 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44681 p hg
    simpa only [d8102, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44861 p hg
    simpa only [d8102, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44874 (p : Pattern) (guard : d8107 p = 1) : d3242 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3242, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44774 p hg
    simpa only [d8107, d3242, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3242, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44725 p hg
    simpa only [d8107, d3242, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44875 (p : Pattern) (guard : d8108 p = 1) : d3299 p ≤ (0 : Int) + d362 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d3299, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44873 p hg
    simpa only [d8108, d3299, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d3299, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44874 p hg
    simpa only [d8108, d3299, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44876 (p : Pattern) (guard : d8113 p = 1) : d3248 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d3248, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44853 p hg
    simpa only [d8113, d3248, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d3248, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44728 p hg
    simpa only [d8113, d3248, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44877 (p : Pattern) (guard : d8114 p = 1) : d3300 p ≤ (0 : Int) + d395 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d3300, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44875 p hg
    simpa only [d8114, d3300, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d3300, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44876 p hg
    simpa only [d8114, d3300, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44878 (p : Pattern) (guard : d8101 p = 1) : d3275 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3275, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44527 p hg
    simpa only [d8101, d3275, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3275, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44584 p hg
    simpa only [d8101, d3275, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44879 (p : Pattern) (guard : d8107 p = 1) : d3302 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3302, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44878 p hg
    simpa only [d8107, d3302, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3302, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44736 p hg
    simpa only [d8107, d3302, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44880 (p : Pattern) (guard : d8113 p = 1) : d3303 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d3303, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44879 p hg
    simpa only [d8113, d3303, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d3303, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44601 p hg
    simpa only [d8113, d3303, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44881 (p : Pattern) (guard : d8119 p = 1) : d3304 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d3304, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44880 p hg
    simpa only [d8119, d3304, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d3304, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34613 p hg
    simpa only [d8119, d3304, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44882 (p : Pattern) (guard : d8120 p = 1) : d3305 p ≤ (0 : Int) + d397 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d3305, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44877 p hg
    simpa only [d8120, d3305, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d3305, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44881 p hg
    simpa only [d8120, d3305, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44883 (p : Pattern) (guard : d8085 p = 1) : d3226 p ≤ (0 : Int) + d318 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44343 p hg
    simpa only [d8085, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44360 p hg
    simpa only [d8085, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44884 (p : Pattern) (guard : d8090 p = 1) : d3226 p ≤ (0 : Int) + d323 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44883 p hg
    simpa only [d8090, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44430 p hg
    simpa only [d8090, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44885 (p : Pattern) (guard : d8095 p = 1) : d3226 p ≤ (0 : Int) + d324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44884 p hg
    simpa only [d8095, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44663 p hg
    simpa only [d8095, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44886 (p : Pattern) (guard : d8101 p = 1) : d3238 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3238, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44885 p hg
    simpa only [d8101, d3238, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3238, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44720 p hg
    simpa only [d8101, d3238, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44887 (p : Pattern) (guard : d8084 p = 1) : d3250 p ≤ (0 : Int) + d329 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d3250, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34584 p hg
    simpa only [d8084, d3250, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d3250, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d8084, d3250, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44888 (p : Pattern) (guard : d8089 p = 1) : d3250 p ≤ (0 : Int) + d330 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44887 p hg
    simpa only [d8089, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44477 p hg
    simpa only [d8089, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44889 (p : Pattern) (guard : d8094 p = 1) : d3250 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44888 p hg
    simpa only [d8094, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44525 p hg
    simpa only [d8094, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44890 (p : Pattern) (guard : d8100 p = 1) : d3250 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44889 p hg
    simpa only [d8100, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44702 p hg
    simpa only [d8100, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44891 (p : Pattern) (guard : d8106 p = 1) : d3275 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3275, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44890 p hg
    simpa only [d8106, d3275, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3275, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44745 p hg
    simpa only [d8106, d3275, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44892 (p : Pattern) (guard : d8107 p = 1) : d3306 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3306, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44886 p hg
    simpa only [d8107, d3306, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3306, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44891 p hg
    simpa only [d8107, d3306, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44893 (p : Pattern) (guard : d8084 p = 1) : d3239 p ≤ (0 : Int) + d327 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d3239, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34592 p hg
    simpa only [d8084, d3239, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d3239, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d8084, d3239, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44894 (p : Pattern) (guard : d8089 p = 1) : d3239 p ≤ (0 : Int) + d332 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44893 p hg
    simpa only [d8089, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44381 p hg
    simpa only [d8089, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44895 (p : Pattern) (guard : d8094 p = 1) : d3239 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44894 p hg
    simpa only [d8094, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44451 p hg
    simpa only [d8094, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44896 (p : Pattern) (guard : d8100 p = 1) : d3239 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44895 p hg
    simpa only [d8100, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44668 p hg
    simpa only [d8100, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44897 (p : Pattern) (guard : d8106 p = 1) : d3241 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3241, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44896 p hg
    simpa only [d8106, d3241, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3241, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44724 p hg
    simpa only [d8106, d3241, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44898 (p : Pattern) (guard : d8112 p = 1) : d3277 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3277, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44897 p hg
    simpa only [d8112, d3277, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3277, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44749 p hg
    simpa only [d8112, d3277, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44899 (p : Pattern) (guard : d8113 p = 1) : d3307 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d3307, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44892 p hg
    simpa only [d8113, d3307, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d3307, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44898 p hg
    simpa only [d8113, d3307, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44900 (p : Pattern) (guard : d8119 p = 1) : d3308 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d3308, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44899 p hg
    simpa only [d8119, d3308, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d3308, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44758 p hg
    simpa only [d8119, d3308, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44901 (p : Pattern) (guard : d8125 p = 1) : d3312 p ≤ (0 : Int) + d399 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d3312, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44900 p hg
    simpa only [d8125, d3312, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d3312, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44762 p hg
    simpa only [d8125, d3312, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44902 (p : Pattern) (guard : d8126 p = 1) : d3313 p ≤ (0 : Int) + d400 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d3313, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44882 p hg
    simpa only [d8126, d3313, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d3313, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44901 p hg
    simpa only [d8126, d3313, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44903 (p : Pattern) (guard : d8107 p = 1) : d3315 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3315, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44805 p hg
    simpa only [d8107, d3315, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3315, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44600 p hg
    simpa only [d8107, d3315, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44904 (p : Pattern) (guard : d8113 p = 1) : d3316 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d3316, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44903 p hg
    simpa only [d8113, d3316, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d3316, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44601 p hg
    simpa only [d8113, d3316, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44905 (p : Pattern) (guard : d8118 p = 1) : d3317 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44601 p hg
    simpa only [d8118, d3317, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34734 p hg
    simpa only [d8118, d3317, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44906 (p : Pattern) (guard : d8119 p = 1) : d3318 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d3318, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44904 p hg
    simpa only [d8119, d3318, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d3318, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44905 p hg
    simpa only [d8119, d3318, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44907 (p : Pattern) (guard : d8124 p = 1) : d3319 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d3319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44905 p hg
    simpa only [d8124, d3319, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d3319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34736 p hg
    simpa only [d8124, d3319, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44908 (p : Pattern) (guard : d8125 p = 1) : d3320 p ≤ (0 : Int) + d421 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d3320, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44906 p hg
    simpa only [d8125, d3320, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d3320, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44907 p hg
    simpa only [d8125, d3320, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44909 (p : Pattern) (guard : d8130 p = 1) : d3321 p ≤ (0 : Int) + d12 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d3321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44907 p hg
    simpa only [d8130, d3321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d3321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36647 p hg
    simpa only [d8130, d3321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44910 (p : Pattern) (guard : d8131 p = 1) : d3322 p ≤ (0 : Int) + d441 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d3322, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44908 p hg
    simpa only [d8131, d3322, d441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d3322, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44909 p hg
    simpa only [d8131, d3322, d441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44911 (p : Pattern) (guard : d8132 p = 1) : d3323 p ≤ (0 : Int) + d442 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d3323, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44902 p hg
    simpa only [d8132, d3323, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d3323, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44910 p hg
    simpa only [d8132, d3323, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44912 (p : Pattern) (guard : d8133 p = 1) : d3350 p ≤ (0 : Int) + d443 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8127 p = 1 := by simpa only [d8133, d3350, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44872 p hg
    simpa only [d8133, d3350, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8132 p = 1 := by simpa only [d8133, d3350, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44911 p hg
    simpa only [d8133, d3350, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44913 (p : Pattern) (guard : d8102 p = 1) : d3238 p ≤ (0 : Int) + d346 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44792 p hg
    simpa only [d8102, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44886 p hg
    simpa only [d8102, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44914 (p : Pattern) (guard : d8107 p = 1) : d3242 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3242, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44861 p hg
    simpa only [d8107, d3242, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3242, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44897 p hg
    simpa only [d8107, d3242, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44915 (p : Pattern) (guard : d8108 p = 1) : d3299 p ≤ (0 : Int) + d402 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d3299, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44913 p hg
    simpa only [d8108, d3299, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d3299, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44914 p hg
    simpa only [d8108, d3299, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44916 (p : Pattern) (guard : d8113 p = 1) : d3248 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d3248, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44874 p hg
    simpa only [d8113, d3248, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d3248, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44728 p hg
    simpa only [d8113, d3248, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44917 (p : Pattern) (guard : d8114 p = 1) : d3300 p ≤ (0 : Int) + d404 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d3300, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44915 p hg
    simpa only [d8114, d3300, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d3300, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44916 p hg
    simpa only [d8114, d3300, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44918 (p : Pattern) (guard : d8101 p = 1) : d3252 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3252, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44743 p hg
    simpa only [d8101, d3252, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3252, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44584 p hg
    simpa only [d8101, d3252, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44919 (p : Pattern) (guard : d8099 p = 1) : d3226 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44662 p hg
    simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26609 p hg
    simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44920 (p : Pattern) (guard : d8100 p = 1) : d3226 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44663 p hg
    simpa only [d8100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44919 p hg
    simpa only [d8100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44921 (p : Pattern) (guard : d8106 p = 1) : d3255 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44920 p hg
    simpa only [d8106, d3255, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44735 p hg
    simpa only [d8106, d3255, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44922 (p : Pattern) (guard : d8107 p = 1) : d3256 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3256, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44918 p hg
    simpa only [d8107, d3256, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3256, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44921 p hg
    simpa only [d8107, d3256, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44923 (p : Pattern) (guard : d8106 p = 1) : d3259 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44920 p hg
    simpa only [d8106, d3259, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44599 p hg
    simpa only [d8106, d3259, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44924 (p : Pattern) (guard : d8105 p = 1) : d3239 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44668 p hg
    simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26627 p hg
    simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44925 (p : Pattern) (guard : d8111 p = 1) : d3260 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44924 p hg
    simpa only [d8111, d3260, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8111, d3260, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44926 (p : Pattern) (guard : d8112 p = 1) : d3261 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44923 p hg
    simpa only [d8112, d3261, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44925 p hg
    simpa only [d8112, d3261, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44927 (p : Pattern) (guard : d8113 p = 1) : d3262 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d3262, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44922 p hg
    simpa only [d8113, d3262, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d3262, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44926 p hg
    simpa only [d8113, d3262, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44928 (p : Pattern) (guard : d8106 p = 1) : d3263 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44920 p hg
    simpa only [d8106, d3263, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34532 p hg
    simpa only [d8106, d3263, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44929 (p : Pattern) (guard : d8112 p = 1) : d3264 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44928 p hg
    simpa only [d8112, d3264, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44925 p hg
    simpa only [d8112, d3264, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44930 (p : Pattern) (guard : d8117 p = 1) : d3266 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44707 p hg
    simpa only [d8117, d3266, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8117, d3266, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44931 (p : Pattern) (guard : d8118 p = 1) : d3267 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44929 p hg
    simpa only [d8118, d3267, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44930 p hg
    simpa only [d8118, d3267, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44932 (p : Pattern) (guard : d8119 p = 1) : d3268 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d3268, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44927 p hg
    simpa only [d8119, d3268, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d3268, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44931 p hg
    simpa only [d8119, d3268, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44933 (p : Pattern) (guard : d8120 p = 1) : d3351 p ≤ (0 : Int) + d406 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d3351, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44917 p hg
    simpa only [d8120, d3351, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d3351, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44932 p hg
    simpa only [d8120, d3351, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44934 (p : Pattern) (guard : d8085 p = 1) : d3226 p ≤ (0 : Int) + d365 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44416 p hg
    simpa only [d8085, d365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44360 p hg
    simpa only [d8085, d365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44935 (p : Pattern) (guard : d8090 p = 1) : d3226 p ≤ (0 : Int) + d366 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44934 p hg
    simpa only [d8090, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44430 p hg
    simpa only [d8090, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44936 (p : Pattern) (guard : d8095 p = 1) : d3226 p ≤ (0 : Int) + d367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44935 p hg
    simpa only [d8095, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44663 p hg
    simpa only [d8095, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44937 (p : Pattern) (guard : d8101 p = 1) : d3238 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3238, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44936 p hg
    simpa only [d8101, d3238, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3238, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44720 p hg
    simpa only [d8101, d3238, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44938 (p : Pattern) (guard : d8084 p = 1) : d3250 p ≤ (0 : Int) + d356 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d3250, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34879 p hg
    simpa only [d8084, d3250, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d3250, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d8084, d3250, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44939 (p : Pattern) (guard : d8089 p = 1) : d3250 p ≤ (0 : Int) + d357 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44938 p hg
    simpa only [d8089, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44477 p hg
    simpa only [d8089, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
