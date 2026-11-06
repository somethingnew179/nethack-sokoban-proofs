/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons324
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare45500 (p : Pattern) (guard : d8107 p = 1) : d3256 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3256, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45498 p hg
    simpa only [d8107, d3256, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3256, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45499 p hg
    simpa only [d8107, d3256, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45501 (p : Pattern) (guard : d8106 p = 1) : d3259 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3259, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44987 p hg
    simpa only [d8106, d3259, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3259, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44599 p hg
    simpa only [d8106, d3259, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45502 (p : Pattern) (guard : d8112 p = 1) : d3261 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3261, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45501 p hg
    simpa only [d8112, d3261, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3261, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44925 p hg
    simpa only [d8112, d3261, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45503 (p : Pattern) (guard : d8113 p = 1) : d3262 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d3262, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45500 p hg
    simpa only [d8113, d3262, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d3262, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45502 p hg
    simpa only [d8113, d3262, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45504 (p : Pattern) (guard : d8119 p = 1) : d3268 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d3268, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45503 p hg
    simpa only [d8119, d3268, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d3268, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44931 p hg
    simpa only [d8119, d3268, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45505 (p : Pattern) (guard : d8120 p = 1) : d3343 p ≤ (0 : Int) + d437 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d3343, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45497 p hg
    simpa only [d8120, d3343, d437, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d3343, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45504 p hg
    simpa only [d8120, d3343, d437, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45506 (p : Pattern) (guard : d8085 p = 1) : d3233 p ≤ (0 : Int) + d328 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d3233, d328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44353 p hg
    simpa only [d8085, d3233, d328, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d3233, d328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44984 p hg
    simpa only [d8085, d3233, d328, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45507 (p : Pattern) (guard : d8090 p = 1) : d3234 p ≤ (0 : Int) + d331 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d3234, d331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45506 p hg
    simpa only [d8090, d3234, d331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d3234, d331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45011 p hg
    simpa only [d8090, d3234, d331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45508 (p : Pattern) (guard : d8095 p = 1) : d3235 p ≤ (0 : Int) + d334 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d3235, d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45507 p hg
    simpa only [d8095, d3235, d334, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d3235, d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44986 p hg
    simpa only [d8095, d3235, d334, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45509 (p : Pattern) (guard : d8100 p = 1) : d3230 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3230, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45012 p hg
    simpa only [d8100, d3230, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3230, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d3230, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45510 (p : Pattern) (guard : d8101 p = 1) : d3236 p ≤ (0 : Int) + d337 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3236, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45508 p hg
    simpa only [d8101, d3236, d337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3236, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45509 p hg
    simpa only [d8101, d3236, d337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45511 (p : Pattern) (guard : d8084 p = 1) : d3250 p ≤ (0 : Int) + d364 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d3250, d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34783 p hg
    simpa only [d8084, d3250, d364, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d3250, d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d8084, d3250, d364, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45512 (p : Pattern) (guard : d8089 p = 1) : d3250 p ≤ (0 : Int) + d365 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45511 p hg
    simpa only [d8089, d365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44477 p hg
    simpa only [d8089, d365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45513 (p : Pattern) (guard : d8094 p = 1) : d3250 p ≤ (0 : Int) + d366 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45512 p hg
    simpa only [d8094, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44525 p hg
    simpa only [d8094, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45514 (p : Pattern) (guard : d8100 p = 1) : d3250 p ≤ (0 : Int) + d367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45513 p hg
    simpa only [d8100, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44702 p hg
    simpa only [d8100, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45515 (p : Pattern) (guard : d8106 p = 1) : d3275 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3275, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45514 p hg
    simpa only [d8106, d3275, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3275, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44745 p hg
    simpa only [d8106, d3275, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45516 (p : Pattern) (guard : d8107 p = 1) : d3344 p ≤ (0 : Int) + d415 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3344, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45510 p hg
    simpa only [d8107, d3344, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3344, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45515 p hg
    simpa only [d8107, d3344, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45517 (p : Pattern) (guard : d8084 p = 1) : d3239 p ≤ (0 : Int) + d317 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d3239, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34355 p hg
    simpa only [d8084, d3239, d317, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d3239, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d8084, d3239, d317, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45518 (p : Pattern) (guard : d8089 p = 1) : d3239 p ≤ (0 : Int) + d318 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45517 p hg
    simpa only [d8089, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44381 p hg
    simpa only [d8089, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45519 (p : Pattern) (guard : d8094 p = 1) : d3239 p ≤ (0 : Int) + d323 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45518 p hg
    simpa only [d8094, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44451 p hg
    simpa only [d8094, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45520 (p : Pattern) (guard : d8100 p = 1) : d3239 p ≤ (0 : Int) + d324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45519 p hg
    simpa only [d8100, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44668 p hg
    simpa only [d8100, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45521 (p : Pattern) (guard : d8106 p = 1) : d3241 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3241, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45520 p hg
    simpa only [d8106, d3241, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3241, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44724 p hg
    simpa only [d8106, d3241, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45522 (p : Pattern) (guard : d5847 p = 1) : d3244 p ≤ (0 : Int) + d329 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3244, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35427 p hg
    simpa only [d5847, d3244, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3244, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5847, d3244, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45523 (p : Pattern) (guard : d5854 p = 1) : d3244 p ≤ (0 : Int) + d330 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45522 p hg
    simpa only [d5854, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26636 p hg
    simpa only [d5854, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45524 (p : Pattern) (guard : d8099 p = 1) : d3244 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45523 p hg
    simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26636 p hg
    simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45525 (p : Pattern) (guard : d8105 p = 1) : d3244 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45524 p hg
    simpa only [d8105, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26636 p hg
    simpa only [d8105, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45526 (p : Pattern) (guard : d8111 p = 1) : d3246 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3246, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45525 p hg
    simpa only [d8111, d3246, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3246, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44748 p hg
    simpa only [d8111, d3246, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45527 (p : Pattern) (guard : d8112 p = 1) : d3277 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3277, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45521 p hg
    simpa only [d8112, d3277, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3277, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45526 p hg
    simpa only [d8112, d3277, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45528 (p : Pattern) (guard : d8113 p = 1) : d3345 p ≤ (0 : Int) + d416 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d3345, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45516 p hg
    simpa only [d8113, d3345, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d3345, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45527 p hg
    simpa only [d8113, d3345, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45529 (p : Pattern) (guard : d5847 p = 1) : d3279 p ≤ (0 : Int) + d327 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3279, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35435 p hg
    simpa only [d5847, d3279, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3279, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5847, d3279, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45530 (p : Pattern) (guard : d5854 p = 1) : d3279 p ≤ (0 : Int) + d332 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45529 p hg
    simpa only [d5854, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26681 p hg
    simpa only [d5854, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45531 (p : Pattern) (guard : d8099 p = 1) : d3279 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45530 p hg
    simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26681 p hg
    simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45532 (p : Pattern) (guard : d8105 p = 1) : d3279 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45531 p hg
    simpa only [d8105, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26681 p hg
    simpa only [d8105, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45533 (p : Pattern) (guard : d8111 p = 1) : d3281 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3281, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45532 p hg
    simpa only [d8111, d3281, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3281, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44752 p hg
    simpa only [d8111, d3281, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45534 (p : Pattern) (guard : d8112 p = 1) : d3282 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3282, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45491 p hg
    simpa only [d8112, d3282, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3282, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45533 p hg
    simpa only [d8112, d3282, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45535 (p : Pattern) (guard : d8118 p = 1) : d3285 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3285, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45534 p hg
    simpa only [d8118, d3285, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3285, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44757 p hg
    simpa only [d8118, d3285, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45536 (p : Pattern) (guard : d8119 p = 1) : d3346 p ≤ (0 : Int) + d417 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d3346, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45528 p hg
    simpa only [d8119, d3346, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d3346, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45535 p hg
    simpa only [d8119, d3346, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45537 (p : Pattern) (guard : d8106 p = 1) : d3255 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3255, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45146 p hg
    simpa only [d8106, d3255, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3255, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44735 p hg
    simpa only [d8106, d3255, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45538 (p : Pattern) (guard : d8112 p = 1) : d3288 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3288, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45537 p hg
    simpa only [d8112, d3288, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3288, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44955 p hg
    simpa only [d8112, d3288, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45539 (p : Pattern) (guard : d8118 p = 1) : d3290 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3290, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45538 p hg
    simpa only [d8118, d3290, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3290, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44958 p hg
    simpa only [d8118, d3290, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45540 (p : Pattern) (guard : d8124 p = 1) : d3296 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d3296, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45539 p hg
    simpa only [d8124, d3296, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d3296, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44963 p hg
    simpa only [d8124, d3296, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45541 (p : Pattern) (guard : d8125 p = 1) : d3347 p ≤ (0 : Int) + d418 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d3347, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45536 p hg
    simpa only [d8125, d3347, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d3347, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45540 p hg
    simpa only [d8125, d3347, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45542 (p : Pattern) (guard : d8126 p = 1) : d3348 p ≤ (0 : Int) + d438 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d3348, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45505 p hg
    simpa only [d8126, d3348, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d3348, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45541 p hg
    simpa only [d8126, d3348, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45543 (p : Pattern) (guard : d8107 p = 1) : d3238 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44937 p hg
    simpa only [d8107, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45147 p hg
    simpa only [d8107, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45544 (p : Pattern) (guard : d8112 p = 1) : d3242 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3242, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45014 p hg
    simpa only [d8112, d3242, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3242, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44971 p hg
    simpa only [d8112, d3242, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45545 (p : Pattern) (guard : d8113 p = 1) : d3299 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d3299, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45543 p hg
    simpa only [d8113, d3299, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d3299, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45544 p hg
    simpa only [d8113, d3299, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45546 (p : Pattern) (guard : d8118 p = 1) : d3248 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3248, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45139 p hg
    simpa only [d8118, d3248, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3248, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44974 p hg
    simpa only [d8118, d3248, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45547 (p : Pattern) (guard : d8119 p = 1) : d3300 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d3300, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45545 p hg
    simpa only [d8119, d3300, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d3300, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45546 p hg
    simpa only [d8119, d3300, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45548 (p : Pattern) (guard : d8125 p = 1) : d3305 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d3305, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45547 p hg
    simpa only [d8125, d3305, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d3305, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44982 p hg
    simpa only [d8125, d3305, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45549 (p : Pattern) (guard : d8084 p = 1) : d3226 p ≤ (0 : Int) + d315 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d3226, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33795 p hg
    simpa only [d8084, d3226, d315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d3226, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d8084, d3226, d315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45550 (p : Pattern) (guard : d8089 p = 1) : d3226 p ≤ (0 : Int) + d320 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45549 p hg
    simpa only [d8089, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44429 p hg
    simpa only [d8089, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45551 (p : Pattern) (guard : d8094 p = 1) : d3226 p ≤ (0 : Int) + d321 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45550 p hg
    simpa only [d8094, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44662 p hg
    simpa only [d8094, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45552 (p : Pattern) (guard : d8100 p = 1) : d3226 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45551 p hg
    simpa only [d8100, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44919 p hg
    simpa only [d8100, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45553 (p : Pattern) (guard : d8106 p = 1) : d3238 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3238, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45552 p hg
    simpa only [d8106, d3238, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3238, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44967 p hg
    simpa only [d8106, d3238, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45554 (p : Pattern) (guard : d5847 p = 1) : d3250 p ≤ (0 : Int) + d327 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3250, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35467 p hg
    simpa only [d5847, d3250, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3250, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5847, d3250, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45555 (p : Pattern) (guard : d5854 p = 1) : d3250 p ≤ (0 : Int) + d332 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45554 p hg
    simpa only [d5854, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26644 p hg
    simpa only [d5854, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45556 (p : Pattern) (guard : d8099 p = 1) : d3250 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45555 p hg
    simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26644 p hg
    simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45557 (p : Pattern) (guard : d8105 p = 1) : d3250 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45556 p hg
    simpa only [d8105, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26644 p hg
    simpa only [d8105, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45558 (p : Pattern) (guard : d8111 p = 1) : d3275 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3275, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45557 p hg
    simpa only [d8111, d3275, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3275, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44989 p hg
    simpa only [d8111, d3275, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45559 (p : Pattern) (guard : d8112 p = 1) : d3306 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3306, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45553 p hg
    simpa only [d8112, d3306, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3306, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45558 p hg
    simpa only [d8112, d3306, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45560 (p : Pattern) (guard : d8118 p = 1) : d3307 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3307, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45559 p hg
    simpa only [d8118, d3307, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3307, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44993 p hg
    simpa only [d8118, d3307, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45561 (p : Pattern) (guard : d8124 p = 1) : d3308 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d3308, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45560 p hg
    simpa only [d8124, d3308, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d3308, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44998 p hg
    simpa only [d8124, d3308, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45562 (p : Pattern) (guard : d8130 p = 1) : d3312 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d3312, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45561 p hg
    simpa only [d8130, d3312, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d3312, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45002 p hg
    simpa only [d8130, d3312, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45563 (p : Pattern) (guard : d8131 p = 1) : d3313 p ≤ (0 : Int) + d439 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d3313, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45548 p hg
    simpa only [d8131, d3313, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d3313, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45562 p hg
    simpa only [d8131, d3313, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45564 (p : Pattern) (guard : d8132 p = 1) : d3349 p ≤ (0 : Int) + d440 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d3349, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45542 p hg
    simpa only [d8132, d3349, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d3349, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45563 p hg
    simpa only [d8132, d3349, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45565 (p : Pattern) (guard : d8107 p = 1) : d3238 p ≤ (0 : Int) + d355 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45114 p hg
    simpa only [d8107, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45553 p hg
    simpa only [d8107, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45566 (p : Pattern) (guard : d8112 p = 1) : d3242 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3242, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45147 p hg
    simpa only [d8112, d3242, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3242, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44971 p hg
    simpa only [d8112, d3242, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45567 (p : Pattern) (guard : d8113 p = 1) : d3299 p ≤ (0 : Int) + d362 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d3299, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45565 p hg
    simpa only [d8113, d3299, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d3299, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45566 p hg
    simpa only [d8113, d3299, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45568 (p : Pattern) (guard : d8118 p = 1) : d3248 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3248, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45544 p hg
    simpa only [d8118, d3248, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3248, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44974 p hg
    simpa only [d8118, d3248, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45569 (p : Pattern) (guard : d8119 p = 1) : d3300 p ≤ (0 : Int) + d395 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d3300, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45567 p hg
    simpa only [d8119, d3300, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d3300, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45568 p hg
    simpa only [d8119, d3300, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45570 (p : Pattern) (guard : d8112 p = 1) : d3302 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3302, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44866 p hg
    simpa only [d8112, d3302, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3302, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44979 p hg
    simpa only [d8112, d3302, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45571 (p : Pattern) (guard : d8118 p = 1) : d3303 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3303, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45570 p hg
    simpa only [d8118, d3303, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3303, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44757 p hg
    simpa only [d8118, d3303, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45572 (p : Pattern) (guard : d8124 p = 1) : d3304 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d3304, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45571 p hg
    simpa only [d8124, d3304, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d3304, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34736 p hg
    simpa only [d8124, d3304, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45573 (p : Pattern) (guard : d8125 p = 1) : d3305 p ≤ (0 : Int) + d397 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d3305, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45569 p hg
    simpa only [d8125, d3305, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d3305, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45572 p hg
    simpa only [d8125, d3305, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45574 (p : Pattern) (guard : d8084 p = 1) : d3226 p ≤ (0 : Int) + d317 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d3226, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33799 p hg
    simpa only [d8084, d3226, d317, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d3226, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d8084, d3226, d317, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45575 (p : Pattern) (guard : d8089 p = 1) : d3226 p ≤ (0 : Int) + d318 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45574 p hg
    simpa only [d8089, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44429 p hg
    simpa only [d8089, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45576 (p : Pattern) (guard : d8094 p = 1) : d3226 p ≤ (0 : Int) + d323 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45575 p hg
    simpa only [d8094, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44662 p hg
    simpa only [d8094, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45577 (p : Pattern) (guard : d8100 p = 1) : d3226 p ≤ (0 : Int) + d324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45576 p hg
    simpa only [d8100, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44919 p hg
    simpa only [d8100, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45578 (p : Pattern) (guard : d8106 p = 1) : d3238 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3238, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45577 p hg
    simpa only [d8106, d3238, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3238, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44967 p hg
    simpa only [d8106, d3238, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45579 (p : Pattern) (guard : d5847 p = 1) : d3250 p ≤ (0 : Int) + d329 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3250, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35624 p hg
    simpa only [d5847, d3250, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3250, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5847, d3250, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45580 (p : Pattern) (guard : d5854 p = 1) : d3250 p ≤ (0 : Int) + d330 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45579 p hg
    simpa only [d5854, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26644 p hg
    simpa only [d5854, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45581 (p : Pattern) (guard : d8099 p = 1) : d3250 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45580 p hg
    simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26644 p hg
    simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45582 (p : Pattern) (guard : d8105 p = 1) : d3250 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45581 p hg
    simpa only [d8105, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26644 p hg
    simpa only [d8105, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45583 (p : Pattern) (guard : d8111 p = 1) : d3275 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3275, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45582 p hg
    simpa only [d8111, d3275, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3275, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44989 p hg
    simpa only [d8111, d3275, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45584 (p : Pattern) (guard : d8112 p = 1) : d3306 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3306, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45578 p hg
    simpa only [d8112, d3306, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3306, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45583 p hg
    simpa only [d8112, d3306, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45585 (p : Pattern) (guard : d5847 p = 1) : d3239 p ≤ (0 : Int) + d327 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3239, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35486 p hg
    simpa only [d5847, d3239, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3239, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5847, d3239, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45586 (p : Pattern) (guard : d5854 p = 1) : d3239 p ≤ (0 : Int) + d332 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45585 p hg
    simpa only [d5854, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26627 p hg
    simpa only [d5854, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45587 (p : Pattern) (guard : d8099 p = 1) : d3239 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45586 p hg
    simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26627 p hg
    simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45588 (p : Pattern) (guard : d8105 p = 1) : d3239 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45587 p hg
    simpa only [d8105, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26627 p hg
    simpa only [d8105, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45589 (p : Pattern) (guard : d8111 p = 1) : d3241 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3241, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45588 p hg
    simpa only [d8111, d3241, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3241, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44970 p hg
    simpa only [d8111, d3241, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45590 (p : Pattern) (guard : d8117 p = 1) : d3277 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3277, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45589 p hg
    simpa only [d8117, d3277, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3277, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44992 p hg
    simpa only [d8117, d3277, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45591 (p : Pattern) (guard : d8118 p = 1) : d3307 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3307, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45584 p hg
    simpa only [d8118, d3307, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3307, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45590 p hg
    simpa only [d8118, d3307, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45592 (p : Pattern) (guard : d8124 p = 1) : d3308 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d3308, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45591 p hg
    simpa only [d8124, d3308, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d3308, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44998 p hg
    simpa only [d8124, d3308, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45593 (p : Pattern) (guard : d8130 p = 1) : d3312 p ≤ (0 : Int) + d399 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d3312, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45592 p hg
    simpa only [d8130, d3312, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d3312, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45002 p hg
    simpa only [d8130, d3312, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45594 (p : Pattern) (guard : d8131 p = 1) : d3313 p ≤ (0 : Int) + d400 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d3313, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45573 p hg
    simpa only [d8131, d3313, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d3313, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45593 p hg
    simpa only [d8131, d3313, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45595 (p : Pattern) (guard : d8112 p = 1) : d3315 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3315, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44835 p hg
    simpa only [d8112, d3315, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3315, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44756 p hg
    simpa only [d8112, d3315, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45596 (p : Pattern) (guard : d8118 p = 1) : d3316 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3316, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45595 p hg
    simpa only [d8118, d3316, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3316, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44757 p hg
    simpa only [d8118, d3316, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45597 (p : Pattern) (guard : d8123 p = 1) : d3317 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d3317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44757 p hg
    simpa only [d8123, d3317, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d3317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d3317, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45598 (p : Pattern) (guard : d8124 p = 1) : d3318 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d3318, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45596 p hg
    simpa only [d8124, d3318, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d3318, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45597 p hg
    simpa only [d8124, d3318, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45599 (p : Pattern) (guard : d8129 p = 1) : d3319 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d3319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45597 p hg
    simpa only [d8129, d3319, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d3319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8129, d3319, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45600 (p : Pattern) (guard : d8130 p = 1) : d3320 p ≤ (0 : Int) + d421 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d3320, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45598 p hg
    simpa only [d8130, d3320, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d3320, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45599 p hg
    simpa only [d8130, d3320, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45601 (p : Pattern) (guard : d8135 p = 1) : d3321 p ≤ (0 : Int) + d12 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d3321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45599 p hg
    simpa only [d8135, d3321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d3321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8135, d3321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45602 (p : Pattern) (guard : d8136 p = 1) : d3322 p ≤ (0 : Int) + d441 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d3322, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45600 p hg
    simpa only [d8136, d3322, d441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d3322, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45601 p hg
    simpa only [d8136, d3322, d441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45603 (p : Pattern) (guard : d8137 p = 1) : d3323 p ≤ (0 : Int) + d442 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d3323, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45594 p hg
    simpa only [d8137, d3323, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d3323, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45602 p hg
    simpa only [d8137, d3323, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45604 (p : Pattern) (guard : d8138 p = 1) : d3350 p ≤ (0 : Int) + d443 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8132 p = 1 := by simpa only [d8138, d3350, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45564 p hg
    simpa only [d8138, d3350, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8137 p = 1 := by simpa only [d8138, d3350, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45603 p hg
    simpa only [d8138, d3350, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45605 (p : Pattern) (guard : d8107 p = 1) : d3238 p ≤ (0 : Int) + d346 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45485 p hg
    simpa only [d8107, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45578 p hg
    simpa only [d8107, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45606 (p : Pattern) (guard : d8112 p = 1) : d3242 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3242, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45553 p hg
    simpa only [d8112, d3242, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3242, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45589 p hg
    simpa only [d8112, d3242, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45607 (p : Pattern) (guard : d8113 p = 1) : d3299 p ≤ (0 : Int) + d402 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d3299, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45605 p hg
    simpa only [d8113, d3299, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d3299, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45606 p hg
    simpa only [d8113, d3299, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45608 (p : Pattern) (guard : d8118 p = 1) : d3248 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3248, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45566 p hg
    simpa only [d8118, d3248, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3248, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44974 p hg
    simpa only [d8118, d3248, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45609 (p : Pattern) (guard : d8119 p = 1) : d3300 p ≤ (0 : Int) + d404 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d3300, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45607 p hg
    simpa only [d8119, d3300, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d3300, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45608 p hg
    simpa only [d8119, d3300, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45610 (p : Pattern) (guard : d8111 p = 1) : d3441 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44954 p hg
    simpa only [d8111, d3441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44978 p hg
    simpa only [d8111, d3441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45611 (p : Pattern) (guard : d8112 p = 1) : d3442 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3442, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44891 p hg
    simpa only [d8112, d3442, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3442, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45610 p hg
    simpa only [d8112, d3442, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45612 (p : Pattern) (guard : d8111 p = 1) : d3443 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44954 p hg
    simpa only [d8111, d3443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44755 p hg
    simpa only [d8111, d3443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45613 (p : Pattern) (guard : d0 p = 1) : d3444 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare45614 (p : Pattern) (guard : d8117 p = 1) : d3445 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45612 p hg
    simpa only [d8117, d3445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45613 p hg
    simpa only [d8117, d3445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45615 (p : Pattern) (guard : d8118 p = 1) : d3446 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3446, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45611 p hg
    simpa only [d8118, d3446, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3446, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45614 p hg
    simpa only [d8118, d3446, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45616 (p : Pattern) (guard : d8117 p = 1) : d3447 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44955 p hg
    simpa only [d8117, d3447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45613 p hg
    simpa only [d8117, d3447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45617 (p : Pattern) (guard : d8123 p = 1) : d3448 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d3448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45616 p hg
    simpa only [d8123, d3448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d3448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44962 p hg
    simpa only [d8123, d3448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45618 (p : Pattern) (guard : d8124 p = 1) : d3449 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d3449, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45615 p hg
    simpa only [d8124, d3449, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d3449, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45617 p hg
    simpa only [d8124, d3449, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45619 (p : Pattern) (guard : d8125 p = 1) : d3450 p ≤ (0 : Int) + d406 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d3450, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45609 p hg
    simpa only [d8125, d3450, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d3450, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45618 p hg
    simpa only [d8125, d3450, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45620 (p : Pattern) (guard : d8084 p = 1) : d3226 p ≤ (0 : Int) + d364 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d3226, d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33863 p hg
    simpa only [d8084, d3226, d364, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d3226, d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d8084, d3226, d364, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45621 (p : Pattern) (guard : d8089 p = 1) : d3226 p ≤ (0 : Int) + d365 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45620 p hg
    simpa only [d8089, d365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44429 p hg
    simpa only [d8089, d365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45622 (p : Pattern) (guard : d8094 p = 1) : d3226 p ≤ (0 : Int) + d366 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45621 p hg
    simpa only [d8094, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44662 p hg
    simpa only [d8094, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45623 (p : Pattern) (guard : d8100 p = 1) : d3226 p ≤ (0 : Int) + d367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45622 p hg
    simpa only [d8100, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44919 p hg
    simpa only [d8100, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45624 (p : Pattern) (guard : d8106 p = 1) : d3238 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3238, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45623 p hg
    simpa only [d8106, d3238, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3238, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44967 p hg
    simpa only [d8106, d3238, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45625 (p : Pattern) (guard : d5847 p = 1) : d3250 p ≤ (0 : Int) + d356 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3250, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35514 p hg
    simpa only [d5847, d3250, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3250, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5847, d3250, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45626 (p : Pattern) (guard : d5854 p = 1) : d3250 p ≤ (0 : Int) + d357 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45625 p hg
    simpa only [d5854, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26644 p hg
    simpa only [d5854, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45627 (p : Pattern) (guard : d8099 p = 1) : d3250 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45626 p hg
    simpa only [d8099, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26644 p hg
    simpa only [d8099, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45628 (p : Pattern) (guard : d8105 p = 1) : d3250 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45627 p hg
    simpa only [d8105, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26644 p hg
    simpa only [d8105, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45629 (p : Pattern) (guard : d8111 p = 1) : d3275 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3275, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45628 p hg
    simpa only [d8111, d3275, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3275, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44989 p hg
    simpa only [d8111, d3275, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45630 (p : Pattern) (guard : d8112 p = 1) : d3306 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3306, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45624 p hg
    simpa only [d8112, d3306, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3306, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45629 p hg
    simpa only [d8112, d3306, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45631 (p : Pattern) (guard : d5847 p = 1) : d3239 p ≤ (0 : Int) + d329 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3239, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35521 p hg
    simpa only [d5847, d3239, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3239, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5847, d3239, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45632 (p : Pattern) (guard : d5854 p = 1) : d3239 p ≤ (0 : Int) + d330 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45631 p hg
    simpa only [d5854, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26627 p hg
    simpa only [d5854, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45633 (p : Pattern) (guard : d8099 p = 1) : d3239 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45632 p hg
    simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26627 p hg
    simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45634 (p : Pattern) (guard : d8105 p = 1) : d3239 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45633 p hg
    simpa only [d8105, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26627 p hg
    simpa only [d8105, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45635 (p : Pattern) (guard : d8111 p = 1) : d3241 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3241, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45634 p hg
    simpa only [d8111, d3241, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3241, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44970 p hg
    simpa only [d8111, d3241, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45636 (p : Pattern) (guard : d8117 p = 1) : d3277 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3277, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45635 p hg
    simpa only [d8117, d3277, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3277, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44992 p hg
    simpa only [d8117, d3277, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45637 (p : Pattern) (guard : d8118 p = 1) : d3307 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3307, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45630 p hg
    simpa only [d8118, d3307, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3307, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45636 p hg
    simpa only [d8118, d3307, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45638 (p : Pattern) (guard : d8117 p = 1) : d3282 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3282, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45589 p hg
    simpa only [d8117, d3282, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3282, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44995 p hg
    simpa only [d8117, d3282, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45639 (p : Pattern) (guard : d8123 p = 1) : d3285 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d3285, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45638 p hg
    simpa only [d8123, d3285, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d3285, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44997 p hg
    simpa only [d8123, d3285, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
