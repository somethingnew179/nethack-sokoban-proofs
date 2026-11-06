/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons317
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare44520 (p : Pattern) (guard : d8091 p = 1) : d3226 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44519 p hg
    simpa only [d8091, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44431 p hg
    simpa only [d8091, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44521 (p : Pattern) (guard : d8096 p = 1) : d3255 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d3255, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44520 p hg
    simpa only [d8096, d3255, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d3255, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44439 p hg
    simpa only [d8096, d3255, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44522 (p : Pattern) (guard : d1 p = 1) : d3250 p ≤ (0 : Int) + d327 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d3250, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34521 p hg
    simpa only [d3250, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d3250, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d3250, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44523 (p : Pattern) (guard : d8085 p = 1) : d3250 p ≤ (0 : Int) + d332 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44522 p hg
    simpa only [d8085, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44421 p hg
    simpa only [d8085, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44524 (p : Pattern) (guard : d8090 p = 1) : d3250 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44523 p hg
    simpa only [d8090, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44478 p hg
    simpa only [d8090, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44525 (p : Pattern) (guard : d5854 p = 1) : d3250 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44477 p hg
    simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26644 p hg
    simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44526 (p : Pattern) (guard : d8094 p = 1) : d3250 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44478 p hg
    simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44525 p hg
    simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44527 (p : Pattern) (guard : d8095 p = 1) : d3250 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44524 p hg
    simpa only [d8095, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44526 p hg
    simpa only [d8095, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44528 (p : Pattern) (guard : d8101 p = 1) : d3287 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3287, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44527 p hg
    simpa only [d8101, d3287, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3287, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34443 p hg
    simpa only [d8101, d3287, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44529 (p : Pattern) (guard : d8102 p = 1) : d3288 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d3288, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44521 p hg
    simpa only [d8102, d3288, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d3288, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44528 p hg
    simpa only [d8102, d3288, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44530 (p : Pattern) (guard : d8099 p = 1) : d3244 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44460 p hg
    simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26636 p hg
    simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44531 (p : Pattern) (guard : d8100 p = 1) : d3244 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44461 p hg
    simpa only [d8100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44530 p hg
    simpa only [d8100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44532 (p : Pattern) (guard : d8106 p = 1) : d3265 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44531 p hg
    simpa only [d8106, d3265, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34532 p hg
    simpa only [d8106, d3265, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44533 (p : Pattern) (guard : d8107 p = 1) : d3289 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44454 p hg
    simpa only [d8107, d3289, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44532 p hg
    simpa only [d8107, d3289, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44534 (p : Pattern) (guard : d8108 p = 1) : d3290 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d3290, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44529 p hg
    simpa only [d8108, d3290, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d3290, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44533 p hg
    simpa only [d8108, d3290, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44535 (p : Pattern) (guard : d8099 p = 1) : d3279 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44502 p hg
    simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26681 p hg
    simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44536 (p : Pattern) (guard : d8100 p = 1) : d3279 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44503 p hg
    simpa only [d8100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44535 p hg
    simpa only [d8100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44537 (p : Pattern) (guard : d8106 p = 1) : d3291 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44536 p hg
    simpa only [d8106, d3291, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34532 p hg
    simpa only [d8106, d3291, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44538 (p : Pattern) (guard : d8107 p = 1) : d3292 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44454 p hg
    simpa only [d8107, d3292, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44537 p hg
    simpa only [d8107, d3292, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44539 (p : Pattern) (guard : d8099 p = 1) : d3257 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44511 p hg
    simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26655 p hg
    simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44540 (p : Pattern) (guard : d8100 p = 1) : d3257 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44512 p hg
    simpa only [d8100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44539 p hg
    simpa only [d8100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44541 (p : Pattern) (guard : d8106 p = 1) : d3293 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44540 p hg
    simpa only [d8106, d3293, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34532 p hg
    simpa only [d8106, d3293, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44542 (p : Pattern) (guard : d8112 p = 1) : d3294 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44541 p hg
    simpa only [d8112, d3294, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34543 p hg
    simpa only [d8112, d3294, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44543 (p : Pattern) (guard : d8113 p = 1) : d3295 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d3295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44538 p hg
    simpa only [d8113, d3295, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d3295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44542 p hg
    simpa only [d8113, d3295, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44544 (p : Pattern) (guard : d8114 p = 1) : d3296 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d3296, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44534 p hg
    simpa only [d8114, d3296, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d3296, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44543 p hg
    simpa only [d8114, d3296, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44545 (p : Pattern) (guard : d8115 p = 1) : d3297 p ≤ (0 : Int) + d392 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8109 p = 1 := by simpa only [d8115, d3297, d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44518 p hg
    simpa only [d8115, d3297, d392, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8114 p = 1 := by simpa only [d8115, d3297, d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44544 p hg
    simpa only [d8115, d3297, d392, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44546 (p : Pattern) (guard : d8116 p = 1) : d3298 p ≤ (0 : Int) + d393 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8110 p = 1 := by simpa only [d8116, d3298, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44467 p hg
    simpa only [d8116, d3298, d393, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8115 p = 1 := by simpa only [d8116, d3298, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44545 p hg
    simpa only [d8116, d3298, d393, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44547 (p : Pattern) (guard : d8095 p = 1) : d3230 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d3230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44431 p hg
    simpa only [d8095, d3230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d3230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34367 p hg
    simpa only [d8095, d3230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44548 (p : Pattern) (guard : d8096 p = 1) : d3238 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d3238, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44520 p hg
    simpa only [d8096, d3238, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d3238, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44547 p hg
    simpa only [d8096, d3238, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44549 (p : Pattern) (guard : d8097 p = 1) : d3238 p ≤ (0 : Int) + d355 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8092 p = 1 := by simpa only [d8097, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44394 p hg
    simpa only [d8097, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8096 p = 1 := by simpa only [d8097, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44548 p hg
    simpa only [d8097, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44550 (p : Pattern) (guard : d8096 p = 1) : d3238 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d3238, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44432 p hg
    simpa only [d8096, d3238, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d3238, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44547 p hg
    simpa only [d8096, d3238, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44551 (p : Pattern) (guard : d8100 p = 1) : d3240 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44452 p hg
    simpa only [d8100, d3240, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d3240, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44552 (p : Pattern) (guard : d8101 p = 1) : d3241 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44453 p hg
    simpa only [d8101, d3241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44551 p hg
    simpa only [d8101, d3241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44553 (p : Pattern) (guard : d8102 p = 1) : d3242 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d3242, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44550 p hg
    simpa only [d8102, d3242, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d3242, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44552 p hg
    simpa only [d8102, d3242, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44554 (p : Pattern) (guard : d8103 p = 1) : d3299 p ≤ (0 : Int) + d362 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8097 p = 1 := by simpa only [d8103, d3299, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44549 p hg
    simpa only [d8103, d3299, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8102 p = 1 := by simpa only [d8103, d3299, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44553 p hg
    simpa only [d8103, d3299, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44555 (p : Pattern) (guard : d8096 p = 1) : d3238 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d3238, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44442 p hg
    simpa only [d8096, d3238, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d3238, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44547 p hg
    simpa only [d8096, d3238, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44556 (p : Pattern) (guard : d8102 p = 1) : d3242 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d3242, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44555 p hg
    simpa only [d8102, d3242, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d3242, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44552 p hg
    simpa only [d8102, d3242, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44557 (p : Pattern) (guard : d8101 p = 1) : d3246 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44462 p hg
    simpa only [d8101, d3246, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44492 p hg
    simpa only [d8101, d3246, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44558 (p : Pattern) (guard : d8107 p = 1) : d3247 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44557 p hg
    simpa only [d8107, d3247, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34455 p hg
    simpa only [d8107, d3247, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44559 (p : Pattern) (guard : d8108 p = 1) : d3248 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d3248, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44556 p hg
    simpa only [d8108, d3248, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d3248, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44558 p hg
    simpa only [d8108, d3248, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44560 (p : Pattern) (guard : d8109 p = 1) : d3300 p ≤ (0 : Int) + d395 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8103 p = 1 := by simpa only [d8109, d3300, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44554 p hg
    simpa only [d8109, d3300, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8108 p = 1 := by simpa only [d8109, d3300, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44559 p hg
    simpa only [d8109, d3300, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44561 (p : Pattern) (guard : d1 p = 1) : d3250 p ≤ (0 : Int) + d332 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44522 p hg
    simpa only [d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44420 p hg
    simpa only [d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44562 (p : Pattern) (guard : d8086 p = 1) : d3250 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44561 p hg
    simpa only [d8086, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44422 p hg
    simpa only [d8086, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44563 (p : Pattern) (guard : d8091 p = 1) : d3250 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44562 p hg
    simpa only [d8091, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44479 p hg
    simpa only [d8091, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44564 (p : Pattern) (guard : d8096 p = 1) : d3275 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d3275, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44563 p hg
    simpa only [d8096, d3275, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d3275, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44481 p hg
    simpa only [d8096, d3275, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44565 (p : Pattern) (guard : d5854 p = 1) : d3253 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44436 p hg
    simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26649 p hg
    simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44566 (p : Pattern) (guard : d8094 p = 1) : d3253 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44437 p hg
    simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44565 p hg
    simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44567 (p : Pattern) (guard : d8095 p = 1) : d3253 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44438 p hg
    simpa only [d8095, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44566 p hg
    simpa only [d8095, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44568 (p : Pattern) (guard : d8100 p = 1) : d3254 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44566 p hg
    simpa only [d8100, d3254, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d3254, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44569 (p : Pattern) (guard : d8101 p = 1) : d3301 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44567 p hg
    simpa only [d8101, d3301, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44568 p hg
    simpa only [d8101, d3301, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44570 (p : Pattern) (guard : d8102 p = 1) : d3302 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d3302, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44564 p hg
    simpa only [d8102, d3302, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d3302, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44569 p hg
    simpa only [d8102, d3302, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44571 (p : Pattern) (guard : d8095 p = 1) : d3257 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44448 p hg
    simpa only [d8095, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44512 p hg
    simpa only [d8095, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44572 (p : Pattern) (guard : d8101 p = 1) : d3283 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44571 p hg
    simpa only [d8101, d3283, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44514 p hg
    simpa only [d8101, d3283, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44573 (p : Pattern) (guard : d8107 p = 1) : d3284 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44572 p hg
    simpa only [d8107, d3284, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34455 p hg
    simpa only [d8107, d3284, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44574 (p : Pattern) (guard : d8108 p = 1) : d3303 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d3303, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44570 p hg
    simpa only [d8108, d3303, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d3303, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44573 p hg
    simpa only [d8108, d3303, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44575 (p : Pattern) (guard : d8114 p = 1) : d3304 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d3304, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44574 p hg
    simpa only [d8114, d3304, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d3304, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34577 p hg
    simpa only [d8114, d3304, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44576 (p : Pattern) (guard : d8115 p = 1) : d3305 p ≤ (0 : Int) + d397 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8109 p = 1 := by simpa only [d8115, d3305, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44560 p hg
    simpa only [d8115, d3305, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8114 p = 1 := by simpa only [d8115, d3305, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44575 p hg
    simpa only [d8115, d3305, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44577 (p : Pattern) (guard : d8086 p = 1) : d3226 p ≤ (0 : Int) + d323 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44345 p hg
    simpa only [d8086, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44361 p hg
    simpa only [d8086, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44578 (p : Pattern) (guard : d8091 p = 1) : d3226 p ≤ (0 : Int) + d324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44577 p hg
    simpa only [d8091, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44431 p hg
    simpa only [d8091, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44579 (p : Pattern) (guard : d8096 p = 1) : d3238 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d3238, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44578 p hg
    simpa only [d8096, d3238, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d3238, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44547 p hg
    simpa only [d8096, d3238, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44580 (p : Pattern) (guard : d1 p = 1) : d3250 p ≤ (0 : Int) + d329 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d3250, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34584 p hg
    simpa only [d3250, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d3250, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d3250, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44581 (p : Pattern) (guard : d8085 p = 1) : d3250 p ≤ (0 : Int) + d330 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44580 p hg
    simpa only [d8085, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44421 p hg
    simpa only [d8085, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44582 (p : Pattern) (guard : d8090 p = 1) : d3250 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44581 p hg
    simpa only [d8090, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44478 p hg
    simpa only [d8090, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44583 (p : Pattern) (guard : d8095 p = 1) : d3250 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44582 p hg
    simpa only [d8095, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44526 p hg
    simpa only [d8095, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44584 (p : Pattern) (guard : d8100 p = 1) : d3251 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44526 p hg
    simpa only [d8100, d3251, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d3251, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44585 (p : Pattern) (guard : d8101 p = 1) : d3275 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3275, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44583 p hg
    simpa only [d8101, d3275, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3275, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44584 p hg
    simpa only [d8101, d3275, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44586 (p : Pattern) (guard : d8102 p = 1) : d3306 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d3306, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44579 p hg
    simpa only [d8102, d3306, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d3306, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44585 p hg
    simpa only [d8102, d3306, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44587 (p : Pattern) (guard : d1 p = 1) : d3239 p ≤ (0 : Int) + d327 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d3239, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34592 p hg
    simpa only [d3239, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d3239, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d3239, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44588 (p : Pattern) (guard : d8085 p = 1) : d3239 p ≤ (0 : Int) + d332 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44587 p hg
    simpa only [d8085, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44378 p hg
    simpa only [d8085, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44589 (p : Pattern) (guard : d8090 p = 1) : d3239 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44588 p hg
    simpa only [d8090, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44382 p hg
    simpa only [d8090, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44590 (p : Pattern) (guard : d8095 p = 1) : d3239 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44589 p hg
    simpa only [d8095, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44452 p hg
    simpa only [d8095, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44591 (p : Pattern) (guard : d8101 p = 1) : d3241 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3241, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44590 p hg
    simpa only [d8101, d3241, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3241, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44551 p hg
    simpa only [d8101, d3241, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44592 (p : Pattern) (guard : d8105 p = 1) : d3245 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d3245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44530 p hg
    simpa only [d8105, d3245, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d3245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d3245, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44593 (p : Pattern) (guard : d8106 p = 1) : d3246 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44531 p hg
    simpa only [d8106, d3246, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44592 p hg
    simpa only [d8106, d3246, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44594 (p : Pattern) (guard : d8107 p = 1) : d3277 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3277, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44591 p hg
    simpa only [d8107, d3277, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3277, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44593 p hg
    simpa only [d8107, d3277, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44595 (p : Pattern) (guard : d8108 p = 1) : d3307 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d3307, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44586 p hg
    simpa only [d8108, d3307, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d3307, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44594 p hg
    simpa only [d8108, d3307, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44596 (p : Pattern) (guard : d8105 p = 1) : d3280 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d3280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44535 p hg
    simpa only [d8105, d3280, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d3280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d3280, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44597 (p : Pattern) (guard : d8106 p = 1) : d3281 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44536 p hg
    simpa only [d8106, d3281, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44596 p hg
    simpa only [d8106, d3281, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44598 (p : Pattern) (guard : d8107 p = 1) : d3282 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44552 p hg
    simpa only [d8107, d3282, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44597 p hg
    simpa only [d8107, d3282, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44599 (p : Pattern) (guard : d8105 p = 1) : d3258 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d3258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44539 p hg
    simpa only [d8105, d3258, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d3258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d3258, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44600 (p : Pattern) (guard : d8106 p = 1) : d3283 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44540 p hg
    simpa only [d8106, d3283, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44599 p hg
    simpa only [d8106, d3283, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44601 (p : Pattern) (guard : d8112 p = 1) : d3284 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44600 p hg
    simpa only [d8112, d3284, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34543 p hg
    simpa only [d8112, d3284, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44602 (p : Pattern) (guard : d8113 p = 1) : d3285 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d3285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44598 p hg
    simpa only [d8113, d3285, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d3285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44601 p hg
    simpa only [d8113, d3285, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44603 (p : Pattern) (guard : d8114 p = 1) : d3308 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d3308, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44595 p hg
    simpa only [d8114, d3308, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d3308, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44602 p hg
    simpa only [d8114, d3308, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44604 (p : Pattern) (guard : d8107 p = 1) : d3309 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44569 p hg
    simpa only [d8107, d3309, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34455 p hg
    simpa only [d8107, d3309, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44605 (p : Pattern) (guard : d8113 p = 1) : d3310 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d3310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44604 p hg
    simpa only [d8113, d3310, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d3310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34611 p hg
    simpa only [d8113, d3310, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44606 (p : Pattern) (guard : d8119 p = 1) : d3311 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d3311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44605 p hg
    simpa only [d8119, d3311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d3311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34613 p hg
    simpa only [d8119, d3311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44607 (p : Pattern) (guard : d8120 p = 1) : d3312 p ≤ (0 : Int) + d399 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d3312, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44603 p hg
    simpa only [d8120, d3312, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d3312, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44606 p hg
    simpa only [d8120, d3312, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44608 (p : Pattern) (guard : d8121 p = 1) : d3313 p ≤ (0 : Int) + d400 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8115 p = 1 := by simpa only [d8121, d3313, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44576 p hg
    simpa only [d8121, d3313, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8120 p = 1 := by simpa only [d8121, d3313, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44607 p hg
    simpa only [d8121, d3313, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44609 (p : Pattern) (guard : d8122 p = 1) : d3314 p ≤ (0 : Int) + d401 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8116 p = 1 := by simpa only [d8122, d3314, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44546 p hg
    simpa only [d8122, d3314, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8121 p = 1 := by simpa only [d8122, d3314, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44608 p hg
    simpa only [d8122, d3314, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44610 (p : Pattern) (guard : d8097 p = 1) : d3238 p ≤ (0 : Int) + d346 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8092 p = 1 := by simpa only [d8097, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44374 p hg
    simpa only [d8097, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8096 p = 1 := by simpa only [d8097, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44579 p hg
    simpa only [d8097, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44611 (p : Pattern) (guard : d8102 p = 1) : d3242 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d3242, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44548 p hg
    simpa only [d8102, d3242, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d3242, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44591 p hg
    simpa only [d8102, d3242, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44612 (p : Pattern) (guard : d8103 p = 1) : d3299 p ≤ (0 : Int) + d402 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8097 p = 1 := by simpa only [d8103, d3299, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44610 p hg
    simpa only [d8103, d3299, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8102 p = 1 := by simpa only [d8103, d3299, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44611 p hg
    simpa only [d8103, d3299, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44613 (p : Pattern) (guard : d8108 p = 1) : d3248 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d3248, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44553 p hg
    simpa only [d8108, d3248, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d3248, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44558 p hg
    simpa only [d8108, d3248, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44614 (p : Pattern) (guard : d8109 p = 1) : d3300 p ≤ (0 : Int) + d404 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8103 p = 1 := by simpa only [d8109, d3300, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44612 p hg
    simpa only [d8109, d3300, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8108 p = 1 := by simpa only [d8109, d3300, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44613 p hg
    simpa only [d8109, d3300, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44615 (p : Pattern) (guard : d1 p = 1) : d3250 p ≤ (0 : Int) + d330 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44580 p hg
    simpa only [d330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44420 p hg
    simpa only [d330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44616 (p : Pattern) (guard : d8086 p = 1) : d3250 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44615 p hg
    simpa only [d8086, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44422 p hg
    simpa only [d8086, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44617 (p : Pattern) (guard : d8091 p = 1) : d3250 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44616 p hg
    simpa only [d8091, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44479 p hg
    simpa only [d8091, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44618 (p : Pattern) (guard : d8096 p = 1) : d3275 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d3275, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44617 p hg
    simpa only [d8096, d3275, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d3275, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44481 p hg
    simpa only [d8096, d3275, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44619 (p : Pattern) (guard : d8102 p = 1) : d3302 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d3302, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44618 p hg
    simpa only [d8102, d3302, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d3302, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44569 p hg
    simpa only [d8102, d3302, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44620 (p : Pattern) (guard : d8108 p = 1) : d3303 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d3303, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44619 p hg
    simpa only [d8108, d3303, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d3303, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44573 p hg
    simpa only [d8108, d3303, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44621 (p : Pattern) (guard : d8114 p = 1) : d3304 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d3304, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44620 p hg
    simpa only [d8114, d3304, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d3304, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34577 p hg
    simpa only [d8114, d3304, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44622 (p : Pattern) (guard : d8115 p = 1) : d3305 p ≤ (0 : Int) + d406 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8109 p = 1 := by simpa only [d8115, d3305, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44614 p hg
    simpa only [d8115, d3305, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8114 p = 1 := by simpa only [d8115, d3305, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44621 p hg
    simpa only [d8115, d3305, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44623 (p : Pattern) (guard : d8086 p = 1) : d3226 p ≤ (0 : Int) + d366 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44417 p hg
    simpa only [d8086, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44361 p hg
    simpa only [d8086, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44624 (p : Pattern) (guard : d8091 p = 1) : d3226 p ≤ (0 : Int) + d367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44623 p hg
    simpa only [d8091, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44431 p hg
    simpa only [d8091, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44625 (p : Pattern) (guard : d8096 p = 1) : d3238 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d3238, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44624 p hg
    simpa only [d8096, d3238, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d3238, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44547 p hg
    simpa only [d8096, d3238, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44626 (p : Pattern) (guard : d1 p = 1) : d3250 p ≤ (0 : Int) + d356 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d3250, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34879 p hg
    simpa only [d3250, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d3250, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d3250, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44627 (p : Pattern) (guard : d8085 p = 1) : d3250 p ≤ (0 : Int) + d357 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44626 p hg
    simpa only [d8085, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44421 p hg
    simpa only [d8085, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44628 (p : Pattern) (guard : d8090 p = 1) : d3250 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44627 p hg
    simpa only [d8090, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44478 p hg
    simpa only [d8090, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44629 (p : Pattern) (guard : d8095 p = 1) : d3250 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44628 p hg
    simpa only [d8095, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44526 p hg
    simpa only [d8095, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44630 (p : Pattern) (guard : d8101 p = 1) : d3275 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3275, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44629 p hg
    simpa only [d8101, d3275, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3275, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44584 p hg
    simpa only [d8101, d3275, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44631 (p : Pattern) (guard : d8102 p = 1) : d3306 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d3306, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44625 p hg
    simpa only [d8102, d3306, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d3306, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44630 p hg
    simpa only [d8102, d3306, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44632 (p : Pattern) (guard : d1 p = 1) : d3239 p ≤ (0 : Int) + d329 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d3239, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34624 p hg
    simpa only [d3239, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d3239, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d3239, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44633 (p : Pattern) (guard : d8085 p = 1) : d3239 p ≤ (0 : Int) + d330 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44632 p hg
    simpa only [d8085, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44378 p hg
    simpa only [d8085, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44634 (p : Pattern) (guard : d8090 p = 1) : d3239 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44633 p hg
    simpa only [d8090, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44382 p hg
    simpa only [d8090, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44635 (p : Pattern) (guard : d8095 p = 1) : d3239 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44634 p hg
    simpa only [d8095, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44452 p hg
    simpa only [d8095, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44636 (p : Pattern) (guard : d8101 p = 1) : d3241 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3241, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44635 p hg
    simpa only [d8101, d3241, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3241, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44551 p hg
    simpa only [d8101, d3241, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44637 (p : Pattern) (guard : d8107 p = 1) : d3277 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3277, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44636 p hg
    simpa only [d8107, d3277, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3277, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44593 p hg
    simpa only [d8107, d3277, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44638 (p : Pattern) (guard : d8108 p = 1) : d3307 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d3307, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44631 p hg
    simpa only [d8108, d3307, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d3307, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44637 p hg
    simpa only [d8108, d3307, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44639 (p : Pattern) (guard : d8107 p = 1) : d3282 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3282, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44591 p hg
    simpa only [d8107, d3282, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3282, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44597 p hg
    simpa only [d8107, d3282, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44640 (p : Pattern) (guard : d8113 p = 1) : d3285 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d3285, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44639 p hg
    simpa only [d8113, d3285, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d3285, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44601 p hg
    simpa only [d8113, d3285, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44641 (p : Pattern) (guard : d8114 p = 1) : d3308 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d3308, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44638 p hg
    simpa only [d8114, d3308, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d3308, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44640 p hg
    simpa only [d8114, d3308, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44642 (p : Pattern) (guard : d8120 p = 1) : d3312 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d3312, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44641 p hg
    simpa only [d8120, d3312, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d3312, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44606 p hg
    simpa only [d8120, d3312, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44643 (p : Pattern) (guard : d8121 p = 1) : d3313 p ≤ (0 : Int) + d408 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8115 p = 1 := by simpa only [d8121, d3313, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44622 p hg
    simpa only [d8121, d3313, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8120 p = 1 := by simpa only [d8121, d3313, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44642 p hg
    simpa only [d8121, d3313, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44644 (p : Pattern) (guard : d8102 p = 1) : d3315 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d3315, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44412 p hg
    simpa only [d8102, d3315, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d3315, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44572 p hg
    simpa only [d8102, d3315, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44645 (p : Pattern) (guard : d8108 p = 1) : d3316 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d3316, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44644 p hg
    simpa only [d8108, d3316, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d3316, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44573 p hg
    simpa only [d8108, d3316, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44646 (p : Pattern) (guard : d8113 p = 1) : d3317 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d3317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44573 p hg
    simpa only [d8113, d3317, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d3317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34611 p hg
    simpa only [d8113, d3317, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44647 (p : Pattern) (guard : d8114 p = 1) : d3318 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d3318, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44645 p hg
    simpa only [d8114, d3318, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d3318, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44646 p hg
    simpa only [d8114, d3318, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44648 (p : Pattern) (guard : d8119 p = 1) : d3319 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d3319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44646 p hg
    simpa only [d8119, d3319, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d3319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34613 p hg
    simpa only [d8119, d3319, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44649 (p : Pattern) (guard : d8120 p = 1) : d3320 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d3320, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44647 p hg
    simpa only [d8120, d3320, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d3320, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44648 p hg
    simpa only [d8120, d3320, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44650 (p : Pattern) (guard : d8113 p = 1) : d3317 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d3317, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44516 p hg
    simpa only [d8113, d3317, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d3317, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34611 p hg
    simpa only [d8113, d3317, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44651 (p : Pattern) (guard : d8119 p = 1) : d3319 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d3319, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44650 p hg
    simpa only [d8119, d3319, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d3319, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34613 p hg
    simpa only [d8119, d3319, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44652 (p : Pattern) (guard : d8125 p = 1) : d3321 p ≤ (0 : Int) + d411 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d3321, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44651 p hg
    simpa only [d8125, d3321, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d3321, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36298 p hg
    simpa only [d8125, d3321, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44653 (p : Pattern) (guard : d8126 p = 1) : d3322 p ≤ (0 : Int) + d412 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d3322, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44649 p hg
    simpa only [d8126, d3322, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d3322, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44652 p hg
    simpa only [d8126, d3322, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44654 (p : Pattern) (guard : d8127 p = 1) : d3323 p ≤ (0 : Int) + d413 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8121 p = 1 := by simpa only [d8127, d3323, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44643 p hg
    simpa only [d8127, d3323, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8126 p = 1 := by simpa only [d8127, d3323, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44653 p hg
    simpa only [d8127, d3323, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44655 (p : Pattern) (guard : d8128 p = 1) : d3324 p ≤ (0 : Int) + d414 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8122 p = 1 := by simpa only [d8128, d3324, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44609 p hg
    simpa only [d8128, d3324, d414, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8127 p = 1 := by simpa only [d8128, d3324, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44654 p hg
    simpa only [d8128, d3324, d414, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44656 (p : Pattern) (guard : d8097 p = 1) : d3325 p ≤ (0 : Int) + d415 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8092 p = 1 := by simpa only [d8097, d3325, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44366 p hg
    simpa only [d8097, d3325, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8096 p = 1 := by simpa only [d8097, d3325, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44625 p hg
    simpa only [d8097, d3325, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44657 (p : Pattern) (guard : d8102 p = 1) : d3242 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d3242, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44579 p hg
    simpa only [d8102, d3242, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d3242, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44636 p hg
    simpa only [d8102, d3242, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44658 (p : Pattern) (guard : d8103 p = 1) : d3326 p ≤ (0 : Int) + d416 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8097 p = 1 := by simpa only [d8103, d3326, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44656 p hg
    simpa only [d8103, d3326, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8102 p = 1 := by simpa only [d8103, d3326, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44657 p hg
    simpa only [d8103, d3326, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44659 (p : Pattern) (guard : d8108 p = 1) : d3248 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d3248, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44611 p hg
    simpa only [d8108, d3248, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d3248, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44558 p hg
    simpa only [d8108, d3248, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
