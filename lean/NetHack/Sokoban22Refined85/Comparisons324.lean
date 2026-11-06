/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons323
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare45360 (p : Pattern) (guard : d5847 p = 1) : d3374 p ≤ (0 : Int) + d329 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3374, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39299 p hg
    simpa only [d5847, d3374, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3374, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5847, d3374, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45361 (p : Pattern) (guard : d5854 p = 1) : d3374 p ≤ (0 : Int) + d330 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45360 p hg
    simpa only [d5854, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26796 p hg
    simpa only [d5854, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45362 (p : Pattern) (guard : d8099 p = 1) : d3374 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45361 p hg
    simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26796 p hg
    simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45363 (p : Pattern) (guard : d8105 p = 1) : d3374 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45362 p hg
    simpa only [d8105, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26796 p hg
    simpa only [d8105, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45364 (p : Pattern) (guard : d8111 p = 1) : d3394 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3394, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45363 p hg
    simpa only [d8111, d3394, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3394, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45326 p hg
    simpa only [d8111, d3394, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45365 (p : Pattern) (guard : d8112 p = 1) : d3417 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3417, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45359 p hg
    simpa only [d8112, d3417, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3417, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45364 p hg
    simpa only [d8112, d3417, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45366 (p : Pattern) (guard : d5847 p = 1) : d3366 p ≤ (0 : Int) + d327 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3366, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35304 p hg
    simpa only [d5847, d3366, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3366, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5847, d3366, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45367 (p : Pattern) (guard : d5854 p = 1) : d3366 p ≤ (0 : Int) + d332 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45366 p hg
    simpa only [d5854, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26786 p hg
    simpa only [d5854, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45368 (p : Pattern) (guard : d8099 p = 1) : d3366 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45367 p hg
    simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26786 p hg
    simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45369 (p : Pattern) (guard : d8105 p = 1) : d3366 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45368 p hg
    simpa only [d8105, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26786 p hg
    simpa only [d8105, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45370 (p : Pattern) (guard : d8111 p = 1) : d3368 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3368, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45369 p hg
    simpa only [d8111, d3368, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3368, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45299 p hg
    simpa only [d8111, d3368, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45371 (p : Pattern) (guard : d8117 p = 1) : d3396 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3396, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45370 p hg
    simpa only [d8117, d3396, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3396, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44995 p hg
    simpa only [d8117, d3396, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45372 (p : Pattern) (guard : d8118 p = 1) : d3418 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3418, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45365 p hg
    simpa only [d8118, d3418, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3418, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45371 p hg
    simpa only [d8118, d3418, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45373 (p : Pattern) (guard : d8124 p = 1) : d3419 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d3419, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45372 p hg
    simpa only [d8124, d3419, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d3419, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45333 p hg
    simpa only [d8124, d3419, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45374 (p : Pattern) (guard : d8130 p = 1) : d3423 p ≤ (0 : Int) + d399 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d3423, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45373 p hg
    simpa only [d8130, d3423, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d3423, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45337 p hg
    simpa only [d8130, d3423, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45375 (p : Pattern) (guard : d8131 p = 1) : d3424 p ≤ (0 : Int) + d400 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d3424, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45354 p hg
    simpa only [d8131, d3424, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d3424, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45374 p hg
    simpa only [d8131, d3424, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45376 (p : Pattern) (guard : d8118 p = 1) : d3426 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3426, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45211 p hg
    simpa only [d8118, d3426, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3426, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34734 p hg
    simpa only [d8118, d3426, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45377 (p : Pattern) (guard : d8124 p = 1) : d3427 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d3427, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45376 p hg
    simpa only [d8124, d3427, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d3427, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34736 p hg
    simpa only [d8124, d3427, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45378 (p : Pattern) (guard : d8130 p = 1) : d3428 p ≤ (0 : Int) + d421 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d3428, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45377 p hg
    simpa only [d8130, d3428, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d3428, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36647 p hg
    simpa only [d8130, d3428, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45379 (p : Pattern) (guard : d8136 p = 1) : d3429 p ≤ (0 : Int) + d441 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d3429, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45378 p hg
    simpa only [d8136, d3429, d441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d3429, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37270 p hg
    simpa only [d8136, d3429, d441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45380 (p : Pattern) (guard : d8137 p = 1) : d3430 p ≤ (0 : Int) + d442 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d3430, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45375 p hg
    simpa only [d8137, d3430, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d3430, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45379 p hg
    simpa only [d8137, d3430, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45381 (p : Pattern) (guard : d8138 p = 1) : d3431 p ≤ (0 : Int) + d443 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8132 p = 1 := by simpa only [d8138, d3431, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45340 p hg
    simpa only [d8138, d3431, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8137 p = 1 := by simpa only [d8138, d3431, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45380 p hg
    simpa only [d8138, d3431, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45382 (p : Pattern) (guard : d8107 p = 1) : d3364 p ≤ (0 : Int) + d346 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45181 p hg
    simpa only [d8107, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45359 p hg
    simpa only [d8107, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45383 (p : Pattern) (guard : d8112 p = 1) : d3369 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3369, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45321 p hg
    simpa only [d8112, d3369, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3369, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45370 p hg
    simpa only [d8112, d3369, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45384 (p : Pattern) (guard : d8113 p = 1) : d3410 p ≤ (0 : Int) + d402 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d3410, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45382 p hg
    simpa only [d8113, d3410, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d3410, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45383 p hg
    simpa only [d8113, d3410, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45385 (p : Pattern) (guard : d8118 p = 1) : d3372 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3372, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45342 p hg
    simpa only [d8118, d3372, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3372, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45305 p hg
    simpa only [d8118, d3372, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45386 (p : Pattern) (guard : d8119 p = 1) : d3411 p ≤ (0 : Int) + d404 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d3411, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45384 p hg
    simpa only [d8119, d3411, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d3411, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45385 p hg
    simpa only [d8119, d3411, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45387 (p : Pattern) (guard : d8106 p = 1) : d3376 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3376, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45229 p hg
    simpa only [d8106, d3376, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3376, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45260 p hg
    simpa only [d8106, d3376, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45388 (p : Pattern) (guard : d8105 p = 1) : d3358 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45228 p hg
    simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26774 p hg
    simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45389 (p : Pattern) (guard : d8111 p = 1) : d3379 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45388 p hg
    simpa only [d8111, d3379, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45311 p hg
    simpa only [d8111, d3379, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45390 (p : Pattern) (guard : d8112 p = 1) : d3380 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3380, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45387 p hg
    simpa only [d8112, d3380, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3380, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45389 p hg
    simpa only [d8112, d3380, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45391 (p : Pattern) (guard : d8111 p = 1) : d3381 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45388 p hg
    simpa only [d8111, d3381, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8111, d3381, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45392 (p : Pattern) (guard : d0 p = 1) : d3382 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare45393 (p : Pattern) (guard : d8117 p = 1) : d3383 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45391 p hg
    simpa only [d8117, d3383, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45392 p hg
    simpa only [d8117, d3383, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45394 (p : Pattern) (guard : d8118 p = 1) : d3384 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3384, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45390 p hg
    simpa only [d8118, d3384, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3384, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45393 p hg
    simpa only [d8118, d3384, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45395 (p : Pattern) (guard : d0 p = 1) : d3385 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare45396 (p : Pattern) (guard : d8123 p = 1) : d3386 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d3386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45393 p hg
    simpa only [d8123, d3386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d3386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45395 p hg
    simpa only [d8123, d3386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45397 (p : Pattern) (guard : d8124 p = 1) : d3387 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d3387, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45394 p hg
    simpa only [d8124, d3387, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d3387, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45396 p hg
    simpa only [d8124, d3387, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45398 (p : Pattern) (guard : d8125 p = 1) : d3432 p ≤ (0 : Int) + d406 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d3432, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45386 p hg
    simpa only [d8125, d3432, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d3432, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45397 p hg
    simpa only [d8125, d3432, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45399 (p : Pattern) (guard : d8084 p = 1) : d3358 p ≤ (0 : Int) + d364 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d3358, d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35144 p hg
    simpa only [d8084, d3358, d364, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d3358, d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d8084, d3358, d364, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45400 (p : Pattern) (guard : d8089 p = 1) : d3358 p ≤ (0 : Int) + d365 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45399 p hg
    simpa only [d8089, d365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45164 p hg
    simpa only [d8089, d365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45401 (p : Pattern) (guard : d8094 p = 1) : d3358 p ≤ (0 : Int) + d366 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45400 p hg
    simpa only [d8094, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45176 p hg
    simpa only [d8094, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45402 (p : Pattern) (guard : d8100 p = 1) : d3358 p ≤ (0 : Int) + d367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45401 p hg
    simpa only [d8100, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45228 p hg
    simpa only [d8100, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45403 (p : Pattern) (guard : d8106 p = 1) : d3364 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3364, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45402 p hg
    simpa only [d8106, d3364, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3364, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45295 p hg
    simpa only [d8106, d3364, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45404 (p : Pattern) (guard : d5847 p = 1) : d3374 p ≤ (0 : Int) + d356 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3374, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35330 p hg
    simpa only [d5847, d3374, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3374, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5847, d3374, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45405 (p : Pattern) (guard : d5854 p = 1) : d3374 p ≤ (0 : Int) + d357 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45404 p hg
    simpa only [d5854, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26796 p hg
    simpa only [d5854, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45406 (p : Pattern) (guard : d8099 p = 1) : d3374 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45405 p hg
    simpa only [d8099, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26796 p hg
    simpa only [d8099, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45407 (p : Pattern) (guard : d8105 p = 1) : d3374 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45406 p hg
    simpa only [d8105, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26796 p hg
    simpa only [d8105, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45408 (p : Pattern) (guard : d8111 p = 1) : d3394 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3394, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45407 p hg
    simpa only [d8111, d3394, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3394, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45326 p hg
    simpa only [d8111, d3394, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45409 (p : Pattern) (guard : d8112 p = 1) : d3417 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3417, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45403 p hg
    simpa only [d8112, d3417, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3417, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45408 p hg
    simpa only [d8112, d3417, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45410 (p : Pattern) (guard : d5847 p = 1) : d3366 p ≤ (0 : Int) + d329 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3366, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35337 p hg
    simpa only [d5847, d3366, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3366, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5847, d3366, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45411 (p : Pattern) (guard : d5854 p = 1) : d3366 p ≤ (0 : Int) + d330 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45410 p hg
    simpa only [d5854, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26786 p hg
    simpa only [d5854, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45412 (p : Pattern) (guard : d8099 p = 1) : d3366 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45411 p hg
    simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26786 p hg
    simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45413 (p : Pattern) (guard : d8105 p = 1) : d3366 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45412 p hg
    simpa only [d8105, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26786 p hg
    simpa only [d8105, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45414 (p : Pattern) (guard : d8111 p = 1) : d3368 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3368, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45413 p hg
    simpa only [d8111, d3368, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3368, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45299 p hg
    simpa only [d8111, d3368, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45415 (p : Pattern) (guard : d8117 p = 1) : d3396 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3396, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45414 p hg
    simpa only [d8117, d3396, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3396, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44995 p hg
    simpa only [d8117, d3396, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45416 (p : Pattern) (guard : d8118 p = 1) : d3418 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3418, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45409 p hg
    simpa only [d8118, d3418, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3418, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45415 p hg
    simpa only [d8118, d3418, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45417 (p : Pattern) (guard : d8117 p = 1) : d3398 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3398, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45370 p hg
    simpa only [d8117, d3398, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3398, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45331 p hg
    simpa only [d8117, d3398, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45418 (p : Pattern) (guard : d8123 p = 1) : d3399 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d3399, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45417 p hg
    simpa only [d8123, d3399, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d3399, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d3399, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45419 (p : Pattern) (guard : d8124 p = 1) : d3419 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d3419, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45416 p hg
    simpa only [d8124, d3419, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d3419, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45418 p hg
    simpa only [d8124, d3419, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45420 (p : Pattern) (guard : d0 p = 1) : d3401 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare45421 (p : Pattern) (guard : d8117 p = 1) : d3402 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45389 p hg
    simpa only [d8117, d3402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45420 p hg
    simpa only [d8117, d3402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45422 (p : Pattern) (guard : d0 p = 1) : d3403 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare45423 (p : Pattern) (guard : d8123 p = 1) : d3404 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d3404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45421 p hg
    simpa only [d8123, d3404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d3404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45422 p hg
    simpa only [d8123, d3404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45424 (p : Pattern) (guard : d0 p = 1) : d3406 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare45425 (p : Pattern) (guard : d8129 p = 1) : d3407 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d3407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45423 p hg
    simpa only [d8129, d3407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d3407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45424 p hg
    simpa only [d8129, d3407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45426 (p : Pattern) (guard : d8130 p = 1) : d3433 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d3433, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45419 p hg
    simpa only [d8130, d3433, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d3433, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45425 p hg
    simpa only [d8130, d3433, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45427 (p : Pattern) (guard : d8131 p = 1) : d3434 p ≤ (0 : Int) + d408 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d3434, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45398 p hg
    simpa only [d8131, d3434, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d3434, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45426 p hg
    simpa only [d8131, d3434, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45428 (p : Pattern) (guard : d0 p = 1) : d3362 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare45429 (p : Pattern) (guard : d8111 p = 1) : d3364 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45388 p hg
    simpa only [d8111, d3364, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45428 p hg
    simpa only [d8111, d3364, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45430 (p : Pattern) (guard : d8112 p = 1) : d3364 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45296 p hg
    simpa only [d8112, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45429 p hg
    simpa only [d8112, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45431 (p : Pattern) (guard : d0 p = 1) : d3368 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare45432 (p : Pattern) (guard : d8117 p = 1) : d3369 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45429 p hg
    simpa only [d8117, d3369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45431 p hg
    simpa only [d8117, d3369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45433 (p : Pattern) (guard : d8118 p = 1) : d3410 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3410, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45430 p hg
    simpa only [d8118, d3410, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3410, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45432 p hg
    simpa only [d8118, d3410, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45434 (p : Pattern) (guard : d0 p = 1) : d3371 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare45435 (p : Pattern) (guard : d8123 p = 1) : d3372 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d3372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45432 p hg
    simpa only [d8123, d3372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d3372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45434 p hg
    simpa only [d8123, d3372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45436 (p : Pattern) (guard : d8124 p = 1) : d3411 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d3411, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45433 p hg
    simpa only [d8124, d3411, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d3411, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45435 p hg
    simpa only [d8124, d3411, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45437 (p : Pattern) (guard : d8111 p = 1) : d3394 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45284 p hg
    simpa only [d8111, d3394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45326 p hg
    simpa only [d8111, d3394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45438 (p : Pattern) (guard : d0 p = 1) : d3412 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare45439 (p : Pattern) (guard : d8117 p = 1) : d3413 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45437 p hg
    simpa only [d8117, d3413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45438 p hg
    simpa only [d8117, d3413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45440 (p : Pattern) (guard : d8123 p = 1) : d3414 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d3414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45439 p hg
    simpa only [d8123, d3414, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d3414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d3414, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45441 (p : Pattern) (guard : d8129 p = 1) : d3415 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d3415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45440 p hg
    simpa only [d8129, d3415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d3415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8129, d3415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45442 (p : Pattern) (guard : d8130 p = 1) : d3416 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d3416, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45436 p hg
    simpa only [d8130, d3416, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d3416, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45441 p hg
    simpa only [d8130, d3416, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45443 (p : Pattern) (guard : d5847 p = 1) : d3358 p ≤ (0 : Int) + d327 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3358, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35365 p hg
    simpa only [d5847, d3358, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3358, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5847, d3358, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45444 (p : Pattern) (guard : d5854 p = 1) : d3358 p ≤ (0 : Int) + d332 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45443 p hg
    simpa only [d5854, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26774 p hg
    simpa only [d5854, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45445 (p : Pattern) (guard : d8099 p = 1) : d3358 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45444 p hg
    simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26774 p hg
    simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45446 (p : Pattern) (guard : d8105 p = 1) : d3358 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45445 p hg
    simpa only [d8105, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26774 p hg
    simpa only [d8105, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45447 (p : Pattern) (guard : d8111 p = 1) : d3364 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3364, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45446 p hg
    simpa only [d8111, d3364, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3364, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45428 p hg
    simpa only [d8111, d3364, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45448 (p : Pattern) (guard : d0 p = 1) : d3394 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare45449 (p : Pattern) (guard : d8117 p = 1) : d3417 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3417, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45447 p hg
    simpa only [d8117, d3417, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3417, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45448 p hg
    simpa only [d8117, d3417, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45450 (p : Pattern) (guard : d0 p = 1) : d3396 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare45451 (p : Pattern) (guard : d8123 p = 1) : d3418 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d3418, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45449 p hg
    simpa only [d8123, d3418, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d3418, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45450 p hg
    simpa only [d8123, d3418, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45452 (p : Pattern) (guard : d0 p = 1) : d3399 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare45453 (p : Pattern) (guard : d8129 p = 1) : d3419 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d3419, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45451 p hg
    simpa only [d8129, d3419, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d3419, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45452 p hg
    simpa only [d8129, d3419, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45454 (p : Pattern) (guard : d0 p = 1) : d3422 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare45455 (p : Pattern) (guard : d8135 p = 1) : d3423 p ≤ (0 : Int) + d411 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d3423, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45453 p hg
    simpa only [d8135, d3423, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d3423, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45454 p hg
    simpa only [d8135, d3423, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45456 (p : Pattern) (guard : d8136 p = 1) : d3424 p ≤ (0 : Int) + d412 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d3424, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45442 p hg
    simpa only [d8136, d3424, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d3424, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45455 p hg
    simpa only [d8136, d3424, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45457 (p : Pattern) (guard : d8137 p = 1) : d3435 p ≤ (0 : Int) + d413 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d3435, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45427 p hg
    simpa only [d8137, d3435, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d3435, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45456 p hg
    simpa only [d8137, d3435, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45458 (p : Pattern) (guard : d8112 p = 1) : d3364 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45321 p hg
    simpa only [d8112, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45447 p hg
    simpa only [d8112, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45459 (p : Pattern) (guard : d8118 p = 1) : d3410 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3410, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45458 p hg
    simpa only [d8118, d3410, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3410, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45432 p hg
    simpa only [d8118, d3410, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45460 (p : Pattern) (guard : d8124 p = 1) : d3411 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d3411, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45459 p hg
    simpa only [d8124, d3411, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d3411, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45435 p hg
    simpa only [d8124, d3411, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45461 (p : Pattern) (guard : d8130 p = 1) : d3416 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d3416, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45460 p hg
    simpa only [d8130, d3416, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d3416, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45441 p hg
    simpa only [d8130, d3416, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45462 (p : Pattern) (guard : d5847 p = 1) : d3358 p ≤ (0 : Int) + d329 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3358, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35732 p hg
    simpa only [d5847, d3358, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3358, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5847, d3358, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45463 (p : Pattern) (guard : d5854 p = 1) : d3358 p ≤ (0 : Int) + d330 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45462 p hg
    simpa only [d5854, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26774 p hg
    simpa only [d5854, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45464 (p : Pattern) (guard : d8099 p = 1) : d3358 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45463 p hg
    simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26774 p hg
    simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45465 (p : Pattern) (guard : d8105 p = 1) : d3358 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45464 p hg
    simpa only [d8105, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26774 p hg
    simpa only [d8105, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45466 (p : Pattern) (guard : d8111 p = 1) : d3364 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3364, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45465 p hg
    simpa only [d8111, d3364, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3364, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45428 p hg
    simpa only [d8111, d3364, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45467 (p : Pattern) (guard : d8117 p = 1) : d3417 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3417, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45466 p hg
    simpa only [d8117, d3417, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3417, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45448 p hg
    simpa only [d8117, d3417, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45468 (p : Pattern) (guard : d8123 p = 1) : d3418 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d3418, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45467 p hg
    simpa only [d8123, d3418, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d3418, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45450 p hg
    simpa only [d8123, d3418, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45469 (p : Pattern) (guard : d8129 p = 1) : d3419 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d3419, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45468 p hg
    simpa only [d8129, d3419, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d3419, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45452 p hg
    simpa only [d8129, d3419, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45470 (p : Pattern) (guard : d8135 p = 1) : d3423 p ≤ (0 : Int) + d421 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d3423, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45469 p hg
    simpa only [d8135, d3423, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d3423, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45454 p hg
    simpa only [d8135, d3423, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45471 (p : Pattern) (guard : d8136 p = 1) : d3424 p ≤ (0 : Int) + d422 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d3424, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45461 p hg
    simpa only [d8136, d3424, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d3424, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45470 p hg
    simpa only [d8136, d3424, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45472 (p : Pattern) (guard : d8142 p = 1) : d3436 p ≤ (0 : Int) + d444 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8136 p = 1 := by simpa only [d8142, d3436, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45471 p hg
    simpa only [d8142, d3436, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8141 p = 1 := by simpa only [d8142, d3436, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37397 p hg
    simpa only [d8142, d3436, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45473 (p : Pattern) (guard : d8143 p = 1) : d3437 p ≤ (0 : Int) + d445 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8137 p = 1 := by simpa only [d8143, d3437, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45457 p hg
    simpa only [d8143, d3437, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8142 p = 1 := by simpa only [d8143, d3437, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45472 p hg
    simpa only [d8143, d3437, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45474 (p : Pattern) (guard : d8144 p = 1) : d3438 p ≤ (0 : Int) + d446 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8138 p = 1 := by simpa only [d8144, d3438, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45381 p hg
    simpa only [d8144, d3438, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8143 p = 1 := by simpa only [d8144, d3438, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45473 p hg
    simpa only [d8144, d3438, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45475 (p : Pattern) (guard : d8145 p = 1) : d3439 p ≤ (0 : Int) + d447 p := by
  cases selected : p 71 with
  | false =>
    have hg : d8139 p = 1 := by simpa only [d8145, d3439, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45155 p hg
    simpa only [d8145, d3439, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8144 p = 1 := by simpa only [d8145, d3439, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45474 p hg
    simpa only [d8145, d3439, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45476 (p : Pattern) (guard : d8146 p = 1) : d3440 p ≤ (0 : Int) + d447 p := by
  cases selected : p 49 with
  | false =>
    have hg : d8140 p = 1 := by simpa only [d8146, d3440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45023 p hg
    simpa only [d8146, d3440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8145 p = 1 := by simpa only [d8146, d3440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45475 p hg
    simpa only [d8146, d3440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45477 (p : Pattern) (guard : d8086 p = 1) : d3337 p ≤ (0 : Int) + d431 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d3337, d431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44784 p hg
    simpa only [d8086, d3337, d431, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d3337, d431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44858 p hg
    simpa only [d8086, d3337, d431, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45478 (p : Pattern) (guard : d8091 p = 1) : d3338 p ≤ (0 : Int) + d432 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d3338, d432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45477 p hg
    simpa only [d8091, d3338, d432, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d3338, d432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44772 p hg
    simpa only [d8091, d3338, d432, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45479 (p : Pattern) (guard : d8095 p = 1) : d3230 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d3230, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44859 p hg
    simpa only [d8095, d3230, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d3230, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34367 p hg
    simpa only [d8095, d3230, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45480 (p : Pattern) (guard : d8096 p = 1) : d3339 p ≤ (0 : Int) + d433 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d3339, d433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45478 p hg
    simpa only [d8096, d3339, d433, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d3339, d433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45479 p hg
    simpa only [d8096, d3339, d433, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45481 (p : Pattern) (guard : d8085 p = 1) : d3226 p ≤ (0 : Int) + d340 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44368 p hg
    simpa only [d8085, d340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44360 p hg
    simpa only [d8085, d340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45482 (p : Pattern) (guard : d8090 p = 1) : d3226 p ≤ (0 : Int) + d341 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45481 p hg
    simpa only [d8090, d341, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44985 p hg
    simpa only [d8090, d341, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45483 (p : Pattern) (guard : d8095 p = 1) : d3226 p ≤ (0 : Int) + d342 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45482 p hg
    simpa only [d8095, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44663 p hg
    simpa only [d8095, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45484 (p : Pattern) (guard : d8100 p = 1) : d3230 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3230, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44986 p hg
    simpa only [d8100, d3230, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3230, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d3230, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45485 (p : Pattern) (guard : d8101 p = 1) : d3238 p ≤ (0 : Int) + d344 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3238, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45483 p hg
    simpa only [d8101, d3238, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3238, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45484 p hg
    simpa only [d8101, d3238, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45486 (p : Pattern) (guard : d8102 p = 1) : d3340 p ≤ (0 : Int) + d434 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d3340, d434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45480 p hg
    simpa only [d8102, d3340, d434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d3340, d434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45485 p hg
    simpa only [d8102, d3340, d434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45487 (p : Pattern) (guard : d8084 p = 1) : d3239 p ≤ (0 : Int) + d315 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d3239, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34379 p hg
    simpa only [d8084, d3239, d315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d3239, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d8084, d3239, d315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45488 (p : Pattern) (guard : d8089 p = 1) : d3239 p ≤ (0 : Int) + d320 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45487 p hg
    simpa only [d8089, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44381 p hg
    simpa only [d8089, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45489 (p : Pattern) (guard : d8094 p = 1) : d3239 p ≤ (0 : Int) + d321 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45488 p hg
    simpa only [d8094, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44451 p hg
    simpa only [d8094, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45490 (p : Pattern) (guard : d8100 p = 1) : d3239 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45489 p hg
    simpa only [d8100, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44668 p hg
    simpa only [d8100, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45491 (p : Pattern) (guard : d8106 p = 1) : d3241 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3241, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45490 p hg
    simpa only [d8106, d3241, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3241, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44724 p hg
    simpa only [d8106, d3241, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45492 (p : Pattern) (guard : d8107 p = 1) : d3242 p ≤ (0 : Int) + d355 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3242, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45114 p hg
    simpa only [d8107, d3242, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3242, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45491 p hg
    simpa only [d8107, d3242, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45493 (p : Pattern) (guard : d8108 p = 1) : d3341 p ≤ (0 : Int) + d435 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d3341, d435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45486 p hg
    simpa only [d8108, d3341, d435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d3341, d435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45492 p hg
    simpa only [d8108, d3341, d435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45494 (p : Pattern) (guard : d8107 p = 1) : d3242 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3242, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44937 p hg
    simpa only [d8107, d3242, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3242, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45125 p hg
    simpa only [d8107, d3242, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45495 (p : Pattern) (guard : d8112 p = 1) : d3247 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3247, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44835 p hg
    simpa only [d8112, d3247, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3247, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34543 p hg
    simpa only [d8112, d3247, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45496 (p : Pattern) (guard : d8113 p = 1) : d3248 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d3248, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45494 p hg
    simpa only [d8113, d3248, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d3248, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45495 p hg
    simpa only [d8113, d3248, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45497 (p : Pattern) (guard : d8114 p = 1) : d3342 p ≤ (0 : Int) + d436 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d3342, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45493 p hg
    simpa only [d8114, d3342, d436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d3342, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45496 p hg
    simpa only [d8114, d3342, d436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45498 (p : Pattern) (guard : d8101 p = 1) : d3252 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3252, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44885 p hg
    simpa only [d8101, d3252, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3252, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44584 p hg
    simpa only [d8101, d3252, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45499 (p : Pattern) (guard : d8106 p = 1) : d3255 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3255, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45013 p hg
    simpa only [d8106, d3255, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3255, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44735 p hg
    simpa only [d8106, d3255, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
