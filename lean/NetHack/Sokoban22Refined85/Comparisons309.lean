/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons308
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare43260 (p : Pattern) (guard : d8137 p = 1) : d2638 p ≤ (0 : Int) + d413 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d2638, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43250 p hg
    simpa only [d8137, d2638, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d2638, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43259 p hg
    simpa only [d8137, d2638, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43261 (p : Pattern) (guard : d8138 p = 1) : d2639 p ≤ (0 : Int) + d414 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8132 p = 1 := by simpa only [d8138, d2639, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43244 p hg
    simpa only [d8138, d2639, d414, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8137 p = 1 := by simpa only [d8138, d2639, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43260 p hg
    simpa only [d8138, d2639, d414, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43262 (p : Pattern) (guard : d8099 p = 1) : d2510 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d2510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42396 p hg
    simpa only [d8099, d2510, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d2510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21640 p hg
    simpa only [d8099, d2510, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43263 (p : Pattern) (guard : d8105 p = 1) : d2511 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d2511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43262 p hg
    simpa only [d8105, d2511, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d2511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d2511, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43264 (p : Pattern) (guard : d8106 p = 1) : d2519 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2519, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43122 p hg
    simpa only [d8106, d2519, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2519, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43263 p hg
    simpa only [d8106, d2519, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43265 (p : Pattern) (guard : d8107 p = 1) : d2640 p ≤ (0 : Int) + d415 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2640, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43015 p hg
    simpa only [d8107, d2640, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2640, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43264 p hg
    simpa only [d8107, d2640, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43266 (p : Pattern) (guard : d8106 p = 1) : d2519 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2519, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43076 p hg
    simpa only [d8106, d2519, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2519, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43263 p hg
    simpa only [d8106, d2519, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43267 (p : Pattern) (guard : d0 p = 1) : d2526 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare43268 (p : Pattern) (guard : d8111 p = 1) : d2527 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2527, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43131 p hg
    simpa only [d8111, d2527, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2527, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43267 p hg
    simpa only [d8111, d2527, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43269 (p : Pattern) (guard : d8112 p = 1) : d2528 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2528, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43266 p hg
    simpa only [d8112, d2528, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2528, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43268 p hg
    simpa only [d8112, d2528, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43270 (p : Pattern) (guard : d8113 p = 1) : d2641 p ≤ (0 : Int) + d416 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2641, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43265 p hg
    simpa only [d8113, d2641, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2641, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43269 p hg
    simpa only [d8113, d2641, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43271 (p : Pattern) (guard : d8106 p = 1) : d2519 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2519, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43052 p hg
    simpa only [d8106, d2519, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2519, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43263 p hg
    simpa only [d8106, d2519, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43272 (p : Pattern) (guard : d8111 p = 1) : d2527 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2527, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43085 p hg
    simpa only [d8111, d2527, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2527, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43267 p hg
    simpa only [d8111, d2527, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43273 (p : Pattern) (guard : d8112 p = 1) : d2528 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2528, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43271 p hg
    simpa only [d8112, d2528, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2528, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43272 p hg
    simpa only [d8112, d2528, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43274 (p : Pattern) (guard : d8117 p = 1) : d2537 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42430 p hg
    simpa only [d8117, d2537, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8117, d2537, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43275 (p : Pattern) (guard : d8118 p = 1) : d2538 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2538, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43273 p hg
    simpa only [d8118, d2538, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2538, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43274 p hg
    simpa only [d8118, d2538, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43276 (p : Pattern) (guard : d8119 p = 1) : d2642 p ≤ (0 : Int) + d417 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d2642, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43270 p hg
    simpa only [d8119, d2642, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d2642, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43275 p hg
    simpa only [d8119, d2642, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43277 (p : Pattern) (guard : d8106 p = 1) : d2544 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2544, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42643 p hg
    simpa only [d8106, d2544, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2544, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42211 p hg
    simpa only [d8106, d2544, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43278 (p : Pattern) (guard : d8111 p = 1) : d2549 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43147 p hg
    simpa only [d8111, d2549, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42462 p hg
    simpa only [d8111, d2549, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43279 (p : Pattern) (guard : d8112 p = 1) : d2550 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2550, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43277 p hg
    simpa only [d8112, d2550, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2550, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43278 p hg
    simpa only [d8112, d2550, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43280 (p : Pattern) (guard : d8111 p = 1) : d2554 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43147 p hg
    simpa only [d8111, d2554, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42221 p hg
    simpa only [d8111, d2554, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43281 (p : Pattern) (guard : d8117 p = 1) : d2556 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43280 p hg
    simpa only [d8117, d2556, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43138 p hg
    simpa only [d8117, d2556, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43282 (p : Pattern) (guard : d8118 p = 1) : d2557 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2557, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43279 p hg
    simpa only [d8118, d2557, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2557, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43281 p hg
    simpa only [d8118, d2557, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43283 (p : Pattern) (guard : d8111 p = 1) : d2558 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43147 p hg
    simpa only [d8111, d2558, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8111, d2558, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43284 (p : Pattern) (guard : d8117 p = 1) : d2559 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43283 p hg
    simpa only [d8117, d2559, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43138 p hg
    simpa only [d8117, d2559, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43285 (p : Pattern) (guard : d0 p = 1) : d2561 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare43286 (p : Pattern) (guard : d8123 p = 1) : d2562 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d2562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43284 p hg
    simpa only [d8123, d2562, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d2562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43285 p hg
    simpa only [d8123, d2562, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43287 (p : Pattern) (guard : d8124 p = 1) : d2563 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d2563, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43282 p hg
    simpa only [d8124, d2563, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d2563, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43286 p hg
    simpa only [d8124, d2563, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43288 (p : Pattern) (guard : d8125 p = 1) : d2643 p ≤ (0 : Int) + d418 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d2643, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43276 p hg
    simpa only [d8125, d2643, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d2643, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43287 p hg
    simpa only [d8125, d2643, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43289 (p : Pattern) (guard : d8089 p = 1) : d2504 p ≤ (0 : Int) + d349 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d2504, d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35649 p hg
    simpa only [d8089, d2504, d349, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d2504, d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d8089, d2504, d349, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43290 (p : Pattern) (guard : d8094 p = 1) : d2504 p ≤ (0 : Int) + d350 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43289 p hg
    simpa only [d8094, d350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42396 p hg
    simpa only [d8094, d350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43291 (p : Pattern) (guard : d8100 p = 1) : d2518 p ≤ (0 : Int) + d351 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2518, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43290 p hg
    simpa only [d8100, d2518, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2518, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42398 p hg
    simpa only [d8100, d2518, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43292 (p : Pattern) (guard : d8106 p = 1) : d2519 p ≤ (0 : Int) + d352 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2519, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43291 p hg
    simpa only [d8106, d2519, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2519, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43263 p hg
    simpa only [d8106, d2519, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43293 (p : Pattern) (guard : d5854 p = 1) : d2540 p ≤ (0 : Int) + d320 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d2540, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35655 p hg
    simpa only [d5854, d2540, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d2540, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5854, d2540, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43294 (p : Pattern) (guard : d8099 p = 1) : d2540 p ≤ (0 : Int) + d321 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43293 p hg
    simpa only [d8099, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21708 p hg
    simpa only [d8099, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43295 (p : Pattern) (guard : d8105 p = 1) : d2569 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d2569, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43294 p hg
    simpa only [d8105, d2569, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d2569, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22597 p hg
    simpa only [d8105, d2569, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43296 (p : Pattern) (guard : d0 p = 1) : d2572 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare43297 (p : Pattern) (guard : d8111 p = 1) : d2573 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2573, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43295 p hg
    simpa only [d8111, d2573, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2573, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43296 p hg
    simpa only [d8111, d2573, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43298 (p : Pattern) (guard : d8112 p = 1) : d2644 p ≤ (0 : Int) + d355 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2644, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43292 p hg
    simpa only [d8112, d2644, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2644, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43297 p hg
    simpa only [d8112, d2644, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43299 (p : Pattern) (guard : d5854 p = 1) : d2520 p ≤ (0 : Int) + d357 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d2520, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35662 p hg
    simpa only [d5854, d2520, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d2520, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5854, d2520, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43300 (p : Pattern) (guard : d8099 p = 1) : d2520 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43299 p hg
    simpa only [d8099, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21653 p hg
    simpa only [d8099, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43301 (p : Pattern) (guard : d8105 p = 1) : d2523 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d2523, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43300 p hg
    simpa only [d8105, d2523, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d2523, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22564 p hg
    simpa only [d8105, d2523, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43302 (p : Pattern) (guard : d8111 p = 1) : d2527 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2527, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43301 p hg
    simpa only [d8111, d2527, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2527, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43267 p hg
    simpa only [d8111, d2527, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43303 (p : Pattern) (guard : d0 p = 1) : d2536 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare43304 (p : Pattern) (guard : d8117 p = 1) : d2575 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2575, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43302 p hg
    simpa only [d8117, d2575, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2575, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43303 p hg
    simpa only [d8117, d2575, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43305 (p : Pattern) (guard : d8118 p = 1) : d2645 p ≤ (0 : Int) + d362 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2645, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43298 p hg
    simpa only [d8118, d2645, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2645, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43304 p hg
    simpa only [d8118, d2645, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43306 (p : Pattern) (guard : d8117 p = 1) : d2582 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2582, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43268 p hg
    simpa only [d8117, d2582, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2582, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42478 p hg
    simpa only [d8117, d2582, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43307 (p : Pattern) (guard : d8123 p = 1) : d2586 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d2586, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43306 p hg
    simpa only [d8123, d2586, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d2586, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42480 p hg
    simpa only [d8123, d2586, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43308 (p : Pattern) (guard : d8124 p = 1) : d2646 p ≤ (0 : Int) + d395 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d2646, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43305 p hg
    simpa only [d8124, d2646, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d2646, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43307 p hg
    simpa only [d8124, d2646, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43309 (p : Pattern) (guard : d8111 p = 1) : d2549 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2549, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43173 p hg
    simpa only [d8111, d2549, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2549, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42462 p hg
    simpa only [d8111, d2549, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43310 (p : Pattern) (guard : d0 p = 1) : d2588 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare43311 (p : Pattern) (guard : d8117 p = 1) : d2589 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2589, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43309 p hg
    simpa only [d8117, d2589, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2589, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43310 p hg
    simpa only [d8117, d2589, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43312 (p : Pattern) (guard : d0 p = 1) : d2590 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare43313 (p : Pattern) (guard : d8123 p = 1) : d2591 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d2591, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43311 p hg
    simpa only [d8123, d2591, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d2591, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43312 p hg
    simpa only [d8123, d2591, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43314 (p : Pattern) (guard : d0 p = 1) : d2596 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare43315 (p : Pattern) (guard : d8129 p = 1) : d2597 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d2597, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43313 p hg
    simpa only [d8129, d2597, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d2597, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43314 p hg
    simpa only [d8129, d2597, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43316 (p : Pattern) (guard : d8130 p = 1) : d2647 p ≤ (0 : Int) + d397 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d2647, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43308 p hg
    simpa only [d8130, d2647, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d2647, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43315 p hg
    simpa only [d8130, d2647, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43317 (p : Pattern) (guard : d8131 p = 1) : d2648 p ≤ (0 : Int) + d419 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d2648, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43288 p hg
    simpa only [d8131, d2648, d419, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d2648, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43316 p hg
    simpa only [d8131, d2648, d419, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43318 (p : Pattern) (guard : d0 p = 1) : d2603 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare43319 (p : Pattern) (guard : d8117 p = 1) : d2604 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43149 p hg
    simpa only [d8117, d2604, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43318 p hg
    simpa only [d8117, d2604, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43320 (p : Pattern) (guard : d8118 p = 1) : d2605 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2605, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43175 p hg
    simpa only [d8118, d2605, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2605, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43319 p hg
    simpa only [d8118, d2605, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43321 (p : Pattern) (guard : d0 p = 1) : d2608 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare43322 (p : Pattern) (guard : d8123 p = 1) : d2609 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d2609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43319 p hg
    simpa only [d8123, d2609, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d2609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43321 p hg
    simpa only [d8123, d2609, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43323 (p : Pattern) (guard : d8124 p = 1) : d2610 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d2610, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43320 p hg
    simpa only [d8124, d2610, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d2610, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43322 p hg
    simpa only [d8124, d2610, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43324 (p : Pattern) (guard : d8129 p = 1) : d2616 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d2616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43154 p hg
    simpa only [d8129, d2616, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d2616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8129, d2616, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43325 (p : Pattern) (guard : d8130 p = 1) : d2617 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d2617, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43323 p hg
    simpa only [d8130, d2617, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d2617, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43324 p hg
    simpa only [d8130, d2617, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43326 (p : Pattern) (guard : d5854 p = 1) : d2504 p ≤ (0 : Int) + d330 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d2504, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35682 p hg
    simpa only [d5854, d2504, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d2504, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5854, d2504, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43327 (p : Pattern) (guard : d8099 p = 1) : d2504 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43326 p hg
    simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21664 p hg
    simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43328 (p : Pattern) (guard : d8105 p = 1) : d2518 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d2518, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43327 p hg
    simpa only [d8105, d2518, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d2518, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22561 p hg
    simpa only [d8105, d2518, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43329 (p : Pattern) (guard : d8111 p = 1) : d2601 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2601, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43328 p hg
    simpa only [d8111, d2601, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2601, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43148 p hg
    simpa only [d8111, d2601, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43330 (p : Pattern) (guard : d8117 p = 1) : d2618 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2618, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43329 p hg
    simpa only [d8117, d2618, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2618, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43161 p hg
    simpa only [d8117, d2618, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43331 (p : Pattern) (guard : d0 p = 1) : d2619 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare43332 (p : Pattern) (guard : d8123 p = 1) : d2620 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d2620, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43330 p hg
    simpa only [d8123, d2620, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d2620, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43331 p hg
    simpa only [d8123, d2620, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43333 (p : Pattern) (guard : d0 p = 1) : d2622 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare43334 (p : Pattern) (guard : d8129 p = 1) : d2623 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d2623, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43332 p hg
    simpa only [d8129, d2623, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d2623, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43333 p hg
    simpa only [d8129, d2623, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43335 (p : Pattern) (guard : d0 p = 1) : d2626 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare43336 (p : Pattern) (guard : d8135 p = 1) : d2627 p ≤ (0 : Int) + d421 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d2627, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43334 p hg
    simpa only [d8135, d2627, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d2627, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43335 p hg
    simpa only [d8135, d2627, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43337 (p : Pattern) (guard : d8136 p = 1) : d2628 p ≤ (0 : Int) + d422 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d2628, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43325 p hg
    simpa only [d8136, d2628, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d2628, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43336 p hg
    simpa only [d8136, d2628, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43338 (p : Pattern) (guard : d8137 p = 1) : d2649 p ≤ (0 : Int) + d423 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d2649, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43317 p hg
    simpa only [d8137, d2649, d423, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d2649, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43337 p hg
    simpa only [d8137, d2649, d423, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43339 (p : Pattern) (guard : d8112 p = 1) : d2601 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43077 p hg
    simpa only [d8112, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43329 p hg
    simpa only [d8112, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43340 (p : Pattern) (guard : d8117 p = 1) : d2604 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2604, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43174 p hg
    simpa only [d8117, d2604, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2604, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43318 p hg
    simpa only [d8117, d2604, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43341 (p : Pattern) (guard : d8118 p = 1) : d2605 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2605, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43339 p hg
    simpa only [d8118, d2605, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2605, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43340 p hg
    simpa only [d8118, d2605, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43342 (p : Pattern) (guard : d8124 p = 1) : d2610 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d2610, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43341 p hg
    simpa only [d8124, d2610, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d2610, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43322 p hg
    simpa only [d8124, d2610, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43343 (p : Pattern) (guard : d8130 p = 1) : d2617 p ≤ (0 : Int) + d399 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d2617, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43342 p hg
    simpa only [d8130, d2617, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d2617, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43324 p hg
    simpa only [d8130, d2617, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43344 (p : Pattern) (guard : d5854 p = 1) : d2504 p ≤ (0 : Int) + d357 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d2504, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39763 p hg
    simpa only [d5854, d2504, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d2504, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5854, d2504, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43345 (p : Pattern) (guard : d8099 p = 1) : d2504 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43344 p hg
    simpa only [d8099, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21664 p hg
    simpa only [d8099, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43346 (p : Pattern) (guard : d8105 p = 1) : d2518 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d2518, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43345 p hg
    simpa only [d8105, d2518, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d2518, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22561 p hg
    simpa only [d8105, d2518, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43347 (p : Pattern) (guard : d8111 p = 1) : d2601 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2601, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43346 p hg
    simpa only [d8111, d2601, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2601, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43148 p hg
    simpa only [d8111, d2601, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43348 (p : Pattern) (guard : d8117 p = 1) : d2618 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2618, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43347 p hg
    simpa only [d8117, d2618, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2618, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43161 p hg
    simpa only [d8117, d2618, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43349 (p : Pattern) (guard : d8123 p = 1) : d2620 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d2620, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43348 p hg
    simpa only [d8123, d2620, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d2620, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43331 p hg
    simpa only [d8123, d2620, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43350 (p : Pattern) (guard : d8129 p = 1) : d2623 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d2623, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43349 p hg
    simpa only [d8129, d2623, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d2623, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43333 p hg
    simpa only [d8129, d2623, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43351 (p : Pattern) (guard : d8135 p = 1) : d2627 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d2627, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43350 p hg
    simpa only [d8135, d2627, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d2627, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43335 p hg
    simpa only [d8135, d2627, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43352 (p : Pattern) (guard : d8136 p = 1) : d2628 p ≤ (0 : Int) + d424 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d2628, d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43343 p hg
    simpa only [d8136, d2628, d424, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d2628, d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43351 p hg
    simpa only [d8136, d2628, d424, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43353 (p : Pattern) (guard : d8142 p = 1) : d2650 p ≤ (0 : Int) + d425 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8136 p = 1 := by simpa only [d8142, d2650, d425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43352 p hg
    simpa only [d8142, d2650, d425, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8141 p = 1 := by simpa only [d8142, d2650, d425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37397 p hg
    simpa only [d8142, d2650, d425, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43354 (p : Pattern) (guard : d8143 p = 1) : d2651 p ≤ (0 : Int) + d426 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8137 p = 1 := by simpa only [d8143, d2651, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43338 p hg
    simpa only [d8143, d2651, d426, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8142 p = 1 := by simpa only [d8143, d2651, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43353 p hg
    simpa only [d8143, d2651, d426, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43355 (p : Pattern) (guard : d8144 p = 1) : d2652 p ≤ (0 : Int) + d427 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8138 p = 1 := by simpa only [d8144, d2652, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43261 p hg
    simpa only [d8144, d2652, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8143 p = 1 := by simpa only [d8144, d2652, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43354 p hg
    simpa only [d8144, d2652, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43356 (p : Pattern) (guard : d8084 p = 1) : d356 p ≤ (0 : Int) + d356 p := by
  omega
theorem compare43357 (p : Pattern) (guard : d8085 p = 1) : d2676 p ≤ (0 : Int) + d430 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d2676, d430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35086 p hg
    simpa only [d8085, d2676, d430, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d2676, d430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43356 p hg
    simpa only [d8085, d2676, d430, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43358 (p : Pattern) (guard : d8090 p = 1) : d2678 p ≤ (0 : Int) + d431 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d2678, d431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43357 p hg
    simpa only [d8090, d2678, d431, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d2678, d431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42817 p hg
    simpa only [d8090, d2678, d431, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43359 (p : Pattern) (guard : d8094 p = 1) : d2680 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d2680, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42774 p hg
    simpa only [d8094, d2680, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d2680, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42670 p hg
    simpa only [d8094, d2680, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43360 (p : Pattern) (guard : d8095 p = 1) : d2681 p ≤ (0 : Int) + d432 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2681, d432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43358 p hg
    simpa only [d8095, d2681, d432, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2681, d432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43359 p hg
    simpa only [d8095, d2681, d432, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43361 (p : Pattern) (guard : d8094 p = 1) : d2683 p ≤ (0 : Int) + d321 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d2683, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42817 p hg
    simpa only [d8094, d2683, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d2683, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42673 p hg
    simpa only [d8094, d2683, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43362 (p : Pattern) (guard : d8100 p = 1) : d2684 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2684, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43361 p hg
    simpa only [d8100, d2684, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2684, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d2684, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43363 (p : Pattern) (guard : d8101 p = 1) : d2685 p ≤ (0 : Int) + d433 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2685, d433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43360 p hg
    simpa only [d8101, d2685, d433, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2685, d433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43362 p hg
    simpa only [d8101, d2685, d433, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43364 (p : Pattern) (guard : d8089 p = 1) : d2677 p ≤ (0 : Int) + d340 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d2677, d340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35701 p hg
    simpa only [d8089, d2677, d340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d2677, d340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d8089, d2677, d340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43365 (p : Pattern) (guard : d8094 p = 1) : d2677 p ≤ (0 : Int) + d341 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43364 p hg
    simpa only [d8094, d341, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42946 p hg
    simpa only [d8094, d341, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43366 (p : Pattern) (guard : d8100 p = 1) : d2686 p ≤ (0 : Int) + d342 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2686, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43365 p hg
    simpa only [d8100, d2686, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2686, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42717 p hg
    simpa only [d8100, d2686, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43367 (p : Pattern) (guard : d8099 p = 1) : d2683 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d2683, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42946 p hg
    simpa only [d8099, d2683, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d2683, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21836 p hg
    simpa only [d8099, d2683, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43368 (p : Pattern) (guard : d8105 p = 1) : d2684 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d2684, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43367 p hg
    simpa only [d8105, d2684, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d2684, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d2684, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43369 (p : Pattern) (guard : d8106 p = 1) : d2687 p ≤ (0 : Int) + d344 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2687, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43366 p hg
    simpa only [d8106, d2687, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2687, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43368 p hg
    simpa only [d8106, d2687, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43370 (p : Pattern) (guard : d8107 p = 1) : d2688 p ≤ (0 : Int) + d434 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2688, d434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43363 p hg
    simpa only [d8107, d2688, d434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2688, d434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43369 p hg
    simpa only [d8107, d2688, d434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43371 (p : Pattern) (guard : d8089 p = 1) : d2677 p ≤ (0 : Int) + d349 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d2677, d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35708 p hg
    simpa only [d8089, d2677, d349, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d2677, d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d8089, d2677, d349, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43372 (p : Pattern) (guard : d8094 p = 1) : d2677 p ≤ (0 : Int) + d350 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43371 p hg
    simpa only [d8094, d350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42715 p hg
    simpa only [d8094, d350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43373 (p : Pattern) (guard : d8100 p = 1) : d2686 p ≤ (0 : Int) + d351 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2686, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43372 p hg
    simpa only [d8100, d2686, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2686, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42717 p hg
    simpa only [d8100, d2686, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43374 (p : Pattern) (guard : d8106 p = 1) : d2687 p ≤ (0 : Int) + d352 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2687, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43373 p hg
    simpa only [d8106, d2687, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2687, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42878 p hg
    simpa only [d8106, d2687, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43375 (p : Pattern) (guard : d5854 p = 1) : d2689 p ≤ (0 : Int) + d320 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d2689, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35714 p hg
    simpa only [d5854, d2689, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d2689, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5854, d2689, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43376 (p : Pattern) (guard : d8099 p = 1) : d2689 p ≤ (0 : Int) + d321 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43375 p hg
    simpa only [d8099, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21849 p hg
    simpa only [d8099, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43377 (p : Pattern) (guard : d8105 p = 1) : d2692 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d2692, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43376 p hg
    simpa only [d8105, d2692, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d2692, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22716 p hg
    simpa only [d8105, d2692, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43378 (p : Pattern) (guard : d8111 p = 1) : d2696 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2696, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43377 p hg
    simpa only [d8111, d2696, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2696, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42882 p hg
    simpa only [d8111, d2696, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43379 (p : Pattern) (guard : d8112 p = 1) : d2697 p ≤ (0 : Int) + d355 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2697, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43374 p hg
    simpa only [d8112, d2697, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2697, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43378 p hg
    simpa only [d8112, d2697, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43380 (p : Pattern) (guard : d8113 p = 1) : d2698 p ≤ (0 : Int) + d435 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2698, d435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43370 p hg
    simpa only [d8113, d2698, d435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2698, d435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43379 p hg
    simpa only [d8113, d2698, d435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43381 (p : Pattern) (guard : d5854 p = 1) : d2689 p ≤ (0 : Int) + d357 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d2689, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35722 p hg
    simpa only [d5854, d2689, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d2689, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5854, d2689, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43382 (p : Pattern) (guard : d8099 p = 1) : d2689 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43381 p hg
    simpa only [d8099, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21849 p hg
    simpa only [d8099, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43383 (p : Pattern) (guard : d8105 p = 1) : d2692 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d2692, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43382 p hg
    simpa only [d8105, d2692, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d2692, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22716 p hg
    simpa only [d8105, d2692, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43384 (p : Pattern) (guard : d8111 p = 1) : d2696 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2696, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43383 p hg
    simpa only [d8111, d2696, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2696, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42882 p hg
    simpa only [d8111, d2696, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43385 (p : Pattern) (guard : d8112 p = 1) : d2697 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2697, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42907 p hg
    simpa only [d8112, d2697, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2697, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43384 p hg
    simpa only [d8112, d2697, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43386 (p : Pattern) (guard : d8117 p = 1) : d2699 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2699, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42764 p hg
    simpa only [d8117, d2699, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2699, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8117, d2699, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43387 (p : Pattern) (guard : d8118 p = 1) : d2700 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2700, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43385 p hg
    simpa only [d8118, d2700, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2700, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43386 p hg
    simpa only [d8118, d2700, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43388 (p : Pattern) (guard : d8119 p = 1) : d2701 p ≤ (0 : Int) + d436 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d2701, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43380 p hg
    simpa only [d8119, d2701, d436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d2701, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43387 p hg
    simpa only [d8119, d2701, d436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43389 (p : Pattern) (guard : d8106 p = 1) : d2706 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2706, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42855 p hg
    simpa only [d8106, d2706, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2706, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42807 p hg
    simpa only [d8106, d2706, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43390 (p : Pattern) (guard : d8111 p = 1) : d2711 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2711, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42966 p hg
    simpa only [d8111, d2711, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2711, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42811 p hg
    simpa only [d8111, d2711, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43391 (p : Pattern) (guard : d8112 p = 1) : d2712 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2712, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43389 p hg
    simpa only [d8112, d2712, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2712, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43390 p hg
    simpa only [d8112, d2712, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43392 (p : Pattern) (guard : d8111 p = 1) : d2713 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2713, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42948 p hg
    simpa only [d8111, d2713, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2713, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8111, d2713, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43393 (p : Pattern) (guard : d8117 p = 1) : d2715 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2715, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43392 p hg
    simpa only [d8117, d2715, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2715, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d8117, d2715, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43394 (p : Pattern) (guard : d8118 p = 1) : d2716 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2716, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43391 p hg
    simpa only [d8118, d2716, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2716, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43393 p hg
    simpa only [d8118, d2716, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43395 (p : Pattern) (guard : d8124 p = 1) : d2719 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d2719, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43394 p hg
    simpa only [d8124, d2719, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d2719, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42901 p hg
    simpa only [d8124, d2719, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43396 (p : Pattern) (guard : d8125 p = 1) : d2720 p ≤ (0 : Int) + d437 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d2720, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43388 p hg
    simpa only [d8125, d2720, d437, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d2720, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43395 p hg
    simpa only [d8125, d2720, d437, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43397 (p : Pattern) (guard : d5847 p = 1) : d327 p ≤ (0 : Int) + d327 p := by
  omega
theorem compare43398 (p : Pattern) (guard : d8089 p = 1) : d2721 p ≤ (0 : Int) + d328 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d2721, d328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35745 p hg
    simpa only [d8089, d2721, d328, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d2721, d328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43397 p hg
    simpa only [d8089, d2721, d328, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43399 (p : Pattern) (guard : d8094 p = 1) : d2722 p ≤ (0 : Int) + d331 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d2722, d331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43398 p hg
    simpa only [d8094, d2722, d331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d2722, d331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42964 p hg
    simpa only [d8094, d2722, d331, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
