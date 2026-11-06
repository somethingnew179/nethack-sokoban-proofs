/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons301
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare42280 (p : Pattern) (guard : d8107 p = 1) : d2556 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2556, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42279 p hg
    simpa only [d8107, d2556, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2556, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42124 p hg
    simpa only [d8107, d2556, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42281 (p : Pattern) (guard : d8108 p = 1) : d2557 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d2557, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42278 p hg
    simpa only [d8108, d2557, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d2557, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42280 p hg
    simpa only [d8108, d2557, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42282 (p : Pattern) (guard : d8114 p = 1) : d2563 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d2563, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42281 p hg
    simpa only [d8114, d2563, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d2563, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42130 p hg
    simpa only [d8114, d2563, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42283 (p : Pattern) (guard : d8115 p = 1) : d2660 p ≤ (0 : Int) + d437 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8109 p = 1 := by simpa only [d8115, d2660, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42275 p hg
    simpa only [d8115, d2660, d437, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8114 p = 1 := by simpa only [d8115, d2660, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42282 p hg
    simpa only [d8115, d2660, d437, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42284 (p : Pattern) (guard : d8086 p = 1) : d2514 p ≤ (0 : Int) + d331 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d2514, d331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41783 p hg
    simpa only [d8086, d2514, d331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d2514, d331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42207 p hg
    simpa only [d8086, d2514, d331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42285 (p : Pattern) (guard : d8090 p = 1) : d2507 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d2507, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42156 p hg
    simpa only [d8090, d2507, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d2507, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41853 p hg
    simpa only [d8090, d2507, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42286 (p : Pattern) (guard : d8091 p = 1) : d2515 p ≤ (0 : Int) + d334 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d2515, d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42284 p hg
    simpa only [d8091, d2515, d334, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d2515, d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42285 p hg
    simpa only [d8091, d2515, d334, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42287 (p : Pattern) (guard : d8090 p = 1) : d2510 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d2510, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42207 p hg
    simpa only [d8090, d2510, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d2510, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42092 p hg
    simpa only [d8090, d2510, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42288 (p : Pattern) (guard : d8095 p = 1) : d2511 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2511, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42287 p hg
    simpa only [d8095, d2511, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2511, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34367 p hg
    simpa only [d8095, d2511, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42289 (p : Pattern) (guard : d8096 p = 1) : d2516 p ≤ (0 : Int) + d337 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d2516, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42286 p hg
    simpa only [d8096, d2516, d337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d2516, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42288 p hg
    simpa only [d8096, d2516, d337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42290 (p : Pattern) (guard : d8085 p = 1) : d2540 p ≤ (0 : Int) + d365 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d2540, d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34784 p hg
    simpa only [d8085, d2540, d365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d2540, d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41787 p hg
    simpa only [d8085, d2540, d365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42291 (p : Pattern) (guard : d8090 p = 1) : d2540 p ≤ (0 : Int) + d366 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42290 p hg
    simpa only [d8090, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41946 p hg
    simpa only [d8090, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42292 (p : Pattern) (guard : d8095 p = 1) : d2569 p ≤ (0 : Int) + d367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2569, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42291 p hg
    simpa only [d8095, d2569, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2569, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41949 p hg
    simpa only [d8095, d2569, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42293 (p : Pattern) (guard : d8101 p = 1) : d2573 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2573, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42292 p hg
    simpa only [d8101, d2573, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2573, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42141 p hg
    simpa only [d8101, d2573, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42294 (p : Pattern) (guard : d8102 p = 1) : d2661 p ≤ (0 : Int) + d415 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d2661, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42289 p hg
    simpa only [d8102, d2661, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d2661, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42293 p hg
    simpa only [d8102, d2661, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42295 (p : Pattern) (guard : d8085 p = 1) : d2520 p ≤ (0 : Int) + d318 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d2520, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34356 p hg
    simpa only [d8085, d2520, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d2520, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41787 p hg
    simpa only [d8085, d2520, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42296 (p : Pattern) (guard : d8090 p = 1) : d2520 p ≤ (0 : Int) + d323 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42295 p hg
    simpa only [d8090, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41869 p hg
    simpa only [d8090, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42297 (p : Pattern) (guard : d8095 p = 1) : d2523 p ≤ (0 : Int) + d324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2523, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42296 p hg
    simpa only [d8095, d2523, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2523, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41872 p hg
    simpa only [d8095, d2523, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42298 (p : Pattern) (guard : d8101 p = 1) : d2527 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2527, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42297 p hg
    simpa only [d8101, d2527, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2527, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42100 p hg
    simpa only [d8101, d2527, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42299 (p : Pattern) (guard : d8089 p = 1) : d2530 p ≤ (0 : Int) + d330 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d2530, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34794 p hg
    simpa only [d8089, d2530, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d2530, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d8089, d2530, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42300 (p : Pattern) (guard : d8094 p = 1) : d2530 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42299 p hg
    simpa only [d8094, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41953 p hg
    simpa only [d8094, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42301 (p : Pattern) (guard : d8100 p = 1) : d2532 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2532, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42300 p hg
    simpa only [d8100, d2532, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2532, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41955 p hg
    simpa only [d8100, d2532, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42302 (p : Pattern) (guard : d8106 p = 1) : d2536 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2536, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42301 p hg
    simpa only [d8106, d2536, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2536, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42149 p hg
    simpa only [d8106, d2536, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42303 (p : Pattern) (guard : d8107 p = 1) : d2575 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2575, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42298 p hg
    simpa only [d8107, d2575, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2575, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42302 p hg
    simpa only [d8107, d2575, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42304 (p : Pattern) (guard : d8108 p = 1) : d2662 p ≤ (0 : Int) + d416 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d2662, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42294 p hg
    simpa only [d8108, d2662, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d2662, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42303 p hg
    simpa only [d8108, d2662, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42305 (p : Pattern) (guard : d8089 p = 1) : d2577 p ≤ (0 : Int) + d332 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d2577, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34802 p hg
    simpa only [d8089, d2577, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d2577, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d8089, d2577, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42306 (p : Pattern) (guard : d8094 p = 1) : d2577 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42305 p hg
    simpa only [d8094, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41960 p hg
    simpa only [d8094, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42307 (p : Pattern) (guard : d8100 p = 1) : d2579 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2579, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42306 p hg
    simpa only [d8100, d2579, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2579, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41962 p hg
    simpa only [d8100, d2579, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42308 (p : Pattern) (guard : d8106 p = 1) : d2581 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2581, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42307 p hg
    simpa only [d8106, d2581, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2581, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42030 p hg
    simpa only [d8106, d2581, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42309 (p : Pattern) (guard : d8107 p = 1) : d2582 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2582, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42265 p hg
    simpa only [d8107, d2582, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2582, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42308 p hg
    simpa only [d8107, d2582, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42310 (p : Pattern) (guard : d8113 p = 1) : d2586 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2586, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42309 p hg
    simpa only [d8113, d2586, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2586, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42035 p hg
    simpa only [d8113, d2586, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42311 (p : Pattern) (guard : d8114 p = 1) : d2663 p ≤ (0 : Int) + d417 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d2663, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42304 p hg
    simpa only [d8114, d2663, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d2663, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42310 p hg
    simpa only [d8114, d2663, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42312 (p : Pattern) (guard : d8101 p = 1) : d2549 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2549, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42239 p hg
    simpa only [d8101, d2549, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2549, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42003 p hg
    simpa only [d8101, d2549, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42313 (p : Pattern) (guard : d8107 p = 1) : d2589 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2589, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42312 p hg
    simpa only [d8107, d2589, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2589, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42164 p hg
    simpa only [d8107, d2589, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42314 (p : Pattern) (guard : d8113 p = 1) : d2591 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2591, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42313 p hg
    simpa only [d8113, d2591, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2591, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42169 p hg
    simpa only [d8113, d2591, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42315 (p : Pattern) (guard : d8119 p = 1) : d2597 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d2597, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42314 p hg
    simpa only [d8119, d2597, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d2597, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42179 p hg
    simpa only [d8119, d2597, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42316 (p : Pattern) (guard : d8120 p = 1) : d2664 p ≤ (0 : Int) + d418 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d2664, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42311 p hg
    simpa only [d8120, d2664, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d2664, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42315 p hg
    simpa only [d8120, d2664, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42317 (p : Pattern) (guard : d8121 p = 1) : d2665 p ≤ (0 : Int) + d438 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8115 p = 1 := by simpa only [d8121, d2665, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42283 p hg
    simpa only [d8121, d2665, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8120 p = 1 := by simpa only [d8121, d2665, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42316 p hg
    simpa only [d8121, d2665, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42318 (p : Pattern) (guard : d8102 p = 1) : d2601 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42061 p hg
    simpa only [d8102, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42240 p hg
    simpa only [d8102, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42319 (p : Pattern) (guard : d8107 p = 1) : d2604 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2604, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42210 p hg
    simpa only [d8107, d2604, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2604, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42188 p hg
    simpa only [d8107, d2604, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42320 (p : Pattern) (guard : d8108 p = 1) : d2605 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d2605, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42318 p hg
    simpa only [d8108, d2605, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d2605, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42319 p hg
    simpa only [d8108, d2605, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42321 (p : Pattern) (guard : d8113 p = 1) : d2609 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2609, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42233 p hg
    simpa only [d8113, d2609, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2609, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42191 p hg
    simpa only [d8113, d2609, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42322 (p : Pattern) (guard : d8114 p = 1) : d2610 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d2610, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42320 p hg
    simpa only [d8114, d2610, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d2610, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42321 p hg
    simpa only [d8114, d2610, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42323 (p : Pattern) (guard : d8120 p = 1) : d2617 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d2617, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42322 p hg
    simpa only [d8120, d2617, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d2617, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42205 p hg
    simpa only [d8120, d2617, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42324 (p : Pattern) (guard : d8085 p = 1) : d2504 p ≤ (0 : Int) + d320 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d2504, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34319 p hg
    simpa only [d8085, d2504, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d2504, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41787 p hg
    simpa only [d8085, d2504, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42325 (p : Pattern) (guard : d8090 p = 1) : d2504 p ≤ (0 : Int) + d321 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42324 p hg
    simpa only [d8090, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42112 p hg
    simpa only [d8090, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42326 (p : Pattern) (guard : d8095 p = 1) : d2518 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2518, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42325 p hg
    simpa only [d8095, d2518, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2518, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42115 p hg
    simpa only [d8095, d2518, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42327 (p : Pattern) (guard : d8101 p = 1) : d2601 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2601, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42326 p hg
    simpa only [d8101, d2601, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2601, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42183 p hg
    simpa only [d8101, d2601, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42328 (p : Pattern) (guard : d8089 p = 1) : d2540 p ≤ (0 : Int) + d332 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d2540, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34831 p hg
    simpa only [d8089, d2540, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d2540, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d8089, d2540, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42329 (p : Pattern) (guard : d8094 p = 1) : d2540 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42328 p hg
    simpa only [d8094, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42160 p hg
    simpa only [d8094, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42330 (p : Pattern) (guard : d8100 p = 1) : d2569 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2569, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42329 p hg
    simpa only [d8100, d2569, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2569, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42162 p hg
    simpa only [d8100, d2569, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42331 (p : Pattern) (guard : d8106 p = 1) : d2611 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2611, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42330 p hg
    simpa only [d8106, d2611, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2611, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42211 p hg
    simpa only [d8106, d2611, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42332 (p : Pattern) (guard : d8107 p = 1) : d2618 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2618, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42327 p hg
    simpa only [d8107, d2618, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2618, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42331 p hg
    simpa only [d8107, d2618, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42333 (p : Pattern) (guard : d8113 p = 1) : d2620 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2620, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42332 p hg
    simpa only [d8113, d2620, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2620, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42216 p hg
    simpa only [d8113, d2620, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42334 (p : Pattern) (guard : d8119 p = 1) : d2623 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d2623, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42333 p hg
    simpa only [d8119, d2623, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d2623, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42224 p hg
    simpa only [d8119, d2623, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42335 (p : Pattern) (guard : d8125 p = 1) : d2627 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d2627, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42334 p hg
    simpa only [d8125, d2627, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d2627, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42228 p hg
    simpa only [d8125, d2627, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42336 (p : Pattern) (guard : d8126 p = 1) : d2628 p ≤ (0 : Int) + d439 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d2628, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42323 p hg
    simpa only [d8126, d2628, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d2628, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42335 p hg
    simpa only [d8126, d2628, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42337 (p : Pattern) (guard : d8127 p = 1) : d2666 p ≤ (0 : Int) + d440 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8121 p = 1 := by simpa only [d8127, d2666, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42317 p hg
    simpa only [d8127, d2666, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8126 p = 1 := by simpa only [d8127, d2666, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42336 p hg
    simpa only [d8127, d2666, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42338 (p : Pattern) (guard : d8096 p = 1) : d2601 p ≤ (0 : Int) + d352 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d2601, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42134 p hg
    simpa only [d8096, d2601, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d2601, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41978 p hg
    simpa only [d8096, d2601, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42339 (p : Pattern) (guard : d8102 p = 1) : d2601 p ≤ (0 : Int) + d355 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42338 p hg
    simpa only [d8102, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42327 p hg
    simpa only [d8102, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42340 (p : Pattern) (guard : d8107 p = 1) : d2604 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2604, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42240 p hg
    simpa only [d8107, d2604, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2604, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42188 p hg
    simpa only [d8107, d2604, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42341 (p : Pattern) (guard : d8108 p = 1) : d2605 p ≤ (0 : Int) + d362 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d2605, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42339 p hg
    simpa only [d8108, d2605, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d2605, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42340 p hg
    simpa only [d8108, d2605, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42342 (p : Pattern) (guard : d8113 p = 1) : d2609 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2609, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42319 p hg
    simpa only [d8113, d2609, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2609, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42191 p hg
    simpa only [d8113, d2609, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42343 (p : Pattern) (guard : d8114 p = 1) : d2610 p ≤ (0 : Int) + d395 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d2610, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42341 p hg
    simpa only [d8114, d2610, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d2610, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42342 p hg
    simpa only [d8114, d2610, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42344 (p : Pattern) (guard : d8101 p = 1) : d2611 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2611, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41950 p hg
    simpa only [d8101, d2611, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2611, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42019 p hg
    simpa only [d8101, d2611, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42345 (p : Pattern) (guard : d8107 p = 1) : d2614 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2614, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42344 p hg
    simpa only [d8107, d2614, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2614, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42202 p hg
    simpa only [d8107, d2614, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42346 (p : Pattern) (guard : d8113 p = 1) : d2615 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2615, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42345 p hg
    simpa only [d8113, d2615, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2615, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42035 p hg
    simpa only [d8113, d2615, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42347 (p : Pattern) (guard : d8119 p = 1) : d2616 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d2616, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42346 p hg
    simpa only [d8119, d2616, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d2616, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34613 p hg
    simpa only [d8119, d2616, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42348 (p : Pattern) (guard : d8120 p = 1) : d2617 p ≤ (0 : Int) + d397 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d2617, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42343 p hg
    simpa only [d8120, d2617, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d2617, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42347 p hg
    simpa only [d8120, d2617, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42349 (p : Pattern) (guard : d8085 p = 1) : d2504 p ≤ (0 : Int) + d318 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d2504, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34321 p hg
    simpa only [d8085, d2504, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d2504, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41787 p hg
    simpa only [d8085, d2504, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42350 (p : Pattern) (guard : d8090 p = 1) : d2504 p ≤ (0 : Int) + d323 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42349 p hg
    simpa only [d8090, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42112 p hg
    simpa only [d8090, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42351 (p : Pattern) (guard : d8095 p = 1) : d2518 p ≤ (0 : Int) + d324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2518, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42350 p hg
    simpa only [d8095, d2518, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2518, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42115 p hg
    simpa only [d8095, d2518, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42352 (p : Pattern) (guard : d8101 p = 1) : d2601 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2601, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42351 p hg
    simpa only [d8101, d2601, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2601, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42183 p hg
    simpa only [d8101, d2601, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42353 (p : Pattern) (guard : d8089 p = 1) : d2540 p ≤ (0 : Int) + d330 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d2540, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35015 p hg
    simpa only [d8089, d2540, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d2540, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d8089, d2540, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42354 (p : Pattern) (guard : d8094 p = 1) : d2540 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42353 p hg
    simpa only [d8094, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42160 p hg
    simpa only [d8094, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42355 (p : Pattern) (guard : d8100 p = 1) : d2569 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2569, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42354 p hg
    simpa only [d8100, d2569, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2569, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42162 p hg
    simpa only [d8100, d2569, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42356 (p : Pattern) (guard : d8106 p = 1) : d2611 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2611, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42355 p hg
    simpa only [d8106, d2611, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2611, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42211 p hg
    simpa only [d8106, d2611, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42357 (p : Pattern) (guard : d8107 p = 1) : d2618 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2618, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42352 p hg
    simpa only [d8107, d2618, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2618, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42356 p hg
    simpa only [d8107, d2618, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42358 (p : Pattern) (guard : d8089 p = 1) : d2520 p ≤ (0 : Int) + d332 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d2520, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34849 p hg
    simpa only [d8089, d2520, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d2520, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d8089, d2520, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42359 (p : Pattern) (guard : d8094 p = 1) : d2520 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42358 p hg
    simpa only [d8094, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42120 p hg
    simpa only [d8094, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42360 (p : Pattern) (guard : d8100 p = 1) : d2523 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2523, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42359 p hg
    simpa only [d8100, d2523, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2523, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42122 p hg
    simpa only [d8100, d2523, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42361 (p : Pattern) (guard : d8106 p = 1) : d2603 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2603, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42360 p hg
    simpa only [d8106, d2603, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2603, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42187 p hg
    simpa only [d8106, d2603, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42362 (p : Pattern) (guard : d8112 p = 1) : d2619 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2619, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42361 p hg
    simpa only [d8112, d2619, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2619, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42215 p hg
    simpa only [d8112, d2619, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42363 (p : Pattern) (guard : d8113 p = 1) : d2620 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2620, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42357 p hg
    simpa only [d8113, d2620, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2620, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42362 p hg
    simpa only [d8113, d2620, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42364 (p : Pattern) (guard : d8119 p = 1) : d2623 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d2623, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42363 p hg
    simpa only [d8119, d2623, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d2623, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42224 p hg
    simpa only [d8119, d2623, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42365 (p : Pattern) (guard : d8125 p = 1) : d2627 p ≤ (0 : Int) + d399 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d2627, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42364 p hg
    simpa only [d8125, d2627, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d2627, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42228 p hg
    simpa only [d8125, d2627, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42366 (p : Pattern) (guard : d8126 p = 1) : d2628 p ≤ (0 : Int) + d400 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d2628, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42348 p hg
    simpa only [d8126, d2628, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d2628, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42365 p hg
    simpa only [d8126, d2628, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42367 (p : Pattern) (guard : d8101 p = 1) : d2607 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2607, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42271 p hg
    simpa only [d8101, d2607, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2607, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41988 p hg
    simpa only [d8101, d2607, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42368 (p : Pattern) (guard : d8107 p = 1) : d2630 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2630, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42367 p hg
    simpa only [d8107, d2630, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2630, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42034 p hg
    simpa only [d8107, d2630, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42369 (p : Pattern) (guard : d8113 p = 1) : d2631 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2631, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42368 p hg
    simpa only [d8113, d2631, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2631, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42035 p hg
    simpa only [d8113, d2631, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42370 (p : Pattern) (guard : d8118 p = 1) : d2632 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42035 p hg
    simpa only [d8118, d2632, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34734 p hg
    simpa only [d8118, d2632, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42371 (p : Pattern) (guard : d8119 p = 1) : d2633 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d2633, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42369 p hg
    simpa only [d8119, d2633, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d2633, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42370 p hg
    simpa only [d8119, d2633, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42372 (p : Pattern) (guard : d8124 p = 1) : d2634 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d2634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42370 p hg
    simpa only [d8124, d2634, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d2634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34736 p hg
    simpa only [d8124, d2634, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42373 (p : Pattern) (guard : d8125 p = 1) : d2635 p ≤ (0 : Int) + d421 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d2635, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42371 p hg
    simpa only [d8125, d2635, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d2635, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42372 p hg
    simpa only [d8125, d2635, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42374 (p : Pattern) (guard : d8130 p = 1) : d2636 p ≤ (0 : Int) + d12 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d2636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42372 p hg
    simpa only [d8130, d2636, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d2636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36647 p hg
    simpa only [d8130, d2636, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42375 (p : Pattern) (guard : d8131 p = 1) : d2637 p ≤ (0 : Int) + d441 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d2637, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42373 p hg
    simpa only [d8131, d2637, d441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d2637, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42374 p hg
    simpa only [d8131, d2637, d441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42376 (p : Pattern) (guard : d8132 p = 1) : d2638 p ≤ (0 : Int) + d442 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d2638, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42366 p hg
    simpa only [d8132, d2638, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d2638, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42375 p hg
    simpa only [d8132, d2638, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42377 (p : Pattern) (guard : d8133 p = 1) : d2667 p ≤ (0 : Int) + d443 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8127 p = 1 := by simpa only [d8133, d2667, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42337 p hg
    simpa only [d8133, d2667, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8132 p = 1 := by simpa only [d8133, d2667, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42376 p hg
    simpa only [d8133, d2667, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42378 (p : Pattern) (guard : d5854 p = 1) : d2509 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d2509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38631 p hg
    simpa only [d5854, d2509, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d2509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5854, d2509, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42379 (p : Pattern) (guard : d8094 p = 1) : d2510 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d2510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42112 p hg
    simpa only [d8094, d2510, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d2510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42378 p hg
    simpa only [d8094, d2510, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42380 (p : Pattern) (guard : d8100 p = 1) : d2511 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42379 p hg
    simpa only [d8100, d2511, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d2511, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42381 (p : Pattern) (guard : d8101 p = 1) : d2519 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2519, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42351 p hg
    simpa only [d8101, d2519, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2519, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42380 p hg
    simpa only [d8101, d2519, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42382 (p : Pattern) (guard : d8102 p = 1) : d2519 p ≤ (0 : Int) + d346 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42260 p hg
    simpa only [d8102, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42381 p hg
    simpa only [d8102, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42383 (p : Pattern) (guard : d8101 p = 1) : d2519 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2519, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42326 p hg
    simpa only [d8101, d2519, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2519, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42380 p hg
    simpa only [d8101, d2519, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42384 (p : Pattern) (guard : d8099 p = 1) : d2525 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d2525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42120 p hg
    simpa only [d8099, d2525, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d2525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21658 p hg
    simpa only [d8099, d2525, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42385 (p : Pattern) (guard : d8105 p = 1) : d2526 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d2526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42384 p hg
    simpa only [d8105, d2526, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d2526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d2526, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42386 (p : Pattern) (guard : d8106 p = 1) : d2527 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2527, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42360 p hg
    simpa only [d8106, d2527, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2527, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42385 p hg
    simpa only [d8106, d2527, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42387 (p : Pattern) (guard : d8107 p = 1) : d2528 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2528, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42383 p hg
    simpa only [d8107, d2528, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2528, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42386 p hg
    simpa only [d8107, d2528, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42388 (p : Pattern) (guard : d8108 p = 1) : d2668 p ≤ (0 : Int) + d402 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d2668, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42382 p hg
    simpa only [d8108, d2668, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d2668, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42387 p hg
    simpa only [d8108, d2668, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42389 (p : Pattern) (guard : d8101 p = 1) : d2519 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2519, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42239 p hg
    simpa only [d8101, d2519, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2519, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42380 p hg
    simpa only [d8101, d2519, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42390 (p : Pattern) (guard : d8106 p = 1) : d2527 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42123 p hg
    simpa only [d8106, d2527, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42385 p hg
    simpa only [d8106, d2527, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42391 (p : Pattern) (guard : d8107 p = 1) : d2528 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2528, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42389 p hg
    simpa only [d8107, d2528, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2528, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42390 p hg
    simpa only [d8107, d2528, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42392 (p : Pattern) (guard : d8112 p = 1) : d2537 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42150 p hg
    simpa only [d8112, d2537, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34543 p hg
    simpa only [d8112, d2537, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42393 (p : Pattern) (guard : d8113 p = 1) : d2538 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2538, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42391 p hg
    simpa only [d8113, d2538, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2538, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42392 p hg
    simpa only [d8113, d2538, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42394 (p : Pattern) (guard : d8114 p = 1) : d2669 p ≤ (0 : Int) + d404 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d2669, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42388 p hg
    simpa only [d8114, d2669, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d2669, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42393 p hg
    simpa only [d8114, d2669, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42395 (p : Pattern) (guard : d8101 p = 1) : d2544 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2544, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42209 p hg
    simpa only [d8101, d2544, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2544, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42019 p hg
    simpa only [d8101, d2544, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42396 (p : Pattern) (guard : d5854 p = 1) : d2504 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d2504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34416 p hg
    simpa only [d5854, d2504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d2504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5854, d2504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42397 (p : Pattern) (guard : d8094 p = 1) : d2504 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42112 p hg
    simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42396 p hg
    simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42398 (p : Pattern) (guard : d8099 p = 1) : d2507 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d2507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42396 p hg
    simpa only [d8099, d2507, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d2507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21637 p hg
    simpa only [d8099, d2507, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42399 (p : Pattern) (guard : d8100 p = 1) : d2518 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42397 p hg
    simpa only [d8100, d2518, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42398 p hg
    simpa only [d8100, d2518, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42400 (p : Pattern) (guard : d8106 p = 1) : d2549 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42399 p hg
    simpa only [d8106, d2549, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42201 p hg
    simpa only [d8106, d2549, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42401 (p : Pattern) (guard : d8107 p = 1) : d2550 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2550, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42395 p hg
    simpa only [d8107, d2550, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2550, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42400 p hg
    simpa only [d8107, d2550, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42402 (p : Pattern) (guard : d8106 p = 1) : d2554 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42399 p hg
    simpa only [d8106, d2554, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42033 p hg
    simpa only [d8106, d2554, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42403 (p : Pattern) (guard : d8099 p = 1) : d2520 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42120 p hg
    simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21653 p hg
    simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42404 (p : Pattern) (guard : d8105 p = 1) : d2523 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d2523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42403 p hg
    simpa only [d8105, d2523, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d2523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22564 p hg
    simpa only [d8105, d2523, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42405 (p : Pattern) (guard : d8111 p = 1) : d2555 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42404 p hg
    simpa only [d8111, d2555, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8111, d2555, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42406 (p : Pattern) (guard : d8112 p = 1) : d2556 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42402 p hg
    simpa only [d8112, d2556, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42405 p hg
    simpa only [d8112, d2556, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42407 (p : Pattern) (guard : d8113 p = 1) : d2557 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2557, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42401 p hg
    simpa only [d8113, d2557, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2557, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42406 p hg
    simpa only [d8113, d2557, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42408 (p : Pattern) (guard : d8106 p = 1) : d2558 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42399 p hg
    simpa only [d8106, d2558, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34532 p hg
    simpa only [d8106, d2558, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42409 (p : Pattern) (guard : d8112 p = 1) : d2559 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42408 p hg
    simpa only [d8112, d2559, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42405 p hg
    simpa only [d8112, d2559, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42410 (p : Pattern) (guard : d8117 p = 1) : d2561 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42168 p hg
    simpa only [d8117, d2561, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8117, d2561, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42411 (p : Pattern) (guard : d8118 p = 1) : d2562 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42409 p hg
    simpa only [d8118, d2562, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42410 p hg
    simpa only [d8118, d2562, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42412 (p : Pattern) (guard : d8119 p = 1) : d2563 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d2563, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42407 p hg
    simpa only [d8119, d2563, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d2563, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42411 p hg
    simpa only [d8119, d2563, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42413 (p : Pattern) (guard : d8120 p = 1) : d2670 p ≤ (0 : Int) + d406 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d2670, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42394 p hg
    simpa only [d8120, d2670, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d2670, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42412 p hg
    simpa only [d8120, d2670, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42414 (p : Pattern) (guard : d8085 p = 1) : d2504 p ≤ (0 : Int) + d365 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d2504, d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34403 p hg
    simpa only [d8085, d2504, d365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d2504, d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41787 p hg
    simpa only [d8085, d2504, d365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42415 (p : Pattern) (guard : d8090 p = 1) : d2504 p ≤ (0 : Int) + d366 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42414 p hg
    simpa only [d8090, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42112 p hg
    simpa only [d8090, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42416 (p : Pattern) (guard : d8095 p = 1) : d2518 p ≤ (0 : Int) + d367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2518, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42415 p hg
    simpa only [d8095, d2518, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2518, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42115 p hg
    simpa only [d8095, d2518, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42417 (p : Pattern) (guard : d8101 p = 1) : d2519 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2519, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42416 p hg
    simpa only [d8101, d2519, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2519, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42380 p hg
    simpa only [d8101, d2519, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42418 (p : Pattern) (guard : d8089 p = 1) : d2540 p ≤ (0 : Int) + d357 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d2540, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34880 p hg
    simpa only [d8089, d2540, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d2540, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d8089, d2540, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42419 (p : Pattern) (guard : d8094 p = 1) : d2540 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42418 p hg
    simpa only [d8094, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42160 p hg
    simpa only [d8094, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
