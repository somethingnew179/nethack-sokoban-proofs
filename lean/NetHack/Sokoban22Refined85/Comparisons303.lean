/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons302
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare42420 (p : Pattern) (guard : d8100 p = 1) : d2569 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2569, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42419 p hg
    simpa only [d8100, d2569, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2569, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42162 p hg
    simpa only [d8100, d2569, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42421 (p : Pattern) (guard : d8099 p = 1) : d2571 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d2571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42160 p hg
    simpa only [d8099, d2571, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d2571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21711 p hg
    simpa only [d8099, d2571, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42422 (p : Pattern) (guard : d8105 p = 1) : d2572 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d2572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42421 p hg
    simpa only [d8105, d2572, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d2572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d2572, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42423 (p : Pattern) (guard : d8106 p = 1) : d2573 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2573, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42420 p hg
    simpa only [d8106, d2573, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2573, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42422 p hg
    simpa only [d8106, d2573, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42424 (p : Pattern) (guard : d8107 p = 1) : d2644 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2644, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42417 p hg
    simpa only [d8107, d2644, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2644, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42423 p hg
    simpa only [d8107, d2644, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42425 (p : Pattern) (guard : d8089 p = 1) : d2520 p ≤ (0 : Int) + d330 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d2520, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34886 p hg
    simpa only [d8089, d2520, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d2520, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d8089, d2520, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42426 (p : Pattern) (guard : d8094 p = 1) : d2520 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42425 p hg
    simpa only [d8094, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42120 p hg
    simpa only [d8094, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42427 (p : Pattern) (guard : d8100 p = 1) : d2523 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2523, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42426 p hg
    simpa only [d8100, d2523, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2523, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42122 p hg
    simpa only [d8100, d2523, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42428 (p : Pattern) (guard : d8106 p = 1) : d2527 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2527, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42427 p hg
    simpa only [d8106, d2527, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2527, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42385 p hg
    simpa only [d8106, d2527, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42429 (p : Pattern) (guard : d0 p = 1) : d2535 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42430 (p : Pattern) (guard : d8111 p = 1) : d2536 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42167 p hg
    simpa only [d8111, d2536, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42429 p hg
    simpa only [d8111, d2536, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42431 (p : Pattern) (guard : d8112 p = 1) : d2575 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2575, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42428 p hg
    simpa only [d8112, d2575, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2575, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42430 p hg
    simpa only [d8112, d2575, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42432 (p : Pattern) (guard : d8113 p = 1) : d2645 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2645, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42424 p hg
    simpa only [d8113, d2645, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2645, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42431 p hg
    simpa only [d8113, d2645, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42433 (p : Pattern) (guard : d8112 p = 1) : d2582 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2582, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42386 p hg
    simpa only [d8112, d2582, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2582, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42219 p hg
    simpa only [d8112, d2582, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42434 (p : Pattern) (guard : d8118 p = 1) : d2586 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2586, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42433 p hg
    simpa only [d8118, d2586, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2586, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42223 p hg
    simpa only [d8118, d2586, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42435 (p : Pattern) (guard : d8119 p = 1) : d2646 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d2646, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42432 p hg
    simpa only [d8119, d2646, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d2646, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42434 p hg
    simpa only [d8119, d2646, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42436 (p : Pattern) (guard : d8099 p = 1) : d2540 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42160 p hg
    simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21708 p hg
    simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42437 (p : Pattern) (guard : d8105 p = 1) : d2569 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d2569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42436 p hg
    simpa only [d8105, d2569, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d2569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22597 p hg
    simpa only [d8105, d2569, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42438 (p : Pattern) (guard : d8111 p = 1) : d2588 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42437 p hg
    simpa only [d8111, d2588, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8111, d2588, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42439 (p : Pattern) (guard : d8112 p = 1) : d2589 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42400 p hg
    simpa only [d8112, d2589, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42438 p hg
    simpa only [d8112, d2589, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42440 (p : Pattern) (guard : d0 p = 1) : d2560 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42441 (p : Pattern) (guard : d8117 p = 1) : d2590 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42405 p hg
    simpa only [d8117, d2590, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42440 p hg
    simpa only [d8117, d2590, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42442 (p : Pattern) (guard : d8118 p = 1) : d2591 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2591, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42439 p hg
    simpa only [d8118, d2591, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2591, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42441 p hg
    simpa only [d8118, d2591, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42443 (p : Pattern) (guard : d0 p = 1) : d2592 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42444 (p : Pattern) (guard : d8117 p = 1) : d2593 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42405 p hg
    simpa only [d8117, d2593, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42443 p hg
    simpa only [d8117, d2593, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42445 (p : Pattern) (guard : d0 p = 1) : d2595 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42446 (p : Pattern) (guard : d8123 p = 1) : d2596 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d2596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42444 p hg
    simpa only [d8123, d2596, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d2596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42445 p hg
    simpa only [d8123, d2596, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42447 (p : Pattern) (guard : d8124 p = 1) : d2597 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d2597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42442 p hg
    simpa only [d8124, d2597, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d2597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42446 p hg
    simpa only [d8124, d2597, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42448 (p : Pattern) (guard : d8125 p = 1) : d2647 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d2647, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42435 p hg
    simpa only [d8125, d2647, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d2647, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42447 p hg
    simpa only [d8125, d2647, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42449 (p : Pattern) (guard : d8126 p = 1) : d2671 p ≤ (0 : Int) + d408 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d2671, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42413 p hg
    simpa only [d8126, d2671, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d2671, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42448 p hg
    simpa only [d8126, d2671, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42450 (p : Pattern) (guard : d8105 p = 1) : d2600 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d2600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42398 p hg
    simpa only [d8105, d2600, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d2600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d2600, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42451 (p : Pattern) (guard : d8106 p = 1) : d2601 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42399 p hg
    simpa only [d8106, d2601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42450 p hg
    simpa only [d8106, d2601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42452 (p : Pattern) (guard : d8107 p = 1) : d2601 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42240 p hg
    simpa only [d8107, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42451 p hg
    simpa only [d8107, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42453 (p : Pattern) (guard : d0 p = 1) : d2602 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42454 (p : Pattern) (guard : d8111 p = 1) : d2603 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42404 p hg
    simpa only [d8111, d2603, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42453 p hg
    simpa only [d8111, d2603, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42455 (p : Pattern) (guard : d8112 p = 1) : d2604 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42451 p hg
    simpa only [d8112, d2604, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42454 p hg
    simpa only [d8112, d2604, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42456 (p : Pattern) (guard : d8113 p = 1) : d2605 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2605, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42452 p hg
    simpa only [d8113, d2605, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2605, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42455 p hg
    simpa only [d8113, d2605, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42457 (p : Pattern) (guard : d8117 p = 1) : d2608 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42215 p hg
    simpa only [d8117, d2608, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8117, d2608, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42458 (p : Pattern) (guard : d8118 p = 1) : d2609 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42455 p hg
    simpa only [d8118, d2609, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42457 p hg
    simpa only [d8118, d2609, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42459 (p : Pattern) (guard : d8119 p = 1) : d2610 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d2610, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42456 p hg
    simpa only [d8119, d2610, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d2610, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42458 p hg
    simpa only [d8119, d2610, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42460 (p : Pattern) (guard : d8099 p = 1) : d2545 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42197 p hg
    simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21757 p hg
    simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42461 (p : Pattern) (guard : d8105 p = 1) : d2612 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d2612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42460 p hg
    simpa only [d8105, d2612, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d2612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22644 p hg
    simpa only [d8105, d2612, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42462 (p : Pattern) (guard : d0 p = 1) : d2548 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42463 (p : Pattern) (guard : d8111 p = 1) : d2613 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42461 p hg
    simpa only [d8111, d2613, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42462 p hg
    simpa only [d8111, d2613, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42464 (p : Pattern) (guard : d8112 p = 1) : d2614 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42212 p hg
    simpa only [d8112, d2614, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42463 p hg
    simpa only [d8112, d2614, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42465 (p : Pattern) (guard : d8118 p = 1) : d2615 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42464 p hg
    simpa only [d8118, d2615, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42223 p hg
    simpa only [d8118, d2615, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42466 (p : Pattern) (guard : d8124 p = 1) : d2616 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d2616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42465 p hg
    simpa only [d8124, d2616, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d2616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34736 p hg
    simpa only [d8124, d2616, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42467 (p : Pattern) (guard : d8125 p = 1) : d2617 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d2617, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42459 p hg
    simpa only [d8125, d2617, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d2617, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42466 p hg
    simpa only [d8125, d2617, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42468 (p : Pattern) (guard : d8089 p = 1) : d2504 p ≤ (0 : Int) + d332 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d2504, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34923 p hg
    simpa only [d8089, d2504, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d2504, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d8089, d2504, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42469 (p : Pattern) (guard : d8094 p = 1) : d2504 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42468 p hg
    simpa only [d8094, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42396 p hg
    simpa only [d8094, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42470 (p : Pattern) (guard : d8100 p = 1) : d2518 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2518, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42469 p hg
    simpa only [d8100, d2518, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2518, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42398 p hg
    simpa only [d8100, d2518, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42471 (p : Pattern) (guard : d8106 p = 1) : d2601 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2601, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42470 p hg
    simpa only [d8106, d2601, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2601, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42450 p hg
    simpa only [d8106, d2601, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42472 (p : Pattern) (guard : d0 p = 1) : d2543 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42473 (p : Pattern) (guard : d8111 p = 1) : d2611 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42437 p hg
    simpa only [d8111, d2611, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42472 p hg
    simpa only [d8111, d2611, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42474 (p : Pattern) (guard : d8112 p = 1) : d2618 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2618, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42471 p hg
    simpa only [d8112, d2618, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2618, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42473 p hg
    simpa only [d8112, d2618, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42475 (p : Pattern) (guard : d0 p = 1) : d2607 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42476 (p : Pattern) (guard : d8117 p = 1) : d2619 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42454 p hg
    simpa only [d8117, d2619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42475 p hg
    simpa only [d8117, d2619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42477 (p : Pattern) (guard : d8118 p = 1) : d2620 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2620, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42474 p hg
    simpa only [d8118, d2620, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2620, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42476 p hg
    simpa only [d8118, d2620, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42478 (p : Pattern) (guard : d0 p = 1) : d2581 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42479 (p : Pattern) (guard : d8117 p = 1) : d2621 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42454 p hg
    simpa only [d8117, d2621, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42478 p hg
    simpa only [d8117, d2621, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42480 (p : Pattern) (guard : d0 p = 1) : d2585 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42481 (p : Pattern) (guard : d8123 p = 1) : d2622 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d2622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42479 p hg
    simpa only [d8123, d2622, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d2622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42480 p hg
    simpa only [d8123, d2622, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42482 (p : Pattern) (guard : d8124 p = 1) : d2623 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d2623, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42477 p hg
    simpa only [d8124, d2623, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d2623, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42481 p hg
    simpa only [d8124, d2623, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42483 (p : Pattern) (guard : d8117 p = 1) : d2624 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42463 p hg
    simpa only [d8117, d2624, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8117, d2624, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42484 (p : Pattern) (guard : d8123 p = 1) : d2625 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d2625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42483 p hg
    simpa only [d8123, d2625, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d2625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d2625, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42485 (p : Pattern) (guard : d8129 p = 1) : d2626 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d2626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42484 p hg
    simpa only [d8129, d2626, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d2626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8129, d2626, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42486 (p : Pattern) (guard : d8130 p = 1) : d2627 p ≤ (0 : Int) + d411 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d2627, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42482 p hg
    simpa only [d8130, d2627, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d2627, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42485 p hg
    simpa only [d8130, d2627, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42487 (p : Pattern) (guard : d8131 p = 1) : d2628 p ≤ (0 : Int) + d412 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d2628, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42467 p hg
    simpa only [d8131, d2628, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d2628, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42486 p hg
    simpa only [d8131, d2628, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42488 (p : Pattern) (guard : d8132 p = 1) : d2672 p ≤ (0 : Int) + d413 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d2672, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42449 p hg
    simpa only [d8132, d2672, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d2672, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42487 p hg
    simpa only [d8132, d2672, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42489 (p : Pattern) (guard : d8107 p = 1) : d2601 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42327 p hg
    simpa only [d8107, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42471 p hg
    simpa only [d8107, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42490 (p : Pattern) (guard : d8113 p = 1) : d2605 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2605, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42489 p hg
    simpa only [d8113, d2605, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2605, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42455 p hg
    simpa only [d8113, d2605, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42491 (p : Pattern) (guard : d8119 p = 1) : d2610 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d2610, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42490 p hg
    simpa only [d8119, d2610, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d2610, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42458 p hg
    simpa only [d8119, d2610, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42492 (p : Pattern) (guard : d8125 p = 1) : d2617 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d2617, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42491 p hg
    simpa only [d8125, d2617, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d2617, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42466 p hg
    simpa only [d8125, d2617, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42493 (p : Pattern) (guard : d8089 p = 1) : d2504 p ≤ (0 : Int) + d330 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d2504, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35069 p hg
    simpa only [d8089, d2504, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d2504, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d8089, d2504, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42494 (p : Pattern) (guard : d8094 p = 1) : d2504 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42493 p hg
    simpa only [d8094, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42396 p hg
    simpa only [d8094, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42495 (p : Pattern) (guard : d8100 p = 1) : d2518 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2518, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42494 p hg
    simpa only [d8100, d2518, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2518, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42398 p hg
    simpa only [d8100, d2518, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42496 (p : Pattern) (guard : d8106 p = 1) : d2601 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2601, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42495 p hg
    simpa only [d8106, d2601, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2601, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42450 p hg
    simpa only [d8106, d2601, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42497 (p : Pattern) (guard : d8112 p = 1) : d2618 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2618, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42496 p hg
    simpa only [d8112, d2618, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2618, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42473 p hg
    simpa only [d8112, d2618, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42498 (p : Pattern) (guard : d8118 p = 1) : d2620 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2620, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42497 p hg
    simpa only [d8118, d2620, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2620, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42476 p hg
    simpa only [d8118, d2620, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42499 (p : Pattern) (guard : d8124 p = 1) : d2623 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d2623, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42498 p hg
    simpa only [d8124, d2623, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d2623, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42481 p hg
    simpa only [d8124, d2623, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42500 (p : Pattern) (guard : d8130 p = 1) : d2627 p ≤ (0 : Int) + d421 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d2627, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42499 p hg
    simpa only [d8130, d2627, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d2627, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42485 p hg
    simpa only [d8130, d2627, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42501 (p : Pattern) (guard : d8131 p = 1) : d2628 p ≤ (0 : Int) + d422 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d2628, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42492 p hg
    simpa only [d8131, d2628, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d2628, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42500 p hg
    simpa only [d8131, d2628, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42502 (p : Pattern) (guard : d8137 p = 1) : d2650 p ≤ (0 : Int) + d444 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d2650, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42501 p hg
    simpa only [d8137, d2650, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d2650, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36809 p hg
    simpa only [d8137, d2650, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42503 (p : Pattern) (guard : d8138 p = 1) : d2673 p ≤ (0 : Int) + d445 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8132 p = 1 := by simpa only [d8138, d2673, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42488 p hg
    simpa only [d8138, d2673, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8137 p = 1 := by simpa only [d8138, d2673, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42502 p hg
    simpa only [d8138, d2673, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42504 (p : Pattern) (guard : d8139 p = 1) : d2674 p ≤ (0 : Int) + d446 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8133 p = 1 := by simpa only [d8139, d2674, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42377 p hg
    simpa only [d8139, d2674, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8138 p = 1 := by simpa only [d8139, d2674, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42503 p hg
    simpa only [d8139, d2674, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42505 (p : Pattern) (guard : d8140 p = 1) : d2675 p ≤ (0 : Int) + d447 p := by
  cases selected : p 71 with
  | false =>
    have hg : d8134 p = 1 := by simpa only [d8140, d2675, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42248 p hg
    simpa only [d8140, d2675, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8139 p = 1 := by simpa only [d8140, d2675, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42504 p hg
    simpa only [d8140, d2675, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42506 (p : Pattern) (guard : d8086 p = 1) : d2507 p ≤ (0 : Int) + d321 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d2507, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41775 p hg
    simpa only [d8086, d2507, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d2507, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41788 p hg
    simpa only [d8086, d2507, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42507 (p : Pattern) (guard : d8087 p = 1) : d2508 p ≤ (0 : Int) + d322 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8087, d2508, d322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41774 p hg
    simpa only [d8087, d2508, d322, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8086 p = 1 := by simpa only [d8087, d2508, d322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42506 p hg
    simpa only [d8087, d2508, d322, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42508 (p : Pattern) (guard : d8086 p = 1) : d2510 p ≤ (0 : Int) + d323 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d2510, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41773 p hg
    simpa only [d8086, d2510, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d2510, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41791 p hg
    simpa only [d8086, d2510, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42509 (p : Pattern) (guard : d8091 p = 1) : d2511 p ≤ (0 : Int) + d324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d2511, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42508 p hg
    simpa only [d8091, d2511, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d2511, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34344 p hg
    simpa only [d8091, d2511, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42510 (p : Pattern) (guard : d8092 p = 1) : d2512 p ≤ (0 : Int) + d325 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8087 p = 1 := by simpa only [d8092, d2512, d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42507 p hg
    simpa only [d8092, d2512, d325, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8091 p = 1 := by simpa only [d8092, d2512, d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42509 p hg
    simpa only [d8092, d2512, d325, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42511 (p : Pattern) (guard : d8097 p = 1) : d2517 p ≤ (0 : Int) + d338 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8092 p = 1 := by simpa only [d8097, d2517, d338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42510 p hg
    simpa only [d8097, d2517, d338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8096 p = 1 := by simpa only [d8097, d2517, d338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42289 p hg
    simpa only [d8097, d2517, d338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42512 (p : Pattern) (guard : d8102 p = 1) : d2528 p ≤ (0 : Int) + d346 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d2528, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42260 p hg
    simpa only [d8102, d2528, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d2528, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42298 p hg
    simpa only [d8102, d2528, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42513 (p : Pattern) (guard : d8103 p = 1) : d2529 p ≤ (0 : Int) + d347 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8097 p = 1 := by simpa only [d8103, d2529, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42511 p hg
    simpa only [d8103, d2529, d347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8102 p = 1 := by simpa only [d8103, d2529, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42512 p hg
    simpa only [d8103, d2529, d347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42514 (p : Pattern) (guard : d8107 p = 1) : d2537 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2537, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41919 p hg
    simpa only [d8107, d2537, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2537, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34455 p hg
    simpa only [d8107, d2537, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42515 (p : Pattern) (guard : d8108 p = 1) : d2538 p ≤ (0 : Int) + d362 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d2538, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42266 p hg
    simpa only [d8108, d2538, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d2538, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42514 p hg
    simpa only [d8108, d2538, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42516 (p : Pattern) (guard : d8109 p = 1) : d2539 p ≤ (0 : Int) + d363 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8103 p = 1 := by simpa only [d8109, d2539, d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42513 p hg
    simpa only [d8109, d2539, d363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8108 p = 1 := by simpa only [d8109, d2539, d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42515 p hg
    simpa only [d8109, d2539, d363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42517 (p : Pattern) (guard : d8096 p = 1) : d2544 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d2544, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42060 p hg
    simpa only [d8096, d2544, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d2544, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41996 p hg
    simpa only [d8096, d2544, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42518 (p : Pattern) (guard : d8102 p = 1) : d2550 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d2550, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42517 p hg
    simpa only [d8102, d2550, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d2550, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42312 p hg
    simpa only [d8102, d2550, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42519 (p : Pattern) (guard : d8101 p = 1) : d2554 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2554, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42209 p hg
    simpa only [d8101, d2554, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2554, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41937 p hg
    simpa only [d8101, d2554, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42520 (p : Pattern) (guard : d8107 p = 1) : d2556 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2556, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42519 p hg
    simpa only [d8107, d2556, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2556, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42124 p hg
    simpa only [d8107, d2556, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42521 (p : Pattern) (guard : d8108 p = 1) : d2557 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d2557, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42518 p hg
    simpa only [d8108, d2557, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d2557, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42520 p hg
    simpa only [d8108, d2557, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42522 (p : Pattern) (guard : d8101 p = 1) : d2558 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2558, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42158 p hg
    simpa only [d8101, d2558, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2558, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34443 p hg
    simpa only [d8101, d2558, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42523 (p : Pattern) (guard : d8107 p = 1) : d2559 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2559, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42522 p hg
    simpa only [d8107, d2559, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2559, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42124 p hg
    simpa only [d8107, d2559, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42524 (p : Pattern) (guard : d8113 p = 1) : d2562 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2562, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42523 p hg
    simpa only [d8113, d2562, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2562, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42129 p hg
    simpa only [d8113, d2562, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42525 (p : Pattern) (guard : d8114 p = 1) : d2563 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d2563, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42521 p hg
    simpa only [d8114, d2563, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d2563, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42524 p hg
    simpa only [d8114, d2563, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42526 (p : Pattern) (guard : d8115 p = 1) : d2564 p ≤ (0 : Int) + d377 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8109 p = 1 := by simpa only [d8115, d2564, d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42516 p hg
    simpa only [d8115, d2564, d377, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8114 p = 1 := by simpa only [d8115, d2564, d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42525 p hg
    simpa only [d8115, d2564, d377, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42527 (p : Pattern) (guard : d8086 p = 1) : d2566 p ≤ (0 : Int) + d381 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d2566, d381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41891 p hg
    simpa only [d8086, d2566, d381, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d2566, d381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42237 p hg
    simpa only [d8086, d2566, d381, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42528 (p : Pattern) (guard : d8090 p = 1) : d2507 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d2507, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42207 p hg
    simpa only [d8090, d2507, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d2507, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41853 p hg
    simpa only [d8090, d2507, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42529 (p : Pattern) (guard : d8091 p = 1) : d2567 p ≤ (0 : Int) + d382 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d2567, d382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42527 p hg
    simpa only [d8091, d2567, d382, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d2567, d382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42528 p hg
    simpa only [d8091, d2567, d382, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42530 (p : Pattern) (guard : d8090 p = 1) : d2510 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d2510, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42237 p hg
    simpa only [d8090, d2510, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d2510, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42092 p hg
    simpa only [d8090, d2510, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42531 (p : Pattern) (guard : d8095 p = 1) : d2511 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2511, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42530 p hg
    simpa only [d8095, d2511, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2511, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34367 p hg
    simpa only [d8095, d2511, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42532 (p : Pattern) (guard : d8096 p = 1) : d2568 p ≤ (0 : Int) + d383 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d2568, d383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42529 p hg
    simpa only [d8096, d2568, d383, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d2568, d383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42531 p hg
    simpa only [d8096, d2568, d383, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42533 (p : Pattern) (guard : d8085 p = 1) : d2540 p ≤ (0 : Int) + d349 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d2540, d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34468 p hg
    simpa only [d8085, d2540, d349, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d2540, d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41787 p hg
    simpa only [d8085, d2540, d349, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42534 (p : Pattern) (guard : d8090 p = 1) : d2540 p ≤ (0 : Int) + d350 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42533 p hg
    simpa only [d8090, d350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41946 p hg
    simpa only [d8090, d350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42535 (p : Pattern) (guard : d8095 p = 1) : d2569 p ≤ (0 : Int) + d351 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2569, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42534 p hg
    simpa only [d8095, d2569, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2569, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41949 p hg
    simpa only [d8095, d2569, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42536 (p : Pattern) (guard : d8101 p = 1) : d2573 p ≤ (0 : Int) + d352 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2573, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42535 p hg
    simpa only [d8101, d2573, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2573, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42141 p hg
    simpa only [d8101, d2573, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42537 (p : Pattern) (guard : d8102 p = 1) : d2574 p ≤ (0 : Int) + d384 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d2574, d384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42532 p hg
    simpa only [d8102, d2574, d384, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d2574, d384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42536 p hg
    simpa only [d8102, d2574, d384, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42538 (p : Pattern) (guard : d8085 p = 1) : d2520 p ≤ (0 : Int) + d365 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d2520, d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34480 p hg
    simpa only [d8085, d2520, d365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d2520, d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41787 p hg
    simpa only [d8085, d2520, d365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42539 (p : Pattern) (guard : d8090 p = 1) : d2520 p ≤ (0 : Int) + d366 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42538 p hg
    simpa only [d8090, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41869 p hg
    simpa only [d8090, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42540 (p : Pattern) (guard : d8095 p = 1) : d2523 p ≤ (0 : Int) + d367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2523, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42539 p hg
    simpa only [d8095, d2523, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2523, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41872 p hg
    simpa only [d8095, d2523, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42541 (p : Pattern) (guard : d8101 p = 1) : d2527 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2527, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42540 p hg
    simpa only [d8101, d2527, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2527, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42100 p hg
    simpa only [d8101, d2527, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42542 (p : Pattern) (guard : d8089 p = 1) : d2530 p ≤ (0 : Int) + d357 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d2530, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34978 p hg
    simpa only [d8089, d2530, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d2530, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d8089, d2530, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42543 (p : Pattern) (guard : d8094 p = 1) : d2530 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42542 p hg
    simpa only [d8094, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41953 p hg
    simpa only [d8094, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42544 (p : Pattern) (guard : d8100 p = 1) : d2532 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2532, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42543 p hg
    simpa only [d8100, d2532, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2532, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41955 p hg
    simpa only [d8100, d2532, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42545 (p : Pattern) (guard : d8106 p = 1) : d2536 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2536, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42544 p hg
    simpa only [d8106, d2536, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2536, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42149 p hg
    simpa only [d8106, d2536, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42546 (p : Pattern) (guard : d8107 p = 1) : d2575 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2575, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42541 p hg
    simpa only [d8107, d2575, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2575, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42545 p hg
    simpa only [d8107, d2575, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42547 (p : Pattern) (guard : d8108 p = 1) : d2576 p ≤ (0 : Int) + d385 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d2576, d385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42537 p hg
    simpa only [d8108, d2576, d385, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d2576, d385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42546 p hg
    simpa only [d8108, d2576, d385, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42548 (p : Pattern) (guard : d8089 p = 1) : d2577 p ≤ (0 : Int) + d330 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d2577, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34985 p hg
    simpa only [d8089, d2577, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d2577, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d8089, d2577, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42549 (p : Pattern) (guard : d8094 p = 1) : d2577 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42548 p hg
    simpa only [d8094, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41960 p hg
    simpa only [d8094, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42550 (p : Pattern) (guard : d8100 p = 1) : d2579 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2579, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42549 p hg
    simpa only [d8100, d2579, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2579, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41962 p hg
    simpa only [d8100, d2579, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42551 (p : Pattern) (guard : d8106 p = 1) : d2581 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2581, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42550 p hg
    simpa only [d8106, d2581, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2581, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42030 p hg
    simpa only [d8106, d2581, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42552 (p : Pattern) (guard : d8107 p = 1) : d2582 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2582, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42298 p hg
    simpa only [d8107, d2582, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2582, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42551 p hg
    simpa only [d8107, d2582, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42553 (p : Pattern) (guard : d8089 p = 1) : d2551 p ≤ (0 : Int) + d332 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d2551, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34991 p hg
    simpa only [d8089, d2551, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d2551, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d8089, d2551, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42554 (p : Pattern) (guard : d8094 p = 1) : d2551 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42553 p hg
    simpa only [d8094, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41966 p hg
    simpa only [d8094, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42555 (p : Pattern) (guard : d8100 p = 1) : d2583 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2583, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42554 p hg
    simpa only [d8100, d2583, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2583, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41968 p hg
    simpa only [d8100, d2583, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42556 (p : Pattern) (guard : d8106 p = 1) : d2584 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2584, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42555 p hg
    simpa only [d8106, d2584, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2584, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42033 p hg
    simpa only [d8106, d2584, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42557 (p : Pattern) (guard : d8112 p = 1) : d2585 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2585, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42556 p hg
    simpa only [d8112, d2585, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2585, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34543 p hg
    simpa only [d8112, d2585, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42558 (p : Pattern) (guard : d8113 p = 1) : d2586 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2586, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42552 p hg
    simpa only [d8113, d2586, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2586, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42557 p hg
    simpa only [d8113, d2586, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42559 (p : Pattern) (guard : d8114 p = 1) : d2587 p ≤ (0 : Int) + d388 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d2587, d388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42547 p hg
    simpa only [d8114, d2587, d388, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d2587, d388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42558 p hg
    simpa only [d8114, d2587, d388, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
