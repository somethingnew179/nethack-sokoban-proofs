/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons300
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare42140 (p : Pattern) (guard : d8094 p = 1) : d2571 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d2571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41946 p hg
    simpa only [d8094, d2571, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d2571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42139 p hg
    simpa only [d8094, d2571, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42141 (p : Pattern) (guard : d8100 p = 1) : d2572 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42140 p hg
    simpa only [d8100, d2572, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d2572, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42142 (p : Pattern) (guard : d8101 p = 1) : d2573 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2573, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42138 p hg
    simpa only [d8101, d2573, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2573, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42141 p hg
    simpa only [d8101, d2573, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42143 (p : Pattern) (guard : d8102 p = 1) : d2644 p ≤ (0 : Int) + d355 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d2644, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42135 p hg
    simpa only [d8102, d2644, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d2644, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42142 p hg
    simpa only [d8102, d2644, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42144 (p : Pattern) (guard : d8085 p = 1) : d2520 p ≤ (0 : Int) + d357 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d2520, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34664 p hg
    simpa only [d8085, d2520, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d2520, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41787 p hg
    simpa only [d8085, d2520, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42145 (p : Pattern) (guard : d8090 p = 1) : d2520 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42144 p hg
    simpa only [d8090, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41869 p hg
    simpa only [d8090, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42146 (p : Pattern) (guard : d8095 p = 1) : d2523 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2523, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42145 p hg
    simpa only [d8095, d2523, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2523, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41872 p hg
    simpa only [d8095, d2523, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42147 (p : Pattern) (guard : d8101 p = 1) : d2527 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2527, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42146 p hg
    simpa only [d8101, d2527, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2527, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42100 p hg
    simpa only [d8101, d2527, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42148 (p : Pattern) (guard : d8099 p = 1) : d2534 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d2534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41953 p hg
    simpa only [d8099, d2534, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d2534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21674 p hg
    simpa only [d8099, d2534, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42149 (p : Pattern) (guard : d8105 p = 1) : d2535 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d2535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42148 p hg
    simpa only [d8105, d2535, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d2535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d2535, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42150 (p : Pattern) (guard : d8106 p = 1) : d2536 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41956 p hg
    simpa only [d8106, d2536, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42149 p hg
    simpa only [d8106, d2536, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42151 (p : Pattern) (guard : d8107 p = 1) : d2575 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2575, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42147 p hg
    simpa only [d8107, d2575, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2575, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42150 p hg
    simpa only [d8107, d2575, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42152 (p : Pattern) (guard : d8108 p = 1) : d2645 p ≤ (0 : Int) + d362 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d2645, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42143 p hg
    simpa only [d8108, d2645, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d2645, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42151 p hg
    simpa only [d8108, d2645, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42153 (p : Pattern) (guard : d8107 p = 1) : d2582 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2582, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42101 p hg
    simpa only [d8107, d2582, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2582, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42031 p hg
    simpa only [d8107, d2582, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42154 (p : Pattern) (guard : d8113 p = 1) : d2586 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2586, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42153 p hg
    simpa only [d8113, d2586, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2586, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42035 p hg
    simpa only [d8113, d2586, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42155 (p : Pattern) (guard : d8114 p = 1) : d2646 p ≤ (0 : Int) + d395 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d2646, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42152 p hg
    simpa only [d8114, d2646, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d2646, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42154 p hg
    simpa only [d8114, d2646, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42156 (p : Pattern) (guard : d8085 p = 1) : d2504 p ≤ (0 : Int) + d332 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d2504, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34332 p hg
    simpa only [d8085, d2504, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d2504, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41787 p hg
    simpa only [d8085, d2504, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42157 (p : Pattern) (guard : d8090 p = 1) : d2504 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42156 p hg
    simpa only [d8090, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42112 p hg
    simpa only [d8090, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42158 (p : Pattern) (guard : d8095 p = 1) : d2518 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2518, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42157 p hg
    simpa only [d8095, d2518, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2518, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42115 p hg
    simpa only [d8095, d2518, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42159 (p : Pattern) (guard : d8101 p = 1) : d2549 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2549, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42158 p hg
    simpa only [d8101, d2549, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2549, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42003 p hg
    simpa only [d8101, d2549, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42160 (p : Pattern) (guard : d5854 p = 1) : d2540 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d2540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34472 p hg
    simpa only [d5854, d2540, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d2540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5854, d2540, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42161 (p : Pattern) (guard : d8094 p = 1) : d2540 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41946 p hg
    simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42160 p hg
    simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42162 (p : Pattern) (guard : d8099 p = 1) : d2542 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d2542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42160 p hg
    simpa only [d8099, d2542, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d2542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21681 p hg
    simpa only [d8099, d2542, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42163 (p : Pattern) (guard : d8100 p = 1) : d2569 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42161 p hg
    simpa only [d8100, d2569, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42162 p hg
    simpa only [d8100, d2569, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42164 (p : Pattern) (guard : d8106 p = 1) : d2588 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42163 p hg
    simpa only [d8106, d2588, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34532 p hg
    simpa only [d8106, d2588, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42165 (p : Pattern) (guard : d8107 p = 1) : d2589 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2589, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42159 p hg
    simpa only [d8107, d2589, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2589, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42164 p hg
    simpa only [d8107, d2589, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42166 (p : Pattern) (guard : d8099 p = 1) : d2530 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41953 p hg
    simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21669 p hg
    simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42167 (p : Pattern) (guard : d8105 p = 1) : d2532 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d2532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42166 p hg
    simpa only [d8105, d2532, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d2532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22570 p hg
    simpa only [d8105, d2532, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42168 (p : Pattern) (guard : d8111 p = 1) : d2560 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42167 p hg
    simpa only [d8111, d2560, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8111, d2560, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42169 (p : Pattern) (guard : d8112 p = 1) : d2590 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42124 p hg
    simpa only [d8112, d2590, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42168 p hg
    simpa only [d8112, d2590, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42170 (p : Pattern) (guard : d8113 p = 1) : d2591 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2591, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42165 p hg
    simpa only [d8113, d2591, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2591, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42169 p hg
    simpa only [d8113, d2591, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42171 (p : Pattern) (guard : d8099 p = 1) : d2577 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41960 p hg
    simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21718 p hg
    simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42172 (p : Pattern) (guard : d8105 p = 1) : d2579 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d2579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42171 p hg
    simpa only [d8105, d2579, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d2579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22604 p hg
    simpa only [d8105, d2579, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42173 (p : Pattern) (guard : d8111 p = 1) : d2592 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42172 p hg
    simpa only [d8111, d2592, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8111, d2592, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42174 (p : Pattern) (guard : d8112 p = 1) : d2593 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42124 p hg
    simpa only [d8112, d2593, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42173 p hg
    simpa only [d8112, d2593, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42175 (p : Pattern) (guard : d8099 p = 1) : d2551 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41966 p hg
    simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21726 p hg
    simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42176 (p : Pattern) (guard : d8105 p = 1) : d2583 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d2583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42175 p hg
    simpa only [d8105, d2583, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d2583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22609 p hg
    simpa only [d8105, d2583, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42177 (p : Pattern) (guard : d8111 p = 1) : d2594 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42176 p hg
    simpa only [d8111, d2594, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8111, d2594, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42178 (p : Pattern) (guard : d8117 p = 1) : d2595 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2595, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42177 p hg
    simpa only [d8117, d2595, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2595, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8117, d2595, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42179 (p : Pattern) (guard : d8118 p = 1) : d2596 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42174 p hg
    simpa only [d8118, d2596, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42178 p hg
    simpa only [d8118, d2596, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42180 (p : Pattern) (guard : d8119 p = 1) : d2597 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d2597, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42170 p hg
    simpa only [d8119, d2597, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d2597, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42179 p hg
    simpa only [d8119, d2597, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42181 (p : Pattern) (guard : d8120 p = 1) : d2647 p ≤ (0 : Int) + d397 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d2647, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42155 p hg
    simpa only [d8120, d2647, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d2647, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42180 p hg
    simpa only [d8120, d2647, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42182 (p : Pattern) (guard : d8121 p = 1) : d2648 p ≤ (0 : Int) + d419 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8115 p = 1 := by simpa only [d8121, d2648, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42132 p hg
    simpa only [d8121, d2648, d419, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8120 p = 1 := by simpa only [d8121, d2648, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42181 p hg
    simpa only [d8121, d2648, d419, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42183 (p : Pattern) (guard : d8100 p = 1) : d2600 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42115 p hg
    simpa only [d8100, d2600, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d2600, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42184 (p : Pattern) (guard : d8101 p = 1) : d2601 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2601, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42158 p hg
    simpa only [d8101, d2601, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2601, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42183 p hg
    simpa only [d8101, d2601, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42185 (p : Pattern) (guard : d8102 p = 1) : d2601 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41979 p hg
    simpa only [d8102, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42184 p hg
    simpa only [d8102, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42186 (p : Pattern) (guard : d8101 p = 1) : d2601 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42116 p hg
    simpa only [d8101, d2601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42183 p hg
    simpa only [d8101, d2601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42187 (p : Pattern) (guard : d8105 p = 1) : d2602 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d2602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42122 p hg
    simpa only [d8105, d2602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d2602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d2602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42188 (p : Pattern) (guard : d8106 p = 1) : d2603 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42123 p hg
    simpa only [d8106, d2603, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42187 p hg
    simpa only [d8106, d2603, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42189 (p : Pattern) (guard : d8107 p = 1) : d2604 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42186 p hg
    simpa only [d8107, d2604, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42188 p hg
    simpa only [d8107, d2604, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42190 (p : Pattern) (guard : d8108 p = 1) : d2605 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d2605, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42185 p hg
    simpa only [d8108, d2605, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d2605, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42189 p hg
    simpa only [d8108, d2605, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42191 (p : Pattern) (guard : d8112 p = 1) : d2608 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42027 p hg
    simpa only [d8112, d2608, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34543 p hg
    simpa only [d8112, d2608, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42192 (p : Pattern) (guard : d8113 p = 1) : d2609 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42189 p hg
    simpa only [d8113, d2609, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42191 p hg
    simpa only [d8113, d2609, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42193 (p : Pattern) (guard : d8114 p = 1) : d2610 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d2610, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42190 p hg
    simpa only [d8114, d2610, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d2610, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42192 p hg
    simpa only [d8114, d2610, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42194 (p : Pattern) (guard : d8090 p = 1) : d2540 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41899 p hg
    simpa only [d8090, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41946 p hg
    simpa only [d8090, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42195 (p : Pattern) (guard : d8095 p = 1) : d2569 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42194 p hg
    simpa only [d8095, d2569, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41949 p hg
    simpa only [d8095, d2569, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42196 (p : Pattern) (guard : d8101 p = 1) : d2611 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42195 p hg
    simpa only [d8101, d2611, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42019 p hg
    simpa only [d8101, d2611, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42197 (p : Pattern) (guard : d5854 p = 1) : d2545 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d2545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34424 p hg
    simpa only [d5854, d2545, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d2545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5854, d2545, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42198 (p : Pattern) (guard : d8094 p = 1) : d2545 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41998 p hg
    simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42197 p hg
    simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42199 (p : Pattern) (guard : d8099 p = 1) : d2547 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d2547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42197 p hg
    simpa only [d8099, d2547, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d2547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21685 p hg
    simpa only [d8099, d2547, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42200 (p : Pattern) (guard : d8100 p = 1) : d2612 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42198 p hg
    simpa only [d8100, d2612, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42199 p hg
    simpa only [d8100, d2612, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42201 (p : Pattern) (guard : d8105 p = 1) : d2548 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d2548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42199 p hg
    simpa only [d8105, d2548, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d2548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d2548, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42202 (p : Pattern) (guard : d8106 p = 1) : d2613 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42200 p hg
    simpa only [d8106, d2613, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42201 p hg
    simpa only [d8106, d2613, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42203 (p : Pattern) (guard : d8107 p = 1) : d2614 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42196 p hg
    simpa only [d8107, d2614, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42202 p hg
    simpa only [d8107, d2614, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42204 (p : Pattern) (guard : d8113 p = 1) : d2615 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42203 p hg
    simpa only [d8113, d2615, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42035 p hg
    simpa only [d8113, d2615, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42205 (p : Pattern) (guard : d8119 p = 1) : d2616 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d2616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42204 p hg
    simpa only [d8119, d2616, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d2616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34613 p hg
    simpa only [d8119, d2616, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42206 (p : Pattern) (guard : d8120 p = 1) : d2617 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d2617, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42193 p hg
    simpa only [d8120, d2617, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d2617, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42205 p hg
    simpa only [d8120, d2617, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42207 (p : Pattern) (guard : d8085 p = 1) : d2504 p ≤ (0 : Int) + d330 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d2504, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34334 p hg
    simpa only [d8085, d2504, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d2504, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41787 p hg
    simpa only [d8085, d2504, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42208 (p : Pattern) (guard : d8090 p = 1) : d2504 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42207 p hg
    simpa only [d8090, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42112 p hg
    simpa only [d8090, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42209 (p : Pattern) (guard : d8095 p = 1) : d2518 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2518, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42208 p hg
    simpa only [d8095, d2518, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2518, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42115 p hg
    simpa only [d8095, d2518, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42210 (p : Pattern) (guard : d8101 p = 1) : d2601 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2601, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42209 p hg
    simpa only [d8101, d2601, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2601, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42183 p hg
    simpa only [d8101, d2601, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42211 (p : Pattern) (guard : d8105 p = 1) : d2543 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d2543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42162 p hg
    simpa only [d8105, d2543, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d2543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d2543, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42212 (p : Pattern) (guard : d8106 p = 1) : d2611 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42163 p hg
    simpa only [d8106, d2611, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42211 p hg
    simpa only [d8106, d2611, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42213 (p : Pattern) (guard : d8107 p = 1) : d2618 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2618, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42210 p hg
    simpa only [d8107, d2618, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2618, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42212 p hg
    simpa only [d8107, d2618, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42214 (p : Pattern) (guard : d0 p = 1) : d2606 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42215 (p : Pattern) (guard : d8111 p = 1) : d2607 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42167 p hg
    simpa only [d8111, d2607, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42214 p hg
    simpa only [d8111, d2607, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42216 (p : Pattern) (guard : d8112 p = 1) : d2619 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42188 p hg
    simpa only [d8112, d2619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42215 p hg
    simpa only [d8112, d2619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42217 (p : Pattern) (guard : d8113 p = 1) : d2620 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2620, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42213 p hg
    simpa only [d8113, d2620, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2620, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42216 p hg
    simpa only [d8113, d2620, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42218 (p : Pattern) (guard : d0 p = 1) : d2580 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42219 (p : Pattern) (guard : d8111 p = 1) : d2581 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42172 p hg
    simpa only [d8111, d2581, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42218 p hg
    simpa only [d8111, d2581, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42220 (p : Pattern) (guard : d8112 p = 1) : d2621 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42188 p hg
    simpa only [d8112, d2621, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42219 p hg
    simpa only [d8112, d2621, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42221 (p : Pattern) (guard : d0 p = 1) : d2553 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42222 (p : Pattern) (guard : d8111 p = 1) : d2584 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42176 p hg
    simpa only [d8111, d2584, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42221 p hg
    simpa only [d8111, d2584, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42223 (p : Pattern) (guard : d8117 p = 1) : d2585 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42222 p hg
    simpa only [d8117, d2585, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8117, d2585, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42224 (p : Pattern) (guard : d8118 p = 1) : d2622 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42220 p hg
    simpa only [d8118, d2622, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42223 p hg
    simpa only [d8118, d2622, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42225 (p : Pattern) (guard : d8119 p = 1) : d2623 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d2623, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42217 p hg
    simpa only [d8119, d2623, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d2623, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42224 p hg
    simpa only [d8119, d2623, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42226 (p : Pattern) (guard : d8112 p = 1) : d2624 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42202 p hg
    simpa only [d8112, d2624, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34543 p hg
    simpa only [d8112, d2624, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42227 (p : Pattern) (guard : d8118 p = 1) : d2625 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42226 p hg
    simpa only [d8118, d2625, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34734 p hg
    simpa only [d8118, d2625, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42228 (p : Pattern) (guard : d8124 p = 1) : d2626 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d2626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42227 p hg
    simpa only [d8124, d2626, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d2626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34736 p hg
    simpa only [d8124, d2626, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42229 (p : Pattern) (guard : d8125 p = 1) : d2627 p ≤ (0 : Int) + d421 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d2627, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42225 p hg
    simpa only [d8125, d2627, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d2627, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42228 p hg
    simpa only [d8125, d2627, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42230 (p : Pattern) (guard : d8126 p = 1) : d2628 p ≤ (0 : Int) + d422 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d2628, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42206 p hg
    simpa only [d8126, d2628, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d2628, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42229 p hg
    simpa only [d8126, d2628, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42231 (p : Pattern) (guard : d8127 p = 1) : d2649 p ≤ (0 : Int) + d423 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8121 p = 1 := by simpa only [d8127, d2649, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42182 p hg
    simpa only [d8127, d2649, d423, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8126 p = 1 := by simpa only [d8127, d2649, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42230 p hg
    simpa only [d8127, d2649, d423, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42232 (p : Pattern) (guard : d8102 p = 1) : d2601 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42015 p hg
    simpa only [d8102, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42210 p hg
    simpa only [d8102, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42233 (p : Pattern) (guard : d8107 p = 1) : d2604 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2604, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42184 p hg
    simpa only [d8107, d2604, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2604, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42188 p hg
    simpa only [d8107, d2604, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42234 (p : Pattern) (guard : d8108 p = 1) : d2605 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d2605, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42232 p hg
    simpa only [d8108, d2605, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d2605, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42233 p hg
    simpa only [d8108, d2605, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42235 (p : Pattern) (guard : d8114 p = 1) : d2610 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d2610, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42234 p hg
    simpa only [d8114, d2610, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d2610, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42192 p hg
    simpa only [d8114, d2610, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42236 (p : Pattern) (guard : d8120 p = 1) : d2617 p ≤ (0 : Int) + d399 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d2617, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42235 p hg
    simpa only [d8120, d2617, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d2617, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42205 p hg
    simpa only [d8120, d2617, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42237 (p : Pattern) (guard : d8085 p = 1) : d2504 p ≤ (0 : Int) + d357 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d2504, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34413 p hg
    simpa only [d8085, d2504, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d2504, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41787 p hg
    simpa only [d8085, d2504, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42238 (p : Pattern) (guard : d8090 p = 1) : d2504 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42237 p hg
    simpa only [d8090, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42112 p hg
    simpa only [d8090, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42239 (p : Pattern) (guard : d8095 p = 1) : d2518 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2518, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42238 p hg
    simpa only [d8095, d2518, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2518, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42115 p hg
    simpa only [d8095, d2518, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42240 (p : Pattern) (guard : d8101 p = 1) : d2601 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2601, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42239 p hg
    simpa only [d8101, d2601, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2601, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42183 p hg
    simpa only [d8101, d2601, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42241 (p : Pattern) (guard : d8107 p = 1) : d2618 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2618, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42240 p hg
    simpa only [d8107, d2618, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2618, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42212 p hg
    simpa only [d8107, d2618, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42242 (p : Pattern) (guard : d8113 p = 1) : d2620 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2620, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42241 p hg
    simpa only [d8113, d2620, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2620, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42216 p hg
    simpa only [d8113, d2620, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42243 (p : Pattern) (guard : d8119 p = 1) : d2623 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d2623, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42242 p hg
    simpa only [d8119, d2623, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d2623, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42224 p hg
    simpa only [d8119, d2623, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42244 (p : Pattern) (guard : d8125 p = 1) : d2627 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d2627, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42243 p hg
    simpa only [d8125, d2627, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d2627, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42228 p hg
    simpa only [d8125, d2627, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42245 (p : Pattern) (guard : d8126 p = 1) : d2628 p ≤ (0 : Int) + d424 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d2628, d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42236 p hg
    simpa only [d8126, d2628, d424, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d2628, d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42244 p hg
    simpa only [d8126, d2628, d424, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42246 (p : Pattern) (guard : d8132 p = 1) : d2650 p ≤ (0 : Int) + d425 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d2650, d425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42245 p hg
    simpa only [d8132, d2650, d425, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d2650, d425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36499 p hg
    simpa only [d8132, d2650, d425, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42247 (p : Pattern) (guard : d8133 p = 1) : d2651 p ≤ (0 : Int) + d426 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8127 p = 1 := by simpa only [d8133, d2651, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42231 p hg
    simpa only [d8133, d2651, d426, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8132 p = 1 := by simpa only [d8133, d2651, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42246 p hg
    simpa only [d8133, d2651, d426, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42248 (p : Pattern) (guard : d8134 p = 1) : d2652 p ≤ (0 : Int) + d427 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8128 p = 1 := by simpa only [d8134, d2652, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42091 p hg
    simpa only [d8134, d2652, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8133 p = 1 := by simpa only [d8134, d2652, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42247 p hg
    simpa only [d8134, d2652, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42249 (p : Pattern) (guard : d1 p = 1) : d2653 p ≤ (0 : Int) + d430 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2653, d430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34744 p hg
    simpa only [d2653, d430, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2653, d430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17232 p hg
    simpa only [d2653, d430, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42250 (p : Pattern) (guard : d1 p = 1) : d2654 p ≤ (0 : Int) + d431 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2654, d431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42249 p hg
    simpa only [d2654, d431, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2654, d431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41775 p hg
    simpa only [d2654, d431, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42251 (p : Pattern) (guard : d8086 p = 1) : d2507 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d2507, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41850 p hg
    simpa only [d8086, d2507, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d2507, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41788 p hg
    simpa only [d8086, d2507, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42252 (p : Pattern) (guard : d8087 p = 1) : d2655 p ≤ (0 : Int) + d432 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8087, d2655, d432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42250 p hg
    simpa only [d8087, d2655, d432, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8086 p = 1 := by simpa only [d8087, d2655, d432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42251 p hg
    simpa only [d8087, d2655, d432, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42253 (p : Pattern) (guard : d8086 p = 1) : d2510 p ≤ (0 : Int) + d321 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d2510, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41775 p hg
    simpa only [d8086, d2510, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d2510, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41791 p hg
    simpa only [d8086, d2510, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42254 (p : Pattern) (guard : d8091 p = 1) : d2511 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d2511, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42253 p hg
    simpa only [d8091, d2511, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d2511, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34344 p hg
    simpa only [d8091, d2511, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42255 (p : Pattern) (guard : d8092 p = 1) : d2656 p ≤ (0 : Int) + d433 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8087 p = 1 := by simpa only [d8092, d2656, d433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42252 p hg
    simpa only [d8092, d2656, d433, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8091 p = 1 := by simpa only [d8092, d2656, d433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42254 p hg
    simpa only [d8092, d2656, d433, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42256 (p : Pattern) (guard : d8086 p = 1) : d2504 p ≤ (0 : Int) + d341 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41796 p hg
    simpa only [d8086, d341, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42156 p hg
    simpa only [d8086, d341, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42257 (p : Pattern) (guard : d8091 p = 1) : d2518 p ≤ (0 : Int) + d342 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d2518, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42256 p hg
    simpa only [d8091, d2518, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d2518, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41854 p hg
    simpa only [d8091, d2518, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42258 (p : Pattern) (guard : d8090 p = 1) : d2510 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d2510, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42156 p hg
    simpa only [d8090, d2510, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d2510, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42092 p hg
    simpa only [d8090, d2510, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42259 (p : Pattern) (guard : d8095 p = 1) : d2511 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2511, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42258 p hg
    simpa only [d8095, d2511, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2511, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34367 p hg
    simpa only [d8095, d2511, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42260 (p : Pattern) (guard : d8096 p = 1) : d2519 p ≤ (0 : Int) + d344 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d2519, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42257 p hg
    simpa only [d8096, d2519, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d2519, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42259 p hg
    simpa only [d8096, d2519, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42261 (p : Pattern) (guard : d8097 p = 1) : d2657 p ≤ (0 : Int) + d434 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8092 p = 1 := by simpa only [d8097, d2657, d434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42255 p hg
    simpa only [d8097, d2657, d434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8096 p = 1 := by simpa only [d8097, d2657, d434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42260 p hg
    simpa only [d8097, d2657, d434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42262 (p : Pattern) (guard : d8085 p = 1) : d2520 p ≤ (0 : Int) + d320 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d2520, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34380 p hg
    simpa only [d8085, d2520, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d2520, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41787 p hg
    simpa only [d8085, d2520, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42263 (p : Pattern) (guard : d8090 p = 1) : d2520 p ≤ (0 : Int) + d321 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42262 p hg
    simpa only [d8090, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41869 p hg
    simpa only [d8090, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42264 (p : Pattern) (guard : d8095 p = 1) : d2523 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2523, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42263 p hg
    simpa only [d8095, d2523, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2523, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41872 p hg
    simpa only [d8095, d2523, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42265 (p : Pattern) (guard : d8101 p = 1) : d2527 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2527, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42264 p hg
    simpa only [d8101, d2527, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2527, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42100 p hg
    simpa only [d8101, d2527, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42266 (p : Pattern) (guard : d8102 p = 1) : d2528 p ≤ (0 : Int) + d355 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d2528, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42135 p hg
    simpa only [d8102, d2528, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d2528, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42265 p hg
    simpa only [d8102, d2528, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42267 (p : Pattern) (guard : d8103 p = 1) : d2658 p ≤ (0 : Int) + d435 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8097 p = 1 := by simpa only [d8103, d2658, d435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42261 p hg
    simpa only [d8103, d2658, d435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8102 p = 1 := by simpa only [d8103, d2658, d435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42266 p hg
    simpa only [d8103, d2658, d435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42268 (p : Pattern) (guard : d8102 p = 1) : d2528 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d2528, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42095 p hg
    simpa only [d8102, d2528, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d2528, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42147 p hg
    simpa only [d8102, d2528, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42269 (p : Pattern) (guard : d8085 p = 1) : d2530 p ≤ (0 : Int) + d330 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d2530, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34763 p hg
    simpa only [d8085, d2530, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d2530, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41787 p hg
    simpa only [d8085, d2530, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42270 (p : Pattern) (guard : d8090 p = 1) : d2530 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42269 p hg
    simpa only [d8090, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41881 p hg
    simpa only [d8090, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42271 (p : Pattern) (guard : d8095 p = 1) : d2532 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2532, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42270 p hg
    simpa only [d8095, d2532, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2532, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41884 p hg
    simpa only [d8095, d2532, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42272 (p : Pattern) (guard : d8101 p = 1) : d2536 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2536, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42271 p hg
    simpa only [d8101, d2536, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2536, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41918 p hg
    simpa only [d8101, d2536, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42273 (p : Pattern) (guard : d8107 p = 1) : d2537 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2537, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42272 p hg
    simpa only [d8107, d2537, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2537, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34455 p hg
    simpa only [d8107, d2537, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42274 (p : Pattern) (guard : d8108 p = 1) : d2538 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d2538, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42268 p hg
    simpa only [d8108, d2538, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d2538, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42273 p hg
    simpa only [d8108, d2538, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42275 (p : Pattern) (guard : d8109 p = 1) : d2659 p ≤ (0 : Int) + d436 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8103 p = 1 := by simpa only [d8109, d2659, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42267 p hg
    simpa only [d8109, d2659, d436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8108 p = 1 := by simpa only [d8109, d2659, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42274 p hg
    simpa only [d8109, d2659, d436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42276 (p : Pattern) (guard : d8096 p = 1) : d2544 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d2544, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42014 p hg
    simpa only [d8096, d2544, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d2544, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41996 p hg
    simpa only [d8096, d2544, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42277 (p : Pattern) (guard : d8101 p = 1) : d2549 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2549, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42209 p hg
    simpa only [d8101, d2549, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2549, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42003 p hg
    simpa only [d8101, d2549, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42278 (p : Pattern) (guard : d8102 p = 1) : d2550 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d2550, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42276 p hg
    simpa only [d8102, d2550, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d2550, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42277 p hg
    simpa only [d8102, d2550, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42279 (p : Pattern) (guard : d8101 p = 1) : d2554 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2554, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42158 p hg
    simpa only [d8101, d2554, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2554, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41937 p hg
    simpa only [d8101, d2554, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
