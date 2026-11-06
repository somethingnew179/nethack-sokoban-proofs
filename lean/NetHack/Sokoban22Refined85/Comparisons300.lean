/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons299
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare42000 (p : Pattern) (guard : d5854 p = 1) : d2546 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d2546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38531 p hg
    simpa only [d5854, d2546, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d2546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5854, d2546, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42001 (p : Pattern) (guard : d8094 p = 1) : d2547 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d2547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41998 p hg
    simpa only [d8094, d2547, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d2547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42000 p hg
    simpa only [d8094, d2547, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42002 (p : Pattern) (guard : d8095 p = 1) : d2612 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41999 p hg
    simpa only [d8095, d2612, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42001 p hg
    simpa only [d8095, d2612, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42003 (p : Pattern) (guard : d8100 p = 1) : d2548 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42001 p hg
    simpa only [d8100, d2548, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d2548, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42004 (p : Pattern) (guard : d8101 p = 1) : d2613 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42002 p hg
    simpa only [d8101, d2613, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42003 p hg
    simpa only [d8101, d2613, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42005 (p : Pattern) (guard : d8102 p = 1) : d2614 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d2614, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41997 p hg
    simpa only [d8102, d2614, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d2614, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42004 p hg
    simpa only [d8102, d2614, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42006 (p : Pattern) (guard : d8090 p = 1) : d2551 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41864 p hg
    simpa only [d8090, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41932 p hg
    simpa only [d8090, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42007 (p : Pattern) (guard : d8095 p = 1) : d2583 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42006 p hg
    simpa only [d8095, d2583, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41935 p hg
    simpa only [d8095, d2583, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42008 (p : Pattern) (guard : d8101 p = 1) : d2584 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42007 p hg
    simpa only [d8101, d2584, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41937 p hg
    simpa only [d8101, d2584, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42009 (p : Pattern) (guard : d8107 p = 1) : d2585 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42008 p hg
    simpa only [d8107, d2585, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34455 p hg
    simpa only [d8107, d2585, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42010 (p : Pattern) (guard : d8108 p = 1) : d2615 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d2615, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42005 p hg
    simpa only [d8108, d2615, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d2615, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42009 p hg
    simpa only [d8108, d2615, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42011 (p : Pattern) (guard : d8114 p = 1) : d2616 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d2616, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42010 p hg
    simpa only [d8114, d2616, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d2616, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34577 p hg
    simpa only [d8114, d2616, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42012 (p : Pattern) (guard : d8115 p = 1) : d2617 p ≤ (0 : Int) + d397 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8109 p = 1 := by simpa only [d8115, d2617, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41992 p hg
    simpa only [d8115, d2617, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8114 p = 1 := by simpa only [d8115, d2617, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42011 p hg
    simpa only [d8115, d2617, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42013 (p : Pattern) (guard : d8086 p = 1) : d2504 p ≤ (0 : Int) + d323 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41773 p hg
    simpa only [d8086, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41851 p hg
    simpa only [d8086, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42014 (p : Pattern) (guard : d8091 p = 1) : d2518 p ≤ (0 : Int) + d324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d2518, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42013 p hg
    simpa only [d8091, d2518, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d2518, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41854 p hg
    simpa only [d8091, d2518, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42015 (p : Pattern) (guard : d8096 p = 1) : d2601 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d2601, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42014 p hg
    simpa only [d8096, d2601, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d2601, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41978 p hg
    simpa only [d8096, d2601, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42016 (p : Pattern) (guard : d8085 p = 1) : d2540 p ≤ (0 : Int) + d330 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d2540, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34585 p hg
    simpa only [d8085, d2540, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d2540, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41787 p hg
    simpa only [d8085, d2540, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42017 (p : Pattern) (guard : d8090 p = 1) : d2540 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42016 p hg
    simpa only [d8090, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41946 p hg
    simpa only [d8090, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42018 (p : Pattern) (guard : d8095 p = 1) : d2569 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2569, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42017 p hg
    simpa only [d8095, d2569, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2569, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41949 p hg
    simpa only [d8095, d2569, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42019 (p : Pattern) (guard : d8100 p = 1) : d2543 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41949 p hg
    simpa only [d8100, d2543, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d2543, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42020 (p : Pattern) (guard : d8101 p = 1) : d2611 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2611, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42018 p hg
    simpa only [d8101, d2611, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2611, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42019 p hg
    simpa only [d8101, d2611, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42021 (p : Pattern) (guard : d8102 p = 1) : d2618 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d2618, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42015 p hg
    simpa only [d8102, d2618, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d2618, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42020 p hg
    simpa only [d8102, d2618, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42022 (p : Pattern) (guard : d8085 p = 1) : d2520 p ≤ (0 : Int) + d332 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d2520, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34593 p hg
    simpa only [d8085, d2520, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d2520, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41787 p hg
    simpa only [d8085, d2520, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42023 (p : Pattern) (guard : d8090 p = 1) : d2520 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42022 p hg
    simpa only [d8090, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41869 p hg
    simpa only [d8090, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42024 (p : Pattern) (guard : d8095 p = 1) : d2523 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2523, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42023 p hg
    simpa only [d8095, d2523, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2523, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41872 p hg
    simpa only [d8095, d2523, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42025 (p : Pattern) (guard : d8101 p = 1) : d2603 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2603, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42024 p hg
    simpa only [d8101, d2603, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2603, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41982 p hg
    simpa only [d8101, d2603, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42026 (p : Pattern) (guard : d8105 p = 1) : d2606 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d2606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41955 p hg
    simpa only [d8105, d2606, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d2606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d2606, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42027 (p : Pattern) (guard : d8106 p = 1) : d2607 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41956 p hg
    simpa only [d8106, d2607, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42026 p hg
    simpa only [d8106, d2607, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42028 (p : Pattern) (guard : d8107 p = 1) : d2619 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2619, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42025 p hg
    simpa only [d8107, d2619, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2619, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42027 p hg
    simpa only [d8107, d2619, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42029 (p : Pattern) (guard : d8108 p = 1) : d2620 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d2620, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42021 p hg
    simpa only [d8108, d2620, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d2620, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42028 p hg
    simpa only [d8108, d2620, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42030 (p : Pattern) (guard : d8105 p = 1) : d2580 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d2580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41962 p hg
    simpa only [d8105, d2580, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d2580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d2580, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42031 (p : Pattern) (guard : d8106 p = 1) : d2581 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41963 p hg
    simpa only [d8106, d2581, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42030 p hg
    simpa only [d8106, d2581, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42032 (p : Pattern) (guard : d8107 p = 1) : d2621 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41983 p hg
    simpa only [d8107, d2621, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42031 p hg
    simpa only [d8107, d2621, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42033 (p : Pattern) (guard : d8105 p = 1) : d2553 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d2553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41968 p hg
    simpa only [d8105, d2553, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d2553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d2553, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42034 (p : Pattern) (guard : d8106 p = 1) : d2584 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41969 p hg
    simpa only [d8106, d2584, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42033 p hg
    simpa only [d8106, d2584, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42035 (p : Pattern) (guard : d8112 p = 1) : d2585 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42034 p hg
    simpa only [d8112, d2585, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34543 p hg
    simpa only [d8112, d2585, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42036 (p : Pattern) (guard : d8113 p = 1) : d2622 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42032 p hg
    simpa only [d8113, d2622, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42035 p hg
    simpa only [d8113, d2622, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42037 (p : Pattern) (guard : d8114 p = 1) : d2623 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d2623, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42029 p hg
    simpa only [d8114, d2623, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d2623, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42036 p hg
    simpa only [d8114, d2623, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42038 (p : Pattern) (guard : d8107 p = 1) : d2624 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42004 p hg
    simpa only [d8107, d2624, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34455 p hg
    simpa only [d8107, d2624, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42039 (p : Pattern) (guard : d8113 p = 1) : d2625 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42038 p hg
    simpa only [d8113, d2625, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34611 p hg
    simpa only [d8113, d2625, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42040 (p : Pattern) (guard : d8119 p = 1) : d2626 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d2626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42039 p hg
    simpa only [d8119, d2626, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d2626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34613 p hg
    simpa only [d8119, d2626, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42041 (p : Pattern) (guard : d8120 p = 1) : d2627 p ≤ (0 : Int) + d399 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d2627, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42037 p hg
    simpa only [d8120, d2627, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d2627, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42040 p hg
    simpa only [d8120, d2627, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42042 (p : Pattern) (guard : d8121 p = 1) : d2628 p ≤ (0 : Int) + d400 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8115 p = 1 := by simpa only [d8121, d2628, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42012 p hg
    simpa only [d8121, d2628, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8120 p = 1 := by simpa only [d8121, d2628, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42041 p hg
    simpa only [d8121, d2628, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42043 (p : Pattern) (guard : d8122 p = 1) : d2629 p ≤ (0 : Int) + d401 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8116 p = 1 := by simpa only [d8122, d2629, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41975 p hg
    simpa only [d8122, d2629, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8121 p = 1 := by simpa only [d8122, d2629, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42042 p hg
    simpa only [d8122, d2629, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42044 (p : Pattern) (guard : d8091 p = 1) : d2600 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d2600, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41789 p hg
    simpa only [d8091, d2600, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d2600, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34344 p hg
    simpa only [d8091, d2600, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42045 (p : Pattern) (guard : d8092 p = 1) : d2601 p ≤ (0 : Int) + d344 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8087 p = 1 := by simpa only [d8092, d2601, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41800 p hg
    simpa only [d8092, d2601, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8091 p = 1 := by simpa only [d8092, d2601, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42044 p hg
    simpa only [d8092, d2601, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42046 (p : Pattern) (guard : d8097 p = 1) : d2601 p ≤ (0 : Int) + d346 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8092 p = 1 := by simpa only [d8097, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42045 p hg
    simpa only [d8097, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8096 p = 1 := by simpa only [d8097, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42015 p hg
    simpa only [d8097, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42047 (p : Pattern) (guard : d8102 p = 1) : d2604 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d2604, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41979 p hg
    simpa only [d8102, d2604, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d2604, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42025 p hg
    simpa only [d8102, d2604, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42048 (p : Pattern) (guard : d8103 p = 1) : d2605 p ≤ (0 : Int) + d402 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8097 p = 1 := by simpa only [d8103, d2605, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42046 p hg
    simpa only [d8103, d2605, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8102 p = 1 := by simpa only [d8103, d2605, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42047 p hg
    simpa only [d8103, d2605, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42049 (p : Pattern) (guard : d8108 p = 1) : d2609 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d2609, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41984 p hg
    simpa only [d8108, d2609, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d2609, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41990 p hg
    simpa only [d8108, d2609, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42050 (p : Pattern) (guard : d8109 p = 1) : d2610 p ≤ (0 : Int) + d404 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8103 p = 1 := by simpa only [d8109, d2610, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42048 p hg
    simpa only [d8109, d2610, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8108 p = 1 := by simpa only [d8109, d2610, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42049 p hg
    simpa only [d8109, d2610, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42051 (p : Pattern) (guard : d1 p = 1) : d2540 p ≤ (0 : Int) + d330 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2540, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34585 p hg
    simpa only [d2540, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2540, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d2540, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42052 (p : Pattern) (guard : d8086 p = 1) : d2540 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42051 p hg
    simpa only [d8086, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41899 p hg
    simpa only [d8086, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42053 (p : Pattern) (guard : d8091 p = 1) : d2569 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d2569, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42052 p hg
    simpa only [d8091, d2569, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d2569, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41902 p hg
    simpa only [d8091, d2569, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42054 (p : Pattern) (guard : d8096 p = 1) : d2611 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d2611, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42053 p hg
    simpa only [d8096, d2611, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d2611, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41996 p hg
    simpa only [d8096, d2611, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42055 (p : Pattern) (guard : d8102 p = 1) : d2614 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d2614, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42054 p hg
    simpa only [d8102, d2614, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d2614, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42004 p hg
    simpa only [d8102, d2614, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42056 (p : Pattern) (guard : d8108 p = 1) : d2615 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d2615, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42055 p hg
    simpa only [d8108, d2615, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d2615, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42009 p hg
    simpa only [d8108, d2615, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42057 (p : Pattern) (guard : d8114 p = 1) : d2616 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d2616, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42056 p hg
    simpa only [d8114, d2616, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d2616, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34577 p hg
    simpa only [d8114, d2616, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42058 (p : Pattern) (guard : d8115 p = 1) : d2617 p ≤ (0 : Int) + d406 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8109 p = 1 := by simpa only [d8115, d2617, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42050 p hg
    simpa only [d8115, d2617, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8114 p = 1 := by simpa only [d8115, d2617, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42057 p hg
    simpa only [d8115, d2617, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42059 (p : Pattern) (guard : d8086 p = 1) : d2504 p ≤ (0 : Int) + d366 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41842 p hg
    simpa only [d8086, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41851 p hg
    simpa only [d8086, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42060 (p : Pattern) (guard : d8091 p = 1) : d2518 p ≤ (0 : Int) + d367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d2518, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42059 p hg
    simpa only [d8091, d2518, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d2518, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41854 p hg
    simpa only [d8091, d2518, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42061 (p : Pattern) (guard : d8096 p = 1) : d2601 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d2601, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42060 p hg
    simpa only [d8096, d2601, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d2601, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41978 p hg
    simpa only [d8096, d2601, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42062 (p : Pattern) (guard : d8085 p = 1) : d2540 p ≤ (0 : Int) + d357 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d2540, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38598 p hg
    simpa only [d8085, d2540, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d2540, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41787 p hg
    simpa only [d8085, d2540, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42063 (p : Pattern) (guard : d8090 p = 1) : d2540 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42062 p hg
    simpa only [d8090, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41946 p hg
    simpa only [d8090, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42064 (p : Pattern) (guard : d8095 p = 1) : d2569 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2569, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42063 p hg
    simpa only [d8095, d2569, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2569, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41949 p hg
    simpa only [d8095, d2569, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42065 (p : Pattern) (guard : d8101 p = 1) : d2611 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2611, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42064 p hg
    simpa only [d8101, d2611, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2611, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42019 p hg
    simpa only [d8101, d2611, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42066 (p : Pattern) (guard : d8102 p = 1) : d2618 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d2618, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42061 p hg
    simpa only [d8102, d2618, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d2618, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42065 p hg
    simpa only [d8102, d2618, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42067 (p : Pattern) (guard : d8085 p = 1) : d2520 p ≤ (0 : Int) + d330 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d2520, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34625 p hg
    simpa only [d8085, d2520, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d2520, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41787 p hg
    simpa only [d8085, d2520, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42068 (p : Pattern) (guard : d8090 p = 1) : d2520 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42067 p hg
    simpa only [d8090, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41869 p hg
    simpa only [d8090, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42069 (p : Pattern) (guard : d8095 p = 1) : d2523 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2523, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42068 p hg
    simpa only [d8095, d2523, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2523, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41872 p hg
    simpa only [d8095, d2523, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42070 (p : Pattern) (guard : d8101 p = 1) : d2603 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2603, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42069 p hg
    simpa only [d8101, d2603, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2603, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41982 p hg
    simpa only [d8101, d2603, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42071 (p : Pattern) (guard : d8107 p = 1) : d2619 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2619, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42070 p hg
    simpa only [d8107, d2619, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2619, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42027 p hg
    simpa only [d8107, d2619, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42072 (p : Pattern) (guard : d8108 p = 1) : d2620 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d2620, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42066 p hg
    simpa only [d8108, d2620, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d2620, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42071 p hg
    simpa only [d8108, d2620, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42073 (p : Pattern) (guard : d8107 p = 1) : d2621 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2621, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42025 p hg
    simpa only [d8107, d2621, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2621, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42031 p hg
    simpa only [d8107, d2621, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42074 (p : Pattern) (guard : d8113 p = 1) : d2622 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2622, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42073 p hg
    simpa only [d8113, d2622, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2622, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42035 p hg
    simpa only [d8113, d2622, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42075 (p : Pattern) (guard : d8114 p = 1) : d2623 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d2623, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42072 p hg
    simpa only [d8114, d2623, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d2623, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42074 p hg
    simpa only [d8114, d2623, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42076 (p : Pattern) (guard : d8120 p = 1) : d2627 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d2627, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42075 p hg
    simpa only [d8120, d2627, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d2627, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42040 p hg
    simpa only [d8120, d2627, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42077 (p : Pattern) (guard : d8121 p = 1) : d2628 p ≤ (0 : Int) + d408 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8115 p = 1 := by simpa only [d8121, d2628, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42058 p hg
    simpa only [d8121, d2628, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8120 p = 1 := by simpa only [d8121, d2628, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42076 p hg
    simpa only [d8121, d2628, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42078 (p : Pattern) (guard : d8095 p = 1) : d2606 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41833 p hg
    simpa only [d8095, d2606, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34367 p hg
    simpa only [d8095, d2606, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42079 (p : Pattern) (guard : d8096 p = 1) : d2607 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d2607, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41834 p hg
    simpa only [d8096, d2607, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d2607, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42078 p hg
    simpa only [d8096, d2607, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42080 (p : Pattern) (guard : d8102 p = 1) : d2630 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d2630, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42079 p hg
    simpa only [d8102, d2630, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d2630, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42008 p hg
    simpa only [d8102, d2630, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42081 (p : Pattern) (guard : d8108 p = 1) : d2631 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d2631, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42080 p hg
    simpa only [d8108, d2631, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d2631, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42009 p hg
    simpa only [d8108, d2631, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42082 (p : Pattern) (guard : d8113 p = 1) : d2632 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42009 p hg
    simpa only [d8113, d2632, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34611 p hg
    simpa only [d8113, d2632, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42083 (p : Pattern) (guard : d8114 p = 1) : d2633 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d2633, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42081 p hg
    simpa only [d8114, d2633, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d2633, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42082 p hg
    simpa only [d8114, d2633, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42084 (p : Pattern) (guard : d8119 p = 1) : d2634 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d2634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42082 p hg
    simpa only [d8119, d2634, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d2634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34613 p hg
    simpa only [d8119, d2634, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42085 (p : Pattern) (guard : d8120 p = 1) : d2635 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d2635, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42083 p hg
    simpa only [d8120, d2635, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d2635, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42084 p hg
    simpa only [d8120, d2635, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42086 (p : Pattern) (guard : d8113 p = 1) : d2632 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2632, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41939 p hg
    simpa only [d8113, d2632, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2632, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34611 p hg
    simpa only [d8113, d2632, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42087 (p : Pattern) (guard : d8119 p = 1) : d2634 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d2634, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42086 p hg
    simpa only [d8119, d2634, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d2634, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34613 p hg
    simpa only [d8119, d2634, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42088 (p : Pattern) (guard : d8125 p = 1) : d2636 p ≤ (0 : Int) + d411 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d2636, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42087 p hg
    simpa only [d8125, d2636, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d2636, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36298 p hg
    simpa only [d8125, d2636, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42089 (p : Pattern) (guard : d8126 p = 1) : d2637 p ≤ (0 : Int) + d412 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d2637, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42085 p hg
    simpa only [d8126, d2637, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d2637, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42088 p hg
    simpa only [d8126, d2637, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42090 (p : Pattern) (guard : d8127 p = 1) : d2638 p ≤ (0 : Int) + d413 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8121 p = 1 := by simpa only [d8127, d2638, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42077 p hg
    simpa only [d8127, d2638, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8126 p = 1 := by simpa only [d8127, d2638, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42089 p hg
    simpa only [d8127, d2638, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42091 (p : Pattern) (guard : d8128 p = 1) : d2639 p ≤ (0 : Int) + d414 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8122 p = 1 := by simpa only [d8128, d2639, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42043 p hg
    simpa only [d8128, d2639, d414, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8127 p = 1 := by simpa only [d8128, d2639, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42090 p hg
    simpa only [d8128, d2639, d414, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42092 (p : Pattern) (guard : d8089 p = 1) : d2509 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d2509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38345 p hg
    simpa only [d8089, d2509, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d2509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d8089, d2509, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42093 (p : Pattern) (guard : d8090 p = 1) : d2510 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d2510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41851 p hg
    simpa only [d8090, d2510, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d2510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42092 p hg
    simpa only [d8090, d2510, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42094 (p : Pattern) (guard : d8095 p = 1) : d2511 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42093 p hg
    simpa only [d8095, d2511, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34367 p hg
    simpa only [d8095, d2511, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42095 (p : Pattern) (guard : d8096 p = 1) : d2519 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d2519, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42060 p hg
    simpa only [d8096, d2519, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d2519, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42094 p hg
    simpa only [d8096, d2519, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42096 (p : Pattern) (guard : d8097 p = 1) : d2640 p ≤ (0 : Int) + d415 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8092 p = 1 := by simpa only [d8097, d2640, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41794 p hg
    simpa only [d8097, d2640, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8096 p = 1 := by simpa only [d8097, d2640, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42095 p hg
    simpa only [d8097, d2640, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42097 (p : Pattern) (guard : d8096 p = 1) : d2519 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d2519, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42014 p hg
    simpa only [d8096, d2519, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d2519, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42094 p hg
    simpa only [d8096, d2519, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42098 (p : Pattern) (guard : d5854 p = 1) : d2524 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d2524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38361 p hg
    simpa only [d5854, d2524, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d2524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5854, d2524, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42099 (p : Pattern) (guard : d8094 p = 1) : d2525 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d2525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41869 p hg
    simpa only [d8094, d2525, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d2525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42098 p hg
    simpa only [d8094, d2525, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42100 (p : Pattern) (guard : d8100 p = 1) : d2526 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42099 p hg
    simpa only [d8100, d2526, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d2526, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42101 (p : Pattern) (guard : d8101 p = 1) : d2527 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2527, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42069 p hg
    simpa only [d8101, d2527, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2527, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42100 p hg
    simpa only [d8101, d2527, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42102 (p : Pattern) (guard : d8102 p = 1) : d2528 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d2528, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42097 p hg
    simpa only [d8102, d2528, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d2528, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42101 p hg
    simpa only [d8102, d2528, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42103 (p : Pattern) (guard : d8103 p = 1) : d2641 p ≤ (0 : Int) + d416 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8097 p = 1 := by simpa only [d8103, d2641, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42096 p hg
    simpa only [d8103, d2641, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8102 p = 1 := by simpa only [d8103, d2641, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42102 p hg
    simpa only [d8103, d2641, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42104 (p : Pattern) (guard : d8096 p = 1) : d2519 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d2519, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41943 p hg
    simpa only [d8096, d2519, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d2519, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42094 p hg
    simpa only [d8096, d2519, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42105 (p : Pattern) (guard : d8101 p = 1) : d2527 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2527, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42024 p hg
    simpa only [d8101, d2527, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2527, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42100 p hg
    simpa only [d8101, d2527, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42106 (p : Pattern) (guard : d8102 p = 1) : d2528 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d2528, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42104 p hg
    simpa only [d8102, d2528, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d2528, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42105 p hg
    simpa only [d8102, d2528, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42107 (p : Pattern) (guard : d8101 p = 1) : d2536 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41885 p hg
    simpa only [d8101, d2536, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41918 p hg
    simpa only [d8101, d2536, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42108 (p : Pattern) (guard : d8107 p = 1) : d2537 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42107 p hg
    simpa only [d8107, d2537, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34455 p hg
    simpa only [d8107, d2537, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42109 (p : Pattern) (guard : d8108 p = 1) : d2538 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d2538, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42106 p hg
    simpa only [d8108, d2538, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d2538, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42108 p hg
    simpa only [d8108, d2538, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42110 (p : Pattern) (guard : d8109 p = 1) : d2642 p ≤ (0 : Int) + d417 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8103 p = 1 := by simpa only [d8109, d2642, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42103 p hg
    simpa only [d8109, d2642, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8108 p = 1 := by simpa only [d8109, d2642, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42109 p hg
    simpa only [d8109, d2642, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42111 (p : Pattern) (guard : d8096 p = 1) : d2544 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d2544, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41855 p hg
    simpa only [d8096, d2544, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d2544, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41996 p hg
    simpa only [d8096, d2544, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42112 (p : Pattern) (guard : d8089 p = 1) : d2504 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d2504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34339 p hg
    simpa only [d8089, d2504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d2504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d8089, d2504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42113 (p : Pattern) (guard : d8090 p = 1) : d2504 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41851 p hg
    simpa only [d8090, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42112 p hg
    simpa only [d8090, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42114 (p : Pattern) (guard : d5854 p = 1) : d2506 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d2506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38701 p hg
    simpa only [d5854, d2506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d2506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5854, d2506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42115 (p : Pattern) (guard : d8094 p = 1) : d2507 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d2507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42112 p hg
    simpa only [d8094, d2507, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d2507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42114 p hg
    simpa only [d8094, d2507, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42116 (p : Pattern) (guard : d8095 p = 1) : d2518 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42113 p hg
    simpa only [d8095, d2518, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42115 p hg
    simpa only [d8095, d2518, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42117 (p : Pattern) (guard : d8101 p = 1) : d2549 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42116 p hg
    simpa only [d8101, d2549, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42003 p hg
    simpa only [d8101, d2549, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42118 (p : Pattern) (guard : d8102 p = 1) : d2550 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d2550, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42111 p hg
    simpa only [d8102, d2550, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d2550, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42117 p hg
    simpa only [d8102, d2550, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42119 (p : Pattern) (guard : d8101 p = 1) : d2554 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42116 p hg
    simpa only [d8101, d2554, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41937 p hg
    simpa only [d8101, d2554, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42120 (p : Pattern) (guard : d5854 p = 1) : d2520 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d2520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34363 p hg
    simpa only [d5854, d2520, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d2520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5854, d2520, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42121 (p : Pattern) (guard : d8094 p = 1) : d2520 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41869 p hg
    simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42120 p hg
    simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42122 (p : Pattern) (guard : d8099 p = 1) : d2522 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d2522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42120 p hg
    simpa only [d8099, d2522, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d2522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21655 p hg
    simpa only [d8099, d2522, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42123 (p : Pattern) (guard : d8100 p = 1) : d2523 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42121 p hg
    simpa only [d8100, d2523, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42122 p hg
    simpa only [d8100, d2523, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42124 (p : Pattern) (guard : d8106 p = 1) : d2555 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42123 p hg
    simpa only [d8106, d2555, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34532 p hg
    simpa only [d8106, d2555, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42125 (p : Pattern) (guard : d8107 p = 1) : d2556 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42119 p hg
    simpa only [d8107, d2556, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42124 p hg
    simpa only [d8107, d2556, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42126 (p : Pattern) (guard : d8108 p = 1) : d2557 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d2557, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42118 p hg
    simpa only [d8108, d2557, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d2557, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42125 p hg
    simpa only [d8108, d2557, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42127 (p : Pattern) (guard : d8101 p = 1) : d2558 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42116 p hg
    simpa only [d8101, d2558, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34443 p hg
    simpa only [d8101, d2558, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42128 (p : Pattern) (guard : d8107 p = 1) : d2559 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42127 p hg
    simpa only [d8107, d2559, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42124 p hg
    simpa only [d8107, d2559, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42129 (p : Pattern) (guard : d8112 p = 1) : d2561 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41957 p hg
    simpa only [d8112, d2561, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34543 p hg
    simpa only [d8112, d2561, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42130 (p : Pattern) (guard : d8113 p = 1) : d2562 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42128 p hg
    simpa only [d8113, d2562, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42129 p hg
    simpa only [d8113, d2562, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42131 (p : Pattern) (guard : d8114 p = 1) : d2563 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d2563, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42126 p hg
    simpa only [d8114, d2563, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d2563, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42130 p hg
    simpa only [d8114, d2563, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42132 (p : Pattern) (guard : d8115 p = 1) : d2643 p ≤ (0 : Int) + d418 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8109 p = 1 := by simpa only [d8115, d2643, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42110 p hg
    simpa only [d8115, d2643, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8114 p = 1 := by simpa only [d8115, d2643, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42131 p hg
    simpa only [d8115, d2643, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42133 (p : Pattern) (guard : d8086 p = 1) : d2504 p ≤ (0 : Int) + d350 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41818 p hg
    simpa only [d8086, d350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41851 p hg
    simpa only [d8086, d350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42134 (p : Pattern) (guard : d8091 p = 1) : d2518 p ≤ (0 : Int) + d351 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d2518, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42133 p hg
    simpa only [d8091, d2518, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d2518, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41854 p hg
    simpa only [d8091, d2518, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42135 (p : Pattern) (guard : d8096 p = 1) : d2519 p ≤ (0 : Int) + d352 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d2519, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42134 p hg
    simpa only [d8096, d2519, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d2519, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42094 p hg
    simpa only [d8096, d2519, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42136 (p : Pattern) (guard : d8085 p = 1) : d2540 p ≤ (0 : Int) + d320 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d2540, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34657 p hg
    simpa only [d8085, d2540, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d2540, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41787 p hg
    simpa only [d8085, d2540, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42137 (p : Pattern) (guard : d8090 p = 1) : d2540 p ≤ (0 : Int) + d321 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42136 p hg
    simpa only [d8090, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41946 p hg
    simpa only [d8090, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42138 (p : Pattern) (guard : d8095 p = 1) : d2569 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2569, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42137 p hg
    simpa only [d8095, d2569, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2569, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41949 p hg
    simpa only [d8095, d2569, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42139 (p : Pattern) (guard : d5854 p = 1) : d2570 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d2570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38432 p hg
    simpa only [d5854, d2570, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d2570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5854, d2570, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
