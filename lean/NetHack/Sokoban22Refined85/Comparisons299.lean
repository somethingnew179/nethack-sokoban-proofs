/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons298
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare41860 (p : Pattern) (guard : d8096 p = 1) : d2549 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d2549, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41855 p hg
    simpa only [d8096, d2549, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d2549, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41859 p hg
    simpa only [d8096, d2549, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41861 (p : Pattern) (guard : d8097 p = 1) : d2550 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8092 p = 1 := by simpa only [d8097, d2550, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41849 p hg
    simpa only [d8097, d2550, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8096 p = 1 := by simpa only [d8097, d2550, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41860 p hg
    simpa only [d8097, d2550, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41862 (p : Pattern) (guard : d8086 p = 1) : d2504 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41784 p hg
    simpa only [d8086, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41851 p hg
    simpa only [d8086, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41863 (p : Pattern) (guard : d8091 p = 1) : d2518 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d2518, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41862 p hg
    simpa only [d8091, d2518, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d2518, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41854 p hg
    simpa only [d8091, d2518, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41864 (p : Pattern) (guard : d8085 p = 1) : d2551 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d2551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare711 p hg
    simpa only [d8085, d2551, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d2551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41787 p hg
    simpa only [d8085, d2551, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41865 (p : Pattern) (guard : d8089 p = 1) : d332 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36009 p hg
    simpa only [d8089, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d8089, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41866 (p : Pattern) (guard : d8090 p = 1) : d2552 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d2552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41864 p hg
    simpa only [d8090, d2552, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d2552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41865 p hg
    simpa only [d8090, d2552, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41867 (p : Pattern) (guard : d8095 p = 1) : d2553 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41866 p hg
    simpa only [d8095, d2553, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34367 p hg
    simpa only [d8095, d2553, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41868 (p : Pattern) (guard : d8096 p = 1) : d2554 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d2554, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41863 p hg
    simpa only [d8096, d2554, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d2554, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41867 p hg
    simpa only [d8096, d2554, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41869 (p : Pattern) (guard : d8089 p = 1) : d2520 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d2520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34359 p hg
    simpa only [d8089, d2520, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d2520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d8089, d2520, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41870 (p : Pattern) (guard : d8090 p = 1) : d2520 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41805 p hg
    simpa only [d8090, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41869 p hg
    simpa only [d8090, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41871 (p : Pattern) (guard : d5854 p = 1) : d2521 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d2521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38505 p hg
    simpa only [d5854, d2521, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d2521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5854, d2521, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41872 (p : Pattern) (guard : d8094 p = 1) : d2522 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d2522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41869 p hg
    simpa only [d8094, d2522, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d2522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41871 p hg
    simpa only [d8094, d2522, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41873 (p : Pattern) (guard : d8095 p = 1) : d2523 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41870 p hg
    simpa only [d8095, d2523, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41872 p hg
    simpa only [d8095, d2523, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41874 (p : Pattern) (guard : d8101 p = 1) : d2555 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41873 p hg
    simpa only [d8101, d2555, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34443 p hg
    simpa only [d8101, d2555, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41875 (p : Pattern) (guard : d8102 p = 1) : d2556 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d2556, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41868 p hg
    simpa only [d8102, d2556, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d2556, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41874 p hg
    simpa only [d8102, d2556, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41876 (p : Pattern) (guard : d8103 p = 1) : d2557 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8097 p = 1 := by simpa only [d8103, d2557, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41861 p hg
    simpa only [d8103, d2557, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8102 p = 1 := by simpa only [d8103, d2557, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41875 p hg
    simpa only [d8103, d2557, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41877 (p : Pattern) (guard : d8086 p = 1) : d2504 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41786 p hg
    simpa only [d8086, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41851 p hg
    simpa only [d8086, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41878 (p : Pattern) (guard : d8091 p = 1) : d2518 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d2518, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41877 p hg
    simpa only [d8091, d2518, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d2518, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41854 p hg
    simpa only [d8091, d2518, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41879 (p : Pattern) (guard : d8096 p = 1) : d2558 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d2558, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41878 p hg
    simpa only [d8096, d2558, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d2558, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34448 p hg
    simpa only [d8096, d2558, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41880 (p : Pattern) (guard : d8102 p = 1) : d2559 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d2559, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41879 p hg
    simpa only [d8102, d2559, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d2559, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41874 p hg
    simpa only [d8102, d2559, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41881 (p : Pattern) (guard : d8089 p = 1) : d2530 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d2530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34389 p hg
    simpa only [d8089, d2530, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d2530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d8089, d2530, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41882 (p : Pattern) (guard : d8090 p = 1) : d2530 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41830 p hg
    simpa only [d8090, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41881 p hg
    simpa only [d8090, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41883 (p : Pattern) (guard : d5854 p = 1) : d357 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35956 p hg
    simpa only [d5854, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5854, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41884 (p : Pattern) (guard : d8094 p = 1) : d2531 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d2531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41881 p hg
    simpa only [d8094, d2531, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d2531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41883 p hg
    simpa only [d8094, d2531, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41885 (p : Pattern) (guard : d8095 p = 1) : d2532 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41882 p hg
    simpa only [d8095, d2532, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41884 p hg
    simpa only [d8095, d2532, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41886 (p : Pattern) (guard : d8101 p = 1) : d2560 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41885 p hg
    simpa only [d8101, d2560, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34443 p hg
    simpa only [d8101, d2560, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41887 (p : Pattern) (guard : d8107 p = 1) : d2561 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41886 p hg
    simpa only [d8107, d2561, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34455 p hg
    simpa only [d8107, d2561, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41888 (p : Pattern) (guard : d8108 p = 1) : d2562 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d2562, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41880 p hg
    simpa only [d8108, d2562, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d2562, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41887 p hg
    simpa only [d8108, d2562, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41889 (p : Pattern) (guard : d8109 p = 1) : d2563 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8103 p = 1 := by simpa only [d8109, d2563, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41876 p hg
    simpa only [d8109, d2563, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8108 p = 1 := by simpa only [d8109, d2563, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41888 p hg
    simpa only [d8109, d2563, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41890 (p : Pattern) (guard : d8110 p = 1) : d2564 p ≤ (0 : Int) + d377 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8104 p = 1 := by simpa only [d8110, d2564, d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41841 p hg
    simpa only [d8110, d2564, d377, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8109 p = 1 := by simpa only [d8110, d2564, d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41889 p hg
    simpa only [d8110, d2564, d377, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41891 (p : Pattern) (guard : d1 p = 1) : d2565 p ≤ (0 : Int) + d380 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2565, d380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34461 p hg
    simpa only [d2565, d380, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2565, d380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17176 p hg
    simpa only [d2565, d380, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41892 (p : Pattern) (guard : d1 p = 1) : d2566 p ≤ (0 : Int) + d381 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2566, d381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41891 p hg
    simpa only [d2566, d381, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2566, d381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41850 p hg
    simpa only [d2566, d381, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41893 (p : Pattern) (guard : d8086 p = 1) : d2507 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d2507, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41784 p hg
    simpa only [d8086, d2507, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d2507, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41788 p hg
    simpa only [d8086, d2507, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41894 (p : Pattern) (guard : d8087 p = 1) : d2567 p ≤ (0 : Int) + d382 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8087, d2567, d382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41892 p hg
    simpa only [d8087, d2567, d382, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8086 p = 1 := by simpa only [d8087, d2567, d382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41893 p hg
    simpa only [d8087, d2567, d382, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41895 (p : Pattern) (guard : d8086 p = 1) : d2510 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d2510, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41850 p hg
    simpa only [d8086, d2510, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d2510, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41791 p hg
    simpa only [d8086, d2510, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41896 (p : Pattern) (guard : d8091 p = 1) : d2511 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d2511, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41895 p hg
    simpa only [d8091, d2511, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d2511, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34344 p hg
    simpa only [d8091, d2511, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41897 (p : Pattern) (guard : d8092 p = 1) : d2568 p ≤ (0 : Int) + d383 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8087 p = 1 := by simpa only [d8092, d2568, d383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41894 p hg
    simpa only [d8092, d2568, d383, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8091 p = 1 := by simpa only [d8092, d2568, d383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41896 p hg
    simpa only [d8092, d2568, d383, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41898 (p : Pattern) (guard : d1 p = 1) : d2540 p ≤ (0 : Int) + d349 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2540, d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34468 p hg
    simpa only [d2540, d349, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2540, d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d2540, d349, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41899 (p : Pattern) (guard : d8085 p = 1) : d2540 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d2540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1508 p hg
    simpa only [d8085, d2540, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d2540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41787 p hg
    simpa only [d8085, d2540, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41900 (p : Pattern) (guard : d8086 p = 1) : d2540 p ≤ (0 : Int) + d350 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41898 p hg
    simpa only [d8086, d350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41899 p hg
    simpa only [d8086, d350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41901 (p : Pattern) (guard : d8089 p = 1) : d2541 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d2541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38524 p hg
    simpa only [d8089, d2541, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d2541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d8089, d2541, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41902 (p : Pattern) (guard : d8090 p = 1) : d2542 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d2542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41899 p hg
    simpa only [d8090, d2542, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d2542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41901 p hg
    simpa only [d8090, d2542, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41903 (p : Pattern) (guard : d8091 p = 1) : d2569 p ≤ (0 : Int) + d351 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d2569, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41900 p hg
    simpa only [d8091, d2569, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d2569, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41902 p hg
    simpa only [d8091, d2569, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41904 (p : Pattern) (guard : d8089 p = 1) : d2570 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d2570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38429 p hg
    simpa only [d8089, d2570, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d2570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d8089, d2570, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41905 (p : Pattern) (guard : d8090 p = 1) : d2571 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d2571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41899 p hg
    simpa only [d8090, d2571, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d2571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41904 p hg
    simpa only [d8090, d2571, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41906 (p : Pattern) (guard : d8095 p = 1) : d2572 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41905 p hg
    simpa only [d8095, d2572, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34367 p hg
    simpa only [d8095, d2572, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41907 (p : Pattern) (guard : d8096 p = 1) : d2573 p ≤ (0 : Int) + d352 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d2573, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41903 p hg
    simpa only [d8096, d2573, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d2573, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41906 p hg
    simpa only [d8096, d2573, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41908 (p : Pattern) (guard : d8097 p = 1) : d2574 p ≤ (0 : Int) + d384 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8092 p = 1 := by simpa only [d8097, d2574, d384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41897 p hg
    simpa only [d8097, d2574, d384, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8096 p = 1 := by simpa only [d8097, d2574, d384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41907 p hg
    simpa only [d8097, d2574, d384, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41909 (p : Pattern) (guard : d1 p = 1) : d2520 p ≤ (0 : Int) + d365 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2520, d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34480 p hg
    simpa only [d2520, d365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2520, d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d2520, d365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41910 (p : Pattern) (guard : d8086 p = 1) : d2520 p ≤ (0 : Int) + d366 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41909 p hg
    simpa only [d8086, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41805 p hg
    simpa only [d8086, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41911 (p : Pattern) (guard : d8091 p = 1) : d2523 p ≤ (0 : Int) + d367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d2523, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41910 p hg
    simpa only [d8091, d2523, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d2523, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41810 p hg
    simpa only [d8091, d2523, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41912 (p : Pattern) (guard : d8096 p = 1) : d2527 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d2527, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41911 p hg
    simpa only [d8096, d2527, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d2527, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41814 p hg
    simpa only [d8096, d2527, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41913 (p : Pattern) (guard : d8085 p = 1) : d2530 p ≤ (0 : Int) + d357 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d2530, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34386 p hg
    simpa only [d8085, d2530, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d2530, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41787 p hg
    simpa only [d8085, d2530, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41914 (p : Pattern) (guard : d8090 p = 1) : d2530 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41913 p hg
    simpa only [d8090, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41881 p hg
    simpa only [d8090, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41915 (p : Pattern) (guard : d8095 p = 1) : d2532 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2532, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41914 p hg
    simpa only [d8095, d2532, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2532, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41884 p hg
    simpa only [d8095, d2532, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41916 (p : Pattern) (guard : d5854 p = 1) : d2533 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d2533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38381 p hg
    simpa only [d5854, d2533, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d2533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5854, d2533, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41917 (p : Pattern) (guard : d8094 p = 1) : d2534 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d2534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41881 p hg
    simpa only [d8094, d2534, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d2534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41916 p hg
    simpa only [d8094, d2534, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41918 (p : Pattern) (guard : d8100 p = 1) : d2535 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41917 p hg
    simpa only [d8100, d2535, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d2535, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41919 (p : Pattern) (guard : d8101 p = 1) : d2536 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2536, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41915 p hg
    simpa only [d8101, d2536, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2536, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41918 p hg
    simpa only [d8101, d2536, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41920 (p : Pattern) (guard : d8102 p = 1) : d2575 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d2575, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41912 p hg
    simpa only [d8102, d2575, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d2575, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41919 p hg
    simpa only [d8102, d2575, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41921 (p : Pattern) (guard : d8103 p = 1) : d2576 p ≤ (0 : Int) + d385 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8097 p = 1 := by simpa only [d8103, d2576, d385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41908 p hg
    simpa only [d8103, d2576, d385, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8102 p = 1 := by simpa only [d8103, d2576, d385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41920 p hg
    simpa only [d8103, d2576, d385, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41922 (p : Pattern) (guard : d8085 p = 1) : d2577 p ≤ (0 : Int) + d330 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d2577, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34493 p hg
    simpa only [d8085, d2577, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d2577, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41787 p hg
    simpa only [d8085, d2577, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41923 (p : Pattern) (guard : d8089 p = 1) : d2577 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d2577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34495 p hg
    simpa only [d8089, d2577, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d2577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d8089, d2577, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41924 (p : Pattern) (guard : d8090 p = 1) : d2577 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41922 p hg
    simpa only [d8090, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41923 p hg
    simpa only [d8090, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41925 (p : Pattern) (guard : d5854 p = 1) : d330 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36095 p hg
    simpa only [d5854, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5854, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41926 (p : Pattern) (guard : d8094 p = 1) : d2578 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d2578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41923 p hg
    simpa only [d8094, d2578, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d2578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41925 p hg
    simpa only [d8094, d2578, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41927 (p : Pattern) (guard : d8095 p = 1) : d2579 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2579, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41924 p hg
    simpa only [d8095, d2579, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2579, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41926 p hg
    simpa only [d8095, d2579, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41928 (p : Pattern) (guard : d8100 p = 1) : d2580 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41926 p hg
    simpa only [d8100, d2580, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d2580, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41929 (p : Pattern) (guard : d8101 p = 1) : d2581 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2581, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41927 p hg
    simpa only [d8101, d2581, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2581, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41928 p hg
    simpa only [d8101, d2581, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41930 (p : Pattern) (guard : d8102 p = 1) : d2582 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d2582, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41815 p hg
    simpa only [d8102, d2582, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d2582, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41929 p hg
    simpa only [d8102, d2582, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41931 (p : Pattern) (guard : d8085 p = 1) : d2551 p ≤ (0 : Int) + d332 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d2551, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34507 p hg
    simpa only [d8085, d2551, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d2551, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41787 p hg
    simpa only [d8085, d2551, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41932 (p : Pattern) (guard : d8089 p = 1) : d2551 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d2551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34432 p hg
    simpa only [d8089, d2551, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d2551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d8089, d2551, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41933 (p : Pattern) (guard : d8090 p = 1) : d2551 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41931 p hg
    simpa only [d8090, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41932 p hg
    simpa only [d8090, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41934 (p : Pattern) (guard : d5854 p = 1) : d332 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36011 p hg
    simpa only [d5854, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5854, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41935 (p : Pattern) (guard : d8094 p = 1) : d2552 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d2552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41932 p hg
    simpa only [d8094, d2552, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d2552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41934 p hg
    simpa only [d8094, d2552, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41936 (p : Pattern) (guard : d8095 p = 1) : d2583 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2583, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41933 p hg
    simpa only [d8095, d2583, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2583, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41935 p hg
    simpa only [d8095, d2583, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41937 (p : Pattern) (guard : d8100 p = 1) : d2553 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41935 p hg
    simpa only [d8100, d2553, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d2553, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41938 (p : Pattern) (guard : d8101 p = 1) : d2584 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2584, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41936 p hg
    simpa only [d8101, d2584, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2584, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41937 p hg
    simpa only [d8101, d2584, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41939 (p : Pattern) (guard : d8107 p = 1) : d2585 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2585, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41938 p hg
    simpa only [d8107, d2585, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2585, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34455 p hg
    simpa only [d8107, d2585, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41940 (p : Pattern) (guard : d8108 p = 1) : d2586 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d2586, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41930 p hg
    simpa only [d8108, d2586, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d2586, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41939 p hg
    simpa only [d8108, d2586, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41941 (p : Pattern) (guard : d8109 p = 1) : d2587 p ≤ (0 : Int) + d388 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8103 p = 1 := by simpa only [d8109, d2587, d388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41921 p hg
    simpa only [d8109, d2587, d388, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8108 p = 1 := by simpa only [d8109, d2587, d388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41940 p hg
    simpa only [d8109, d2587, d388, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41942 (p : Pattern) (guard : d8086 p = 1) : d2504 p ≤ (0 : Int) + d321 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41775 p hg
    simpa only [d8086, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41851 p hg
    simpa only [d8086, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41943 (p : Pattern) (guard : d8091 p = 1) : d2518 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d2518, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41942 p hg
    simpa only [d8091, d2518, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d2518, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41854 p hg
    simpa only [d8091, d2518, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41944 (p : Pattern) (guard : d8096 p = 1) : d2549 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d2549, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41943 p hg
    simpa only [d8096, d2549, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d2549, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41859 p hg
    simpa only [d8096, d2549, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41945 (p : Pattern) (guard : d8085 p = 1) : d2540 p ≤ (0 : Int) + d332 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d2540, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34522 p hg
    simpa only [d8085, d2540, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d2540, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41787 p hg
    simpa only [d8085, d2540, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41946 (p : Pattern) (guard : d8089 p = 1) : d2540 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d2540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34408 p hg
    simpa only [d8089, d2540, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d2540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d8089, d2540, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41947 (p : Pattern) (guard : d8090 p = 1) : d2540 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41945 p hg
    simpa only [d8090, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41946 p hg
    simpa only [d8090, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41948 (p : Pattern) (guard : d5854 p = 1) : d2541 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d2541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38548 p hg
    simpa only [d5854, d2541, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d2541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5854, d2541, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41949 (p : Pattern) (guard : d8094 p = 1) : d2542 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d2542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41946 p hg
    simpa only [d8094, d2542, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d2542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41948 p hg
    simpa only [d8094, d2542, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41950 (p : Pattern) (guard : d8095 p = 1) : d2569 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2569, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41947 p hg
    simpa only [d8095, d2569, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2569, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41949 p hg
    simpa only [d8095, d2569, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41951 (p : Pattern) (guard : d8101 p = 1) : d2588 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2588, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41950 p hg
    simpa only [d8101, d2588, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2588, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34443 p hg
    simpa only [d8101, d2588, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41952 (p : Pattern) (guard : d8102 p = 1) : d2589 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d2589, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41944 p hg
    simpa only [d8102, d2589, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d2589, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41951 p hg
    simpa only [d8102, d2589, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41953 (p : Pattern) (guard : d5854 p = 1) : d2530 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d2530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34393 p hg
    simpa only [d5854, d2530, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d2530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5854, d2530, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41954 (p : Pattern) (guard : d8094 p = 1) : d2530 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41881 p hg
    simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41953 p hg
    simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41955 (p : Pattern) (guard : d8099 p = 1) : d2531 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d2531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41953 p hg
    simpa only [d8099, d2531, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d2531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21671 p hg
    simpa only [d8099, d2531, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41956 (p : Pattern) (guard : d8100 p = 1) : d2532 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41954 p hg
    simpa only [d8100, d2532, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41955 p hg
    simpa only [d8100, d2532, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41957 (p : Pattern) (guard : d8106 p = 1) : d2560 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41956 p hg
    simpa only [d8106, d2560, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34532 p hg
    simpa only [d8106, d2560, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41958 (p : Pattern) (guard : d8107 p = 1) : d2590 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41874 p hg
    simpa only [d8107, d2590, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41957 p hg
    simpa only [d8107, d2590, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41959 (p : Pattern) (guard : d8108 p = 1) : d2591 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d2591, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41952 p hg
    simpa only [d8108, d2591, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d2591, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41958 p hg
    simpa only [d8108, d2591, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41960 (p : Pattern) (guard : d5854 p = 1) : d2577 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d2577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34498 p hg
    simpa only [d5854, d2577, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d2577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5854, d2577, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41961 (p : Pattern) (guard : d8094 p = 1) : d2577 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41923 p hg
    simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41960 p hg
    simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41962 (p : Pattern) (guard : d8099 p = 1) : d2578 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d2578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41960 p hg
    simpa only [d8099, d2578, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d2578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21720 p hg
    simpa only [d8099, d2578, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41963 (p : Pattern) (guard : d8100 p = 1) : d2579 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41961 p hg
    simpa only [d8100, d2579, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41962 p hg
    simpa only [d8100, d2579, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41964 (p : Pattern) (guard : d8106 p = 1) : d2592 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41963 p hg
    simpa only [d8106, d2592, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34532 p hg
    simpa only [d8106, d2592, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41965 (p : Pattern) (guard : d8107 p = 1) : d2593 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41874 p hg
    simpa only [d8107, d2593, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41964 p hg
    simpa only [d8107, d2593, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41966 (p : Pattern) (guard : d5854 p = 1) : d2551 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d2551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34435 p hg
    simpa only [d5854, d2551, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d2551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5854, d2551, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41967 (p : Pattern) (guard : d8094 p = 1) : d2551 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41932 p hg
    simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41966 p hg
    simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41968 (p : Pattern) (guard : d8099 p = 1) : d2552 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d2552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41966 p hg
    simpa only [d8099, d2552, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d2552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21690 p hg
    simpa only [d8099, d2552, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41969 (p : Pattern) (guard : d8100 p = 1) : d2583 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41967 p hg
    simpa only [d8100, d2583, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41968 p hg
    simpa only [d8100, d2583, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41970 (p : Pattern) (guard : d8106 p = 1) : d2594 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41969 p hg
    simpa only [d8106, d2594, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34532 p hg
    simpa only [d8106, d2594, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41971 (p : Pattern) (guard : d8112 p = 1) : d2595 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2595, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41970 p hg
    simpa only [d8112, d2595, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2595, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34543 p hg
    simpa only [d8112, d2595, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41972 (p : Pattern) (guard : d8113 p = 1) : d2596 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41965 p hg
    simpa only [d8113, d2596, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41971 p hg
    simpa only [d8113, d2596, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41973 (p : Pattern) (guard : d8114 p = 1) : d2597 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d2597, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41959 p hg
    simpa only [d8114, d2597, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d2597, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41972 p hg
    simpa only [d8114, d2597, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41974 (p : Pattern) (guard : d8115 p = 1) : d2598 p ≤ (0 : Int) + d392 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8109 p = 1 := by simpa only [d8115, d2598, d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41941 p hg
    simpa only [d8115, d2598, d392, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8114 p = 1 := by simpa only [d8115, d2598, d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41973 p hg
    simpa only [d8115, d2598, d392, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41975 (p : Pattern) (guard : d8116 p = 1) : d2599 p ≤ (0 : Int) + d393 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8110 p = 1 := by simpa only [d8116, d2599, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41890 p hg
    simpa only [d8116, d2599, d393, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8115 p = 1 := by simpa only [d8116, d2599, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41974 p hg
    simpa only [d8116, d2599, d393, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41976 (p : Pattern) (guard : d8091 p = 1) : d2600 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d2600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41799 p hg
    simpa only [d8091, d2600, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d2600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34344 p hg
    simpa only [d8091, d2600, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41977 (p : Pattern) (guard : d8092 p = 1) : d2601 p ≤ (0 : Int) + d352 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8087 p = 1 := by simpa only [d8092, d2601, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41820 p hg
    simpa only [d8092, d2601, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8091 p = 1 := by simpa only [d8092, d2601, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41976 p hg
    simpa only [d8092, d2601, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41978 (p : Pattern) (guard : d8095 p = 1) : d2600 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41854 p hg
    simpa only [d8095, d2600, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34367 p hg
    simpa only [d8095, d2600, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41979 (p : Pattern) (guard : d8096 p = 1) : d2601 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d2601, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41943 p hg
    simpa only [d8096, d2601, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d2601, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41978 p hg
    simpa only [d8096, d2601, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41980 (p : Pattern) (guard : d8097 p = 1) : d2601 p ≤ (0 : Int) + d355 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8092 p = 1 := by simpa only [d8097, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41977 p hg
    simpa only [d8097, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8096 p = 1 := by simpa only [d8097, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41979 p hg
    simpa only [d8097, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41981 (p : Pattern) (guard : d8096 p = 1) : d2601 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d2601, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41855 p hg
    simpa only [d8096, d2601, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d2601, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41978 p hg
    simpa only [d8096, d2601, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41982 (p : Pattern) (guard : d8100 p = 1) : d2602 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41872 p hg
    simpa only [d8100, d2602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d2602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41983 (p : Pattern) (guard : d8101 p = 1) : d2603 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41873 p hg
    simpa only [d8101, d2603, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41982 p hg
    simpa only [d8101, d2603, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41984 (p : Pattern) (guard : d8102 p = 1) : d2604 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d2604, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41981 p hg
    simpa only [d8102, d2604, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d2604, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41983 p hg
    simpa only [d8102, d2604, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41985 (p : Pattern) (guard : d8103 p = 1) : d2605 p ≤ (0 : Int) + d362 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8097 p = 1 := by simpa only [d8103, d2605, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41980 p hg
    simpa only [d8103, d2605, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8102 p = 1 := by simpa only [d8103, d2605, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41984 p hg
    simpa only [d8103, d2605, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41986 (p : Pattern) (guard : d8096 p = 1) : d2601 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d2601, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41863 p hg
    simpa only [d8096, d2601, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d2601, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41978 p hg
    simpa only [d8096, d2601, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41987 (p : Pattern) (guard : d8102 p = 1) : d2604 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d2604, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41986 p hg
    simpa only [d8102, d2604, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d2604, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41983 p hg
    simpa only [d8102, d2604, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41988 (p : Pattern) (guard : d8100 p = 1) : d2606 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41884 p hg
    simpa only [d8100, d2606, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d2606, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41989 (p : Pattern) (guard : d8101 p = 1) : d2607 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41885 p hg
    simpa only [d8101, d2607, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41988 p hg
    simpa only [d8101, d2607, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41990 (p : Pattern) (guard : d8107 p = 1) : d2608 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41989 p hg
    simpa only [d8107, d2608, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34455 p hg
    simpa only [d8107, d2608, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41991 (p : Pattern) (guard : d8108 p = 1) : d2609 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d2609, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41987 p hg
    simpa only [d8108, d2609, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d2609, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41990 p hg
    simpa only [d8108, d2609, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41992 (p : Pattern) (guard : d8109 p = 1) : d2610 p ≤ (0 : Int) + d395 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8103 p = 1 := by simpa only [d8109, d2610, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41985 p hg
    simpa only [d8109, d2610, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8108 p = 1 := by simpa only [d8109, d2610, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41991 p hg
    simpa only [d8109, d2610, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41993 (p : Pattern) (guard : d1 p = 1) : d2540 p ≤ (0 : Int) + d332 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2540, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34522 p hg
    simpa only [d2540, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2540, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d2540, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41994 (p : Pattern) (guard : d8086 p = 1) : d2540 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41993 p hg
    simpa only [d8086, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41899 p hg
    simpa only [d8086, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41995 (p : Pattern) (guard : d8091 p = 1) : d2569 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d2569, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41994 p hg
    simpa only [d8091, d2569, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d2569, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41902 p hg
    simpa only [d8091, d2569, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41996 (p : Pattern) (guard : d8095 p = 1) : d2543 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41902 p hg
    simpa only [d8095, d2543, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34367 p hg
    simpa only [d8095, d2543, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41997 (p : Pattern) (guard : d8096 p = 1) : d2611 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d2611, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41995 p hg
    simpa only [d8096, d2611, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d2611, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41996 p hg
    simpa only [d8096, d2611, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41998 (p : Pattern) (guard : d8089 p = 1) : d2545 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d2545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34421 p hg
    simpa only [d8089, d2545, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d2545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d8089, d2545, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41999 (p : Pattern) (guard : d8090 p = 1) : d2545 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41856 p hg
    simpa only [d8090, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41998 p hg
    simpa only [d8090, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
