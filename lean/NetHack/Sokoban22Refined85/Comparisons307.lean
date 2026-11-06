/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons306
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare42980 (p : Pattern) (guard : d8091 p = 1) : d2655 p ≤ (0 : Int) + d432 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d2655, d432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42978 p hg
    simpa only [d8091, d2655, d432, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d2655, d432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42979 p hg
    simpa only [d8091, d2655, d432, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42981 (p : Pattern) (guard : d8090 p = 1) : d2510 p ≤ (0 : Int) + d321 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d2510, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42324 p hg
    simpa only [d8090, d2510, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d2510, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42092 p hg
    simpa only [d8090, d2510, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42982 (p : Pattern) (guard : d8095 p = 1) : d2511 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2511, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42981 p hg
    simpa only [d8095, d2511, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2511, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34367 p hg
    simpa only [d8095, d2511, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42983 (p : Pattern) (guard : d8096 p = 1) : d2656 p ≤ (0 : Int) + d433 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d2656, d433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42980 p hg
    simpa only [d8096, d2656, d433, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d2656, d433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42982 p hg
    simpa only [d8096, d2656, d433, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42984 (p : Pattern) (guard : d8085 p = 1) : d2504 p ≤ (0 : Int) + d340 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d2504, d340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34348 p hg
    simpa only [d8085, d2504, d340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d2504, d340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41787 p hg
    simpa only [d8085, d2504, d340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42985 (p : Pattern) (guard : d8090 p = 1) : d2504 p ≤ (0 : Int) + d341 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42984 p hg
    simpa only [d8090, d341, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42468 p hg
    simpa only [d8090, d341, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42986 (p : Pattern) (guard : d8095 p = 1) : d2518 p ≤ (0 : Int) + d342 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2518, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42985 p hg
    simpa only [d8095, d2518, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2518, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42115 p hg
    simpa only [d8095, d2518, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42987 (p : Pattern) (guard : d8094 p = 1) : d2510 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d2510, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42468 p hg
    simpa only [d8094, d2510, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d2510, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42378 p hg
    simpa only [d8094, d2510, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42988 (p : Pattern) (guard : d8100 p = 1) : d2511 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2511, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42987 p hg
    simpa only [d8100, d2511, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2511, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d2511, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42989 (p : Pattern) (guard : d8101 p = 1) : d2519 p ≤ (0 : Int) + d344 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2519, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42986 p hg
    simpa only [d8101, d2519, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2519, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42988 p hg
    simpa only [d8101, d2519, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42990 (p : Pattern) (guard : d8102 p = 1) : d2657 p ≤ (0 : Int) + d434 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d2657, d434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42983 p hg
    simpa only [d8102, d2657, d434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d2657, d434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42989 p hg
    simpa only [d8102, d2657, d434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42991 (p : Pattern) (guard : d8089 p = 1) : d2520 p ≤ (0 : Int) + d320 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d2520, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35392 p hg
    simpa only [d8089, d2520, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d2520, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d8089, d2520, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42992 (p : Pattern) (guard : d8094 p = 1) : d2520 p ≤ (0 : Int) + d321 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42991 p hg
    simpa only [d8094, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42120 p hg
    simpa only [d8094, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42993 (p : Pattern) (guard : d8100 p = 1) : d2523 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2523, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42992 p hg
    simpa only [d8100, d2523, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2523, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42122 p hg
    simpa only [d8100, d2523, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42994 (p : Pattern) (guard : d8106 p = 1) : d2527 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2527, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42993 p hg
    simpa only [d8106, d2527, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2527, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42385 p hg
    simpa only [d8106, d2527, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42995 (p : Pattern) (guard : d8107 p = 1) : d2528 p ≤ (0 : Int) + d355 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2528, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42614 p hg
    simpa only [d8107, d2528, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2528, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42994 p hg
    simpa only [d8107, d2528, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42996 (p : Pattern) (guard : d8108 p = 1) : d2658 p ≤ (0 : Int) + d435 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d2658, d435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d8108, d2658, d435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d2658, d435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42995 p hg
    simpa only [d8108, d2658, d435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42997 (p : Pattern) (guard : d8107 p = 1) : d2528 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2528, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42417 p hg
    simpa only [d8107, d2528, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2528, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42623 p hg
    simpa only [d8107, d2528, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42998 (p : Pattern) (guard : d8112 p = 1) : d2537 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2537, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42302 p hg
    simpa only [d8112, d2537, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2537, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34543 p hg
    simpa only [d8112, d2537, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42999 (p : Pattern) (guard : d8113 p = 1) : d2538 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2538, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42997 p hg
    simpa only [d8113, d2538, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2538, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42998 p hg
    simpa only [d8113, d2538, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43000 (p : Pattern) (guard : d8114 p = 1) : d2659 p ≤ (0 : Int) + d436 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d2659, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42996 p hg
    simpa only [d8114, d2659, d436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d2659, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42999 p hg
    simpa only [d8114, d2659, d436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43001 (p : Pattern) (guard : d8101 p = 1) : d2544 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2544, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42351 p hg
    simpa only [d8101, d2544, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2544, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42019 p hg
    simpa only [d8101, d2544, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43002 (p : Pattern) (guard : d8106 p = 1) : d2549 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2549, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42495 p hg
    simpa only [d8106, d2549, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2549, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42201 p hg
    simpa only [d8106, d2549, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43003 (p : Pattern) (guard : d8107 p = 1) : d2550 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2550, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43001 p hg
    simpa only [d8107, d2550, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2550, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43002 p hg
    simpa only [d8107, d2550, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43004 (p : Pattern) (guard : d8106 p = 1) : d2554 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2554, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42470 p hg
    simpa only [d8106, d2554, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2554, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42033 p hg
    simpa only [d8106, d2554, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43005 (p : Pattern) (guard : d8112 p = 1) : d2556 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2556, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43004 p hg
    simpa only [d8112, d2556, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2556, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42405 p hg
    simpa only [d8112, d2556, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43006 (p : Pattern) (guard : d8113 p = 1) : d2557 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2557, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43003 p hg
    simpa only [d8113, d2557, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2557, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43005 p hg
    simpa only [d8113, d2557, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43007 (p : Pattern) (guard : d8119 p = 1) : d2563 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d2563, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43006 p hg
    simpa only [d8119, d2563, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d2563, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42411 p hg
    simpa only [d8119, d2563, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43008 (p : Pattern) (guard : d8120 p = 1) : d2660 p ≤ (0 : Int) + d437 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d2660, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43000 p hg
    simpa only [d8120, d2660, d437, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d2660, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43007 p hg
    simpa only [d8120, d2660, d437, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43009 (p : Pattern) (guard : d8085 p = 1) : d2513 p ≤ (0 : Int) + d328 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d2513, d328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34331 p hg
    simpa only [d8085, d2513, d328, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d2513, d328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42740 p hg
    simpa only [d8085, d2513, d328, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43010 (p : Pattern) (guard : d8090 p = 1) : d2514 p ≤ (0 : Int) + d331 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d2514, d331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43009 p hg
    simpa only [d8090, d2514, d331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d2514, d331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42493 p hg
    simpa only [d8090, d2514, d331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43011 (p : Pattern) (guard : d8094 p = 1) : d2507 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d2507, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42468 p hg
    simpa only [d8094, d2507, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d2507, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42114 p hg
    simpa only [d8094, d2507, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43012 (p : Pattern) (guard : d8095 p = 1) : d2515 p ≤ (0 : Int) + d334 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2515, d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43010 p hg
    simpa only [d8095, d2515, d334, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2515, d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43011 p hg
    simpa only [d8095, d2515, d334, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43013 (p : Pattern) (guard : d8094 p = 1) : d2510 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d2510, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42493 p hg
    simpa only [d8094, d2510, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d2510, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42378 p hg
    simpa only [d8094, d2510, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43014 (p : Pattern) (guard : d8100 p = 1) : d2511 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2511, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43013 p hg
    simpa only [d8100, d2511, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2511, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d2511, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43015 (p : Pattern) (guard : d8101 p = 1) : d2516 p ≤ (0 : Int) + d337 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2516, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43012 p hg
    simpa only [d8101, d2516, d337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2516, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43014 p hg
    simpa only [d8101, d2516, d337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43016 (p : Pattern) (guard : d8089 p = 1) : d2540 p ≤ (0 : Int) + d365 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d2540, d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35416 p hg
    simpa only [d8089, d2540, d365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d2540, d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d8089, d2540, d365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43017 (p : Pattern) (guard : d8094 p = 1) : d2540 p ≤ (0 : Int) + d366 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43016 p hg
    simpa only [d8094, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42160 p hg
    simpa only [d8094, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43018 (p : Pattern) (guard : d8100 p = 1) : d2569 p ≤ (0 : Int) + d367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2569, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43017 p hg
    simpa only [d8100, d2569, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2569, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42162 p hg
    simpa only [d8100, d2569, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43019 (p : Pattern) (guard : d8106 p = 1) : d2573 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2573, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43018 p hg
    simpa only [d8106, d2573, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2573, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42422 p hg
    simpa only [d8106, d2573, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43020 (p : Pattern) (guard : d8107 p = 1) : d2661 p ≤ (0 : Int) + d415 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2661, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43015 p hg
    simpa only [d8107, d2661, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2661, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43019 p hg
    simpa only [d8107, d2661, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43021 (p : Pattern) (guard : d8089 p = 1) : d2520 p ≤ (0 : Int) + d318 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d2520, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35422 p hg
    simpa only [d8089, d2520, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d2520, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d8089, d2520, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43022 (p : Pattern) (guard : d8094 p = 1) : d2520 p ≤ (0 : Int) + d323 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43021 p hg
    simpa only [d8094, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42120 p hg
    simpa only [d8094, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43023 (p : Pattern) (guard : d8100 p = 1) : d2523 p ≤ (0 : Int) + d324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2523, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43022 p hg
    simpa only [d8100, d2523, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2523, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42122 p hg
    simpa only [d8100, d2523, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43024 (p : Pattern) (guard : d8106 p = 1) : d2527 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2527, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43023 p hg
    simpa only [d8106, d2527, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2527, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42385 p hg
    simpa only [d8106, d2527, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43025 (p : Pattern) (guard : d5854 p = 1) : d2530 p ≤ (0 : Int) + d330 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d2530, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35428 p hg
    simpa only [d5854, d2530, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d2530, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5854, d2530, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43026 (p : Pattern) (guard : d8099 p = 1) : d2530 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43025 p hg
    simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21669 p hg
    simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43027 (p : Pattern) (guard : d8105 p = 1) : d2532 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d2532, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43026 p hg
    simpa only [d8105, d2532, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d2532, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22570 p hg
    simpa only [d8105, d2532, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43028 (p : Pattern) (guard : d8111 p = 1) : d2536 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2536, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43027 p hg
    simpa only [d8111, d2536, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2536, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42429 p hg
    simpa only [d8111, d2536, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43029 (p : Pattern) (guard : d8112 p = 1) : d2575 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2575, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43024 p hg
    simpa only [d8112, d2575, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2575, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43028 p hg
    simpa only [d8112, d2575, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43030 (p : Pattern) (guard : d8113 p = 1) : d2662 p ≤ (0 : Int) + d416 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2662, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43020 p hg
    simpa only [d8113, d2662, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2662, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43029 p hg
    simpa only [d8113, d2662, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43031 (p : Pattern) (guard : d5854 p = 1) : d2577 p ≤ (0 : Int) + d332 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d2577, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35436 p hg
    simpa only [d5854, d2577, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d2577, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5854, d2577, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43032 (p : Pattern) (guard : d8099 p = 1) : d2577 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43031 p hg
    simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21718 p hg
    simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43033 (p : Pattern) (guard : d8105 p = 1) : d2579 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d2579, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43032 p hg
    simpa only [d8105, d2579, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d2579, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22604 p hg
    simpa only [d8105, d2579, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43034 (p : Pattern) (guard : d8111 p = 1) : d2581 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2581, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43033 p hg
    simpa only [d8111, d2581, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2581, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42218 p hg
    simpa only [d8111, d2581, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43035 (p : Pattern) (guard : d8112 p = 1) : d2582 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2582, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42994 p hg
    simpa only [d8112, d2582, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2582, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43034 p hg
    simpa only [d8112, d2582, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43036 (p : Pattern) (guard : d8118 p = 1) : d2586 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2586, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43035 p hg
    simpa only [d8118, d2586, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2586, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42223 p hg
    simpa only [d8118, d2586, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43037 (p : Pattern) (guard : d8119 p = 1) : d2663 p ≤ (0 : Int) + d417 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d2663, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43030 p hg
    simpa only [d8119, d2663, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d2663, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43036 p hg
    simpa only [d8119, d2663, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43038 (p : Pattern) (guard : d8106 p = 1) : d2549 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2549, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42643 p hg
    simpa only [d8106, d2549, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2549, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42201 p hg
    simpa only [d8106, d2549, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43039 (p : Pattern) (guard : d8112 p = 1) : d2589 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2589, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43038 p hg
    simpa only [d8112, d2589, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2589, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42438 p hg
    simpa only [d8112, d2589, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43040 (p : Pattern) (guard : d8118 p = 1) : d2591 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2591, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43039 p hg
    simpa only [d8118, d2591, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2591, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42441 p hg
    simpa only [d8118, d2591, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43041 (p : Pattern) (guard : d8124 p = 1) : d2597 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d2597, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43040 p hg
    simpa only [d8124, d2597, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d2597, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42446 p hg
    simpa only [d8124, d2597, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43042 (p : Pattern) (guard : d8125 p = 1) : d2664 p ≤ (0 : Int) + d418 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d2664, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43037 p hg
    simpa only [d8125, d2664, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d2664, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43041 p hg
    simpa only [d8125, d2664, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43043 (p : Pattern) (guard : d8126 p = 1) : d2665 p ≤ (0 : Int) + d438 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d2665, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43008 p hg
    simpa only [d8126, d2665, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d2665, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43042 p hg
    simpa only [d8126, d2665, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43044 (p : Pattern) (guard : d8107 p = 1) : d2601 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42579 p hg
    simpa only [d8107, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42644 p hg
    simpa only [d8107, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43045 (p : Pattern) (guard : d8112 p = 1) : d2604 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2604, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42496 p hg
    simpa only [d8112, d2604, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2604, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42454 p hg
    simpa only [d8112, d2604, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43046 (p : Pattern) (guard : d8113 p = 1) : d2605 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2605, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43044 p hg
    simpa only [d8113, d2605, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2605, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43045 p hg
    simpa only [d8113, d2605, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43047 (p : Pattern) (guard : d8118 p = 1) : d2609 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2609, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42637 p hg
    simpa only [d8118, d2609, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2609, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42457 p hg
    simpa only [d8118, d2609, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43048 (p : Pattern) (guard : d8119 p = 1) : d2610 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d2610, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43046 p hg
    simpa only [d8119, d2610, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d2610, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43047 p hg
    simpa only [d8119, d2610, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43049 (p : Pattern) (guard : d8125 p = 1) : d2617 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d2617, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43048 p hg
    simpa only [d8125, d2617, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d2617, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42466 p hg
    simpa only [d8125, d2617, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43050 (p : Pattern) (guard : d8089 p = 1) : d2504 p ≤ (0 : Int) + d320 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d2504, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35462 p hg
    simpa only [d8089, d2504, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d2504, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d8089, d2504, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43051 (p : Pattern) (guard : d8094 p = 1) : d2504 p ≤ (0 : Int) + d321 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43050 p hg
    simpa only [d8094, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42396 p hg
    simpa only [d8094, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43052 (p : Pattern) (guard : d8100 p = 1) : d2518 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2518, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43051 p hg
    simpa only [d8100, d2518, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2518, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42398 p hg
    simpa only [d8100, d2518, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43053 (p : Pattern) (guard : d8106 p = 1) : d2601 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2601, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43052 p hg
    simpa only [d8106, d2601, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2601, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42450 p hg
    simpa only [d8106, d2601, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43054 (p : Pattern) (guard : d5854 p = 1) : d2540 p ≤ (0 : Int) + d332 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d2540, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35468 p hg
    simpa only [d5854, d2540, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d2540, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5854, d2540, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43055 (p : Pattern) (guard : d8099 p = 1) : d2540 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43054 p hg
    simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21708 p hg
    simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43056 (p : Pattern) (guard : d8105 p = 1) : d2569 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d2569, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43055 p hg
    simpa only [d8105, d2569, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d2569, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22597 p hg
    simpa only [d8105, d2569, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43057 (p : Pattern) (guard : d8111 p = 1) : d2611 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2611, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43056 p hg
    simpa only [d8111, d2611, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2611, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42472 p hg
    simpa only [d8111, d2611, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43058 (p : Pattern) (guard : d8112 p = 1) : d2618 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2618, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43053 p hg
    simpa only [d8112, d2618, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2618, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43057 p hg
    simpa only [d8112, d2618, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43059 (p : Pattern) (guard : d8118 p = 1) : d2620 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2620, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43058 p hg
    simpa only [d8118, d2620, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2620, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42476 p hg
    simpa only [d8118, d2620, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43060 (p : Pattern) (guard : d8124 p = 1) : d2623 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d2623, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43059 p hg
    simpa only [d8124, d2623, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d2623, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42481 p hg
    simpa only [d8124, d2623, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43061 (p : Pattern) (guard : d8130 p = 1) : d2627 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d2627, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43060 p hg
    simpa only [d8130, d2627, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d2627, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42485 p hg
    simpa only [d8130, d2627, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43062 (p : Pattern) (guard : d8131 p = 1) : d2628 p ≤ (0 : Int) + d439 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d2628, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43049 p hg
    simpa only [d8131, d2628, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d2628, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43061 p hg
    simpa only [d8131, d2628, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43063 (p : Pattern) (guard : d8132 p = 1) : d2666 p ≤ (0 : Int) + d440 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d2666, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43043 p hg
    simpa only [d8132, d2666, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d2666, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43062 p hg
    simpa only [d8132, d2666, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43064 (p : Pattern) (guard : d8101 p = 1) : d2601 p ≤ (0 : Int) + d352 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2601, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42613 p hg
    simpa only [d8101, d2601, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2601, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42183 p hg
    simpa only [d8101, d2601, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43065 (p : Pattern) (guard : d8107 p = 1) : d2601 p ≤ (0 : Int) + d355 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43064 p hg
    simpa only [d8107, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43053 p hg
    simpa only [d8107, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43066 (p : Pattern) (guard : d8112 p = 1) : d2604 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2604, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42644 p hg
    simpa only [d8112, d2604, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2604, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42454 p hg
    simpa only [d8112, d2604, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43067 (p : Pattern) (guard : d8113 p = 1) : d2605 p ≤ (0 : Int) + d362 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2605, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43065 p hg
    simpa only [d8113, d2605, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2605, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43066 p hg
    simpa only [d8113, d2605, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43068 (p : Pattern) (guard : d8118 p = 1) : d2609 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2609, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43045 p hg
    simpa only [d8118, d2609, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2609, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42457 p hg
    simpa only [d8118, d2609, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43069 (p : Pattern) (guard : d8119 p = 1) : d2610 p ≤ (0 : Int) + d395 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d2610, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43067 p hg
    simpa only [d8119, d2610, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d2610, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43068 p hg
    simpa only [d8119, d2610, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43070 (p : Pattern) (guard : d8112 p = 1) : d2614 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2614, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42331 p hg
    simpa only [d8112, d2614, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2614, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42463 p hg
    simpa only [d8112, d2614, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43071 (p : Pattern) (guard : d8118 p = 1) : d2615 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2615, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43070 p hg
    simpa only [d8118, d2615, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2615, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42223 p hg
    simpa only [d8118, d2615, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43072 (p : Pattern) (guard : d8124 p = 1) : d2616 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d2616, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43071 p hg
    simpa only [d8124, d2616, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d2616, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34736 p hg
    simpa only [d8124, d2616, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43073 (p : Pattern) (guard : d8125 p = 1) : d2617 p ≤ (0 : Int) + d397 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d2617, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43069 p hg
    simpa only [d8125, d2617, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d2617, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43072 p hg
    simpa only [d8125, d2617, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43074 (p : Pattern) (guard : d8089 p = 1) : d2504 p ≤ (0 : Int) + d318 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d2504, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35480 p hg
    simpa only [d8089, d2504, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d2504, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d8089, d2504, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43075 (p : Pattern) (guard : d8094 p = 1) : d2504 p ≤ (0 : Int) + d323 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43074 p hg
    simpa only [d8094, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42396 p hg
    simpa only [d8094, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43076 (p : Pattern) (guard : d8100 p = 1) : d2518 p ≤ (0 : Int) + d324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2518, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43075 p hg
    simpa only [d8100, d2518, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2518, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42398 p hg
    simpa only [d8100, d2518, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43077 (p : Pattern) (guard : d8106 p = 1) : d2601 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2601, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43076 p hg
    simpa only [d8106, d2601, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2601, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42450 p hg
    simpa only [d8106, d2601, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43078 (p : Pattern) (guard : d5854 p = 1) : d2540 p ≤ (0 : Int) + d330 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d2540, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35625 p hg
    simpa only [d5854, d2540, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d2540, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5854, d2540, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43079 (p : Pattern) (guard : d8099 p = 1) : d2540 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43078 p hg
    simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21708 p hg
    simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43080 (p : Pattern) (guard : d8105 p = 1) : d2569 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d2569, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43079 p hg
    simpa only [d8105, d2569, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d2569, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22597 p hg
    simpa only [d8105, d2569, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43081 (p : Pattern) (guard : d8111 p = 1) : d2611 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2611, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43080 p hg
    simpa only [d8111, d2611, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2611, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42472 p hg
    simpa only [d8111, d2611, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43082 (p : Pattern) (guard : d8112 p = 1) : d2618 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2618, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43077 p hg
    simpa only [d8112, d2618, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2618, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43081 p hg
    simpa only [d8112, d2618, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43083 (p : Pattern) (guard : d5854 p = 1) : d2520 p ≤ (0 : Int) + d332 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d2520, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35487 p hg
    simpa only [d5854, d2520, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d2520, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5854, d2520, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43084 (p : Pattern) (guard : d8099 p = 1) : d2520 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43083 p hg
    simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21653 p hg
    simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43085 (p : Pattern) (guard : d8105 p = 1) : d2523 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d2523, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43084 p hg
    simpa only [d8105, d2523, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d2523, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22564 p hg
    simpa only [d8105, d2523, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43086 (p : Pattern) (guard : d8111 p = 1) : d2603 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2603, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43085 p hg
    simpa only [d8111, d2603, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2603, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42453 p hg
    simpa only [d8111, d2603, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43087 (p : Pattern) (guard : d8117 p = 1) : d2619 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2619, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43086 p hg
    simpa only [d8117, d2619, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2619, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42475 p hg
    simpa only [d8117, d2619, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43088 (p : Pattern) (guard : d8118 p = 1) : d2620 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2620, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43082 p hg
    simpa only [d8118, d2620, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2620, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43087 p hg
    simpa only [d8118, d2620, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43089 (p : Pattern) (guard : d8124 p = 1) : d2623 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d2623, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43088 p hg
    simpa only [d8124, d2623, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d2623, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42481 p hg
    simpa only [d8124, d2623, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43090 (p : Pattern) (guard : d8130 p = 1) : d2627 p ≤ (0 : Int) + d399 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d2627, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43089 p hg
    simpa only [d8130, d2627, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d2627, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42485 p hg
    simpa only [d8130, d2627, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43091 (p : Pattern) (guard : d8131 p = 1) : d2628 p ≤ (0 : Int) + d400 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d2628, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43073 p hg
    simpa only [d8131, d2628, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d2628, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43090 p hg
    simpa only [d8131, d2628, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43092 (p : Pattern) (guard : d8106 p = 1) : d2607 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2607, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42301 p hg
    simpa only [d8106, d2607, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2607, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42026 p hg
    simpa only [d8106, d2607, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43093 (p : Pattern) (guard : d8112 p = 1) : d2630 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2630, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43092 p hg
    simpa only [d8112, d2630, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2630, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42222 p hg
    simpa only [d8112, d2630, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43094 (p : Pattern) (guard : d8118 p = 1) : d2631 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2631, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43093 p hg
    simpa only [d8118, d2631, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2631, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42223 p hg
    simpa only [d8118, d2631, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43095 (p : Pattern) (guard : d8123 p = 1) : d2632 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d2632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42223 p hg
    simpa only [d8123, d2632, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d2632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d2632, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43096 (p : Pattern) (guard : d8124 p = 1) : d2633 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d2633, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43094 p hg
    simpa only [d8124, d2633, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d2633, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43095 p hg
    simpa only [d8124, d2633, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43097 (p : Pattern) (guard : d8129 p = 1) : d2634 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d2634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43095 p hg
    simpa only [d8129, d2634, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d2634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8129, d2634, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43098 (p : Pattern) (guard : d8130 p = 1) : d2635 p ≤ (0 : Int) + d421 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d2635, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43096 p hg
    simpa only [d8130, d2635, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d2635, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43097 p hg
    simpa only [d8130, d2635, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43099 (p : Pattern) (guard : d8135 p = 1) : d2636 p ≤ (0 : Int) + d12 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d2636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43097 p hg
    simpa only [d8135, d2636, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d2636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8135, d2636, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43100 (p : Pattern) (guard : d8136 p = 1) : d2637 p ≤ (0 : Int) + d441 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d2637, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43098 p hg
    simpa only [d8136, d2637, d441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d2637, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43099 p hg
    simpa only [d8136, d2637, d441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43101 (p : Pattern) (guard : d8137 p = 1) : d2638 p ≤ (0 : Int) + d442 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d2638, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43091 p hg
    simpa only [d8137, d2638, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d2638, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43100 p hg
    simpa only [d8137, d2638, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43102 (p : Pattern) (guard : d8138 p = 1) : d2667 p ≤ (0 : Int) + d443 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8132 p = 1 := by simpa only [d8138, d2667, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43063 p hg
    simpa only [d8138, d2667, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8137 p = 1 := by simpa only [d8138, d2667, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43101 p hg
    simpa only [d8138, d2667, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43103 (p : Pattern) (guard : d8100 p = 1) : d2600 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2600, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43011 p hg
    simpa only [d8100, d2600, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2600, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d2600, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43104 (p : Pattern) (guard : d8101 p = 1) : d2601 p ≤ (0 : Int) + d344 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2601, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42986 p hg
    simpa only [d8101, d2601, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2601, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43103 p hg
    simpa only [d8101, d2601, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43105 (p : Pattern) (guard : d8107 p = 1) : d2601 p ≤ (0 : Int) + d346 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43104 p hg
    simpa only [d8107, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43077 p hg
    simpa only [d8107, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43106 (p : Pattern) (guard : d8112 p = 1) : d2604 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2604, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43053 p hg
    simpa only [d8112, d2604, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2604, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43086 p hg
    simpa only [d8112, d2604, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43107 (p : Pattern) (guard : d8113 p = 1) : d2605 p ≤ (0 : Int) + d402 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2605, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43105 p hg
    simpa only [d8113, d2605, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2605, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43106 p hg
    simpa only [d8113, d2605, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43108 (p : Pattern) (guard : d8118 p = 1) : d2609 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2609, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43066 p hg
    simpa only [d8118, d2609, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2609, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42457 p hg
    simpa only [d8118, d2609, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43109 (p : Pattern) (guard : d8119 p = 1) : d2610 p ≤ (0 : Int) + d404 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d2610, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43107 p hg
    simpa only [d8119, d2610, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d2610, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43108 p hg
    simpa only [d8119, d2610, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43110 (p : Pattern) (guard : d8111 p = 1) : d2792 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42437 p hg
    simpa only [d8111, d2792, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42462 p hg
    simpa only [d8111, d2792, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43111 (p : Pattern) (guard : d8112 p = 1) : d2793 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2793, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42356 p hg
    simpa only [d8112, d2793, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2793, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43110 p hg
    simpa only [d8112, d2793, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43112 (p : Pattern) (guard : d8111 p = 1) : d2794 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42437 p hg
    simpa only [d8111, d2794, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42221 p hg
    simpa only [d8111, d2794, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43113 (p : Pattern) (guard : d0 p = 1) : d2795 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare43114 (p : Pattern) (guard : d8117 p = 1) : d2796 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43112 p hg
    simpa only [d8117, d2796, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43113 p hg
    simpa only [d8117, d2796, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43115 (p : Pattern) (guard : d8118 p = 1) : d2797 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2797, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43111 p hg
    simpa only [d8118, d2797, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2797, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43114 p hg
    simpa only [d8118, d2797, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43116 (p : Pattern) (guard : d8117 p = 1) : d2798 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42438 p hg
    simpa only [d8117, d2798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43113 p hg
    simpa only [d8117, d2798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43117 (p : Pattern) (guard : d8123 p = 1) : d2799 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d2799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43116 p hg
    simpa only [d8123, d2799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d2799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42445 p hg
    simpa only [d8123, d2799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43118 (p : Pattern) (guard : d8124 p = 1) : d2800 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d2800, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43115 p hg
    simpa only [d8124, d2800, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d2800, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43117 p hg
    simpa only [d8124, d2800, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43119 (p : Pattern) (guard : d8125 p = 1) : d2801 p ≤ (0 : Int) + d406 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d2801, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43109 p hg
    simpa only [d8125, d2801, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d2801, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43118 p hg
    simpa only [d8125, d2801, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
