/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons342
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare48020 (p : Pattern) (guard : d8112 p = 1) : d118 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35315 p hg
    simpa only [d8112, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48016 p hg
    simpa only [d8112, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48021 (p : Pattern) (guard : d8118 p = 1) : d1441 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1441, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48020 p hg
    simpa only [d8118, d1441, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1441, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35320 p hg
    simpa only [d8118, d1441, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48022 (p : Pattern) (guard : d8124 p = 1) : d1442 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1442, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48021 p hg
    simpa only [d8124, d1442, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1442, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35322 p hg
    simpa only [d8124, d1442, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48023 (p : Pattern) (guard : d8125 p = 1) : d1443 p ≤ (0 : Int) + d406 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d1443, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48019 p hg
    simpa only [d8125, d1443, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d1443, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48022 p hg
    simpa only [d8125, d1443, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48024 (p : Pattern) (guard : d8117 p = 1) : d1289 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d1289, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41425 p hg
    simpa only [d8117, d1289, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d1289, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8117, d1289, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48025 (p : Pattern) (guard : d8118 p = 1) : d1453 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1453, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35336 p hg
    simpa only [d8118, d1453, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1453, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48024 p hg
    simpa only [d8118, d1453, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48026 (p : Pattern) (guard : d8117 p = 1) : d862 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d862, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35283 p hg
    simpa only [d8117, d862, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d862, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8218 p hg
    simpa only [d8117, d862, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48027 (p : Pattern) (guard : d8123 p = 1) : d1051 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1051, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48026 p hg
    simpa only [d8123, d1051, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1051, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d1051, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48028 (p : Pattern) (guard : d8124 p = 1) : d1460 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1460, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48025 p hg
    simpa only [d8124, d1460, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1460, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48027 p hg
    simpa only [d8124, d1460, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48029 (p : Pattern) (guard : d8117 p = 1) : d862 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35360 p hg
    simpa only [d8117, d862, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8218 p hg
    simpa only [d8117, d862, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48030 (p : Pattern) (guard : d8123 p = 1) : d1446 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48029 p hg
    simpa only [d8123, d1446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10219 p hg
    simpa only [d8123, d1446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48031 (p : Pattern) (guard : d8129 p = 1) : d1447 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d1447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48030 p hg
    simpa only [d8129, d1447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d1447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8786 p hg
    simpa only [d8129, d1447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48032 (p : Pattern) (guard : d8130 p = 1) : d1461 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d1461, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48028 p hg
    simpa only [d8130, d1461, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d1461, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48031 p hg
    simpa only [d8130, d1461, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48033 (p : Pattern) (guard : d8131 p = 1) : d1462 p ≤ (0 : Int) + d408 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d1462, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48023 p hg
    simpa only [d8131, d1462, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d1462, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48032 p hg
    simpa only [d8131, d1462, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48034 (p : Pattern) (guard : d8117 p = 1) : d133 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35354 p hg
    simpa only [d8117, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8230 p hg
    simpa only [d8117, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48035 (p : Pattern) (guard : d8123 p = 1) : d1450 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48034 p hg
    simpa only [d8123, d1450, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4330 p hg
    simpa only [d8123, d1450, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48036 (p : Pattern) (guard : d8124 p = 1) : d1451 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1451, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35357 p hg
    simpa only [d8124, d1451, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1451, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48035 p hg
    simpa only [d8124, d1451, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48037 (p : Pattern) (guard : d8117 p = 1) : d132 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35360 p hg
    simpa only [d8117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8230 p hg
    simpa only [d8117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48038 (p : Pattern) (guard : d8123 p = 1) : d1061 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48037 p hg
    simpa only [d8123, d1061, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d1061, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48039 (p : Pattern) (guard : d8129 p = 1) : d1062 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d1062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48038 p hg
    simpa only [d8129, d1062, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d1062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8129, d1062, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48040 (p : Pattern) (guard : d8130 p = 1) : d1452 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d1452, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48036 p hg
    simpa only [d8130, d1452, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d1452, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48039 p hg
    simpa only [d8130, d1452, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48041 (p : Pattern) (guard : d8123 p = 1) : d1453 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1453, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35371 p hg
    simpa only [d8123, d1453, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1453, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10232 p hg
    simpa only [d8123, d1453, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48042 (p : Pattern) (guard : d8129 p = 1) : d1454 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d1454, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48041 p hg
    simpa only [d8129, d1454, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d1454, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8798 p hg
    simpa only [d8129, d1454, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48043 (p : Pattern) (guard : d0 p = 1) : d1066 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare48044 (p : Pattern) (guard : d8135 p = 1) : d1455 p ≤ (0 : Int) + d411 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d1455, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48042 p hg
    simpa only [d8135, d1455, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d1455, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48043 p hg
    simpa only [d8135, d1455, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48045 (p : Pattern) (guard : d8136 p = 1) : d1456 p ≤ (0 : Int) + d412 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d1456, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48040 p hg
    simpa only [d8136, d1456, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d1456, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48044 p hg
    simpa only [d8136, d1456, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48046 (p : Pattern) (guard : d8137 p = 1) : d1463 p ≤ (0 : Int) + d413 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d1463, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48033 p hg
    simpa only [d8137, d1463, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d1463, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48045 p hg
    simpa only [d8137, d1463, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48047 (p : Pattern) (guard : d8124 p = 1) : d1451 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1451, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38229 p hg
    simpa only [d8124, d1451, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1451, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48035 p hg
    simpa only [d8124, d1451, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48048 (p : Pattern) (guard : d8130 p = 1) : d1452 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d1452, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48047 p hg
    simpa only [d8130, d1452, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d1452, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48039 p hg
    simpa only [d8130, d1452, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48049 (p : Pattern) (guard : d8123 p = 1) : d1453 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1453, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41434 p hg
    simpa only [d8123, d1453, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1453, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10232 p hg
    simpa only [d8123, d1453, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48050 (p : Pattern) (guard : d8129 p = 1) : d1454 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d1454, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48049 p hg
    simpa only [d8129, d1454, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d1454, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8798 p hg
    simpa only [d8129, d1454, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48051 (p : Pattern) (guard : d8135 p = 1) : d1455 p ≤ (0 : Int) + d421 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d1455, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48050 p hg
    simpa only [d8135, d1455, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d1455, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48043 p hg
    simpa only [d8135, d1455, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48052 (p : Pattern) (guard : d8136 p = 1) : d1456 p ≤ (0 : Int) + d422 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d1456, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48048 p hg
    simpa only [d8136, d1456, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d1456, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48051 p hg
    simpa only [d8136, d1456, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48053 (p : Pattern) (guard : d8142 p = 1) : d1464 p ≤ (0 : Int) + d444 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8136 p = 1 := by simpa only [d8142, d1464, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48052 p hg
    simpa only [d8142, d1464, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8141 p = 1 := by simpa only [d8142, d1464, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37397 p hg
    simpa only [d8142, d1464, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48054 (p : Pattern) (guard : d8143 p = 1) : d1465 p ≤ (0 : Int) + d445 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8137 p = 1 := by simpa only [d8143, d1465, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48046 p hg
    simpa only [d8143, d1465, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8142 p = 1 := by simpa only [d8143, d1465, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48053 p hg
    simpa only [d8143, d1465, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48055 (p : Pattern) (guard : d8144 p = 1) : d1466 p ≤ (0 : Int) + d446 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8138 p = 1 := by simpa only [d8144, d1466, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48015 p hg
    simpa only [d8144, d1466, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8143 p = 1 := by simpa only [d8144, d1466, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48054 p hg
    simpa only [d8144, d1466, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48056 (p : Pattern) (guard : d8145 p = 1) : d1467 p ≤ (0 : Int) + d447 p := by
  cases selected : p 71 with
  | false =>
    have hg : d8139 p = 1 := by simpa only [d8145, d1467, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47944 p hg
    simpa only [d8145, d1467, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8144 p = 1 := by simpa only [d8145, d1467, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48055 p hg
    simpa only [d8145, d1467, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48057 (p : Pattern) (guard : d8146 p = 1) : d1468 p ≤ (0 : Int) + d447 p := by
  cases selected : p 49 with
  | false =>
    have hg : d8140 p = 1 := by simpa only [d8146, d1468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47884 p hg
    simpa only [d8146, d1468, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8145 p = 1 := by simpa only [d8146, d1468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48056 p hg
    simpa only [d8146, d1468, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48058 (p : Pattern) (guard : d8107 p = 1) : d950 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d950, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34878 p hg
    simpa only [d8107, d950, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d950, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35644 p hg
    simpa only [d8107, d950, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48059 (p : Pattern) (guard : d8113 p = 1) : d1399 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1399, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48058 p hg
    simpa only [d8113, d1399, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1399, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35400 p hg
    simpa only [d8113, d1399, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48060 (p : Pattern) (guard : d8114 p = 1) : d1400 p ≤ (0 : Int) + d436 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d1400, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35398 p hg
    simpa only [d8114, d1400, d436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d1400, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48059 p hg
    simpa only [d8114, d1400, d436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48061 (p : Pattern) (guard : d8107 p = 1) : d33 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35403 p hg
    simpa only [d8107, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35497 p hg
    simpa only [d8107, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48062 (p : Pattern) (guard : d8113 p = 1) : d1401 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1401, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48061 p hg
    simpa only [d8113, d1401, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1401, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35407 p hg
    simpa only [d8113, d1401, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48063 (p : Pattern) (guard : d8119 p = 1) : d1402 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1402, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48062 p hg
    simpa only [d8119, d1402, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1402, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34872 p hg
    simpa only [d8119, d1402, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48064 (p : Pattern) (guard : d8120 p = 1) : d1403 p ≤ (0 : Int) + d437 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d1403, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48060 p hg
    simpa only [d8120, d1403, d437, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d1403, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48063 p hg
    simpa only [d8120, d1403, d437, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48065 (p : Pattern) (guard : d8084 p = 1) : d31 p ≤ (0 : Int) + d317 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d31, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47692 p hg
    simpa only [d8084, d31, d317, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d31, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34407 p hg
    simpa only [d8084, d31, d317, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48066 (p : Pattern) (guard : d8089 p = 1) : d31 p ≤ (0 : Int) + d318 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48065 p hg
    simpa only [d8089, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34472 p hg
    simpa only [d8089, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48067 (p : Pattern) (guard : d8094 p = 1) : d31 p ≤ (0 : Int) + d323 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48066 p hg
    simpa only [d8094, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34525 p hg
    simpa only [d8094, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48068 (p : Pattern) (guard : d8100 p = 1) : d31 p ≤ (0 : Int) + d324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48067 p hg
    simpa only [d8100, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34678 p hg
    simpa only [d8100, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48069 (p : Pattern) (guard : d8106 p = 1) : d53 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d53, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48068 p hg
    simpa only [d8106, d53, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d53, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34721 p hg
    simpa only [d8106, d53, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48070 (p : Pattern) (guard : d8112 p = 1) : d1167 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1167, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48069 p hg
    simpa only [d8112, d1167, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1167, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47959 p hg
    simpa only [d8112, d1167, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48071 (p : Pattern) (guard : d8113 p = 1) : d1431 p ≤ (0 : Int) + d416 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1431, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35421 p hg
    simpa only [d8113, d1431, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1431, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48070 p hg
    simpa only [d8113, d1431, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48072 (p : Pattern) (guard : d8111 p = 1) : d795 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d795, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35471 p hg
    simpa only [d8111, d795, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d795, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5050 p hg
    simpa only [d8111, d795, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48073 (p : Pattern) (guard : d8112 p = 1) : d796 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d796, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35047 p hg
    simpa only [d8112, d796, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d796, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48072 p hg
    simpa only [d8112, d796, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48074 (p : Pattern) (guard : d8118 p = 1) : d1405 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1405, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48073 p hg
    simpa only [d8118, d1405, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1405, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34730 p hg
    simpa only [d8118, d1405, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48075 (p : Pattern) (guard : d8119 p = 1) : d1432 p ≤ (0 : Int) + d417 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1432, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48071 p hg
    simpa only [d8119, d1432, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1432, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48074 p hg
    simpa only [d8119, d1432, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48076 (p : Pattern) (guard : d8112 p = 1) : d796 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d796, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34884 p hg
    simpa only [d8112, d796, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d796, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47848 p hg
    simpa only [d8112, d796, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48077 (p : Pattern) (guard : d8118 p = 1) : d1407 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1407, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48076 p hg
    simpa only [d8118, d1407, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1407, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47853 p hg
    simpa only [d8118, d1407, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48078 (p : Pattern) (guard : d8124 p = 1) : d1408 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1408, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48077 p hg
    simpa only [d8124, d1408, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1408, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41454 p hg
    simpa only [d8124, d1408, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48079 (p : Pattern) (guard : d8125 p = 1) : d1433 p ≤ (0 : Int) + d418 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d1433, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48075 p hg
    simpa only [d8125, d1433, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d1433, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48078 p hg
    simpa only [d8125, d1433, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48080 (p : Pattern) (guard : d8126 p = 1) : d1434 p ≤ (0 : Int) + d438 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d1434, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48064 p hg
    simpa only [d8126, d1434, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d1434, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48079 p hg
    simpa only [d8126, d1434, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48081 (p : Pattern) (guard : d8118 p = 1) : d1411 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1411, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34929 p hg
    simpa only [d8118, d1411, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1411, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34914 p hg
    simpa only [d8118, d1411, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48082 (p : Pattern) (guard : d8119 p = 1) : d1412 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1412, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35457 p hg
    simpa only [d8119, d1412, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1412, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48081 p hg
    simpa only [d8119, d1412, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48083 (p : Pattern) (guard : d8125 p = 1) : d1415 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d1415, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48082 p hg
    simpa only [d8125, d1415, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d1415, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47863 p hg
    simpa only [d8125, d1415, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48084 (p : Pattern) (guard : d8118 p = 1) : d1416 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1416, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35473 p hg
    simpa only [d8118, d1416, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1416, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47865 p hg
    simpa only [d8118, d1416, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48085 (p : Pattern) (guard : d8124 p = 1) : d1418 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1418, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48084 p hg
    simpa only [d8124, d1418, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1418, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47868 p hg
    simpa only [d8124, d1418, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48086 (p : Pattern) (guard : d8130 p = 1) : d1419 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d1419, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48085 p hg
    simpa only [d8130, d1419, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d1419, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47871 p hg
    simpa only [d8130, d1419, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48087 (p : Pattern) (guard : d8131 p = 1) : d1420 p ≤ (0 : Int) + d439 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d1420, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48083 p hg
    simpa only [d8131, d1420, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d1420, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48086 p hg
    simpa only [d8131, d1420, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48088 (p : Pattern) (guard : d8132 p = 1) : d1435 p ≤ (0 : Int) + d440 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d1435, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48080 p hg
    simpa only [d8132, d1435, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d1435, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48087 p hg
    simpa only [d8132, d1435, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48089 (p : Pattern) (guard : d8118 p = 1) : d1411 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1411, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35074 p hg
    simpa only [d8118, d1411, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1411, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34914 p hg
    simpa only [d8118, d1411, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48090 (p : Pattern) (guard : d8119 p = 1) : d1412 p ≤ (0 : Int) + d395 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1412, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35617 p hg
    simpa only [d8119, d1412, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1412, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48089 p hg
    simpa only [d8119, d1412, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48091 (p : Pattern) (guard : d8112 p = 1) : d53 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34835 p hg
    simpa only [d8112, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34928 p hg
    simpa only [d8112, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48092 (p : Pattern) (guard : d8118 p = 1) : d1413 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1413, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48091 p hg
    simpa only [d8118, d1413, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1413, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34730 p hg
    simpa only [d8118, d1413, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48093 (p : Pattern) (guard : d8124 p = 1) : d1414 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1414, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48092 p hg
    simpa only [d8124, d1414, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1414, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34736 p hg
    simpa only [d8124, d1414, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48094 (p : Pattern) (guard : d8125 p = 1) : d1415 p ≤ (0 : Int) + d397 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d1415, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48090 p hg
    simpa only [d8125, d1415, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d1415, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48093 p hg
    simpa only [d8125, d1415, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48095 (p : Pattern) (guard : d8117 p = 1) : d1181 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d1181, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35472 p hg
    simpa only [d8117, d1181, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d1181, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8117, d1181, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48096 (p : Pattern) (guard : d8118 p = 1) : d1416 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1416, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35630 p hg
    simpa only [d8118, d1416, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1416, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48095 p hg
    simpa only [d8118, d1416, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48097 (p : Pattern) (guard : d8124 p = 1) : d1418 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1418, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48096 p hg
    simpa only [d8124, d1418, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1418, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47868 p hg
    simpa only [d8124, d1418, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48098 (p : Pattern) (guard : d8130 p = 1) : d1419 p ≤ (0 : Int) + d399 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d1419, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48097 p hg
    simpa only [d8130, d1419, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d1419, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47871 p hg
    simpa only [d8130, d1419, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48099 (p : Pattern) (guard : d8131 p = 1) : d1420 p ≤ (0 : Int) + d400 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d1420, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48094 p hg
    simpa only [d8131, d1420, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d1420, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48098 p hg
    simpa only [d8131, d1420, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48100 (p : Pattern) (guard : d8137 p = 1) : d1422 p ≤ (0 : Int) + d442 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d1422, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48099 p hg
    simpa only [d8137, d1422, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d1422, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41445 p hg
    simpa only [d8137, d1422, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48101 (p : Pattern) (guard : d8138 p = 1) : d1436 p ≤ (0 : Int) + d443 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8132 p = 1 := by simpa only [d8138, d1436, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48088 p hg
    simpa only [d8138, d1436, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8137 p = 1 := by simpa only [d8138, d1436, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48100 p hg
    simpa only [d8138, d1436, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48102 (p : Pattern) (guard : d8111 p = 1) : d33 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35498 p hg
    simpa only [d8111, d33, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5062 p hg
    simpa only [d8111, d33, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48103 (p : Pattern) (guard : d8112 p = 1) : d950 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d950, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35454 p hg
    simpa only [d8112, d950, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d950, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48102 p hg
    simpa only [d8112, d950, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48104 (p : Pattern) (guard : d8118 p = 1) : d1399 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1399, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48103 p hg
    simpa only [d8118, d1399, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1399, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34914 p hg
    simpa only [d8118, d1399, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48105 (p : Pattern) (guard : d8119 p = 1) : d1400 p ≤ (0 : Int) + d404 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1400, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35493 p hg
    simpa only [d8119, d1400, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1400, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48104 p hg
    simpa only [d8119, d1400, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48106 (p : Pattern) (guard : d8112 p = 1) : d33 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35497 p hg
    simpa only [d8112, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48102 p hg
    simpa only [d8112, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48107 (p : Pattern) (guard : d8118 p = 1) : d1401 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1401, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48106 p hg
    simpa only [d8118, d1401, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1401, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35502 p hg
    simpa only [d8118, d1401, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48108 (p : Pattern) (guard : d8124 p = 1) : d1402 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1402, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48107 p hg
    simpa only [d8124, d1402, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1402, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35506 p hg
    simpa only [d8124, d1402, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48109 (p : Pattern) (guard : d8125 p = 1) : d1403 p ≤ (0 : Int) + d406 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d1403, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48105 p hg
    simpa only [d8125, d1403, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d1403, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48108 p hg
    simpa only [d8125, d1403, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48110 (p : Pattern) (guard : d8117 p = 1) : d1181 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d1181, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35629 p hg
    simpa only [d8117, d1181, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d1181, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8117, d1181, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48111 (p : Pattern) (guard : d8118 p = 1) : d1416 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1416, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35520 p hg
    simpa only [d8118, d1416, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1416, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48110 p hg
    simpa only [d8118, d1416, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48112 (p : Pattern) (guard : d8117 p = 1) : d796 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d796, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35472 p hg
    simpa only [d8117, d796, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d796, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8126 p hg
    simpa only [d8117, d796, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48113 (p : Pattern) (guard : d8123 p = 1) : d1405 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1405, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48112 p hg
    simpa only [d8123, d1405, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1405, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4232 p hg
    simpa only [d8123, d1405, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48114 (p : Pattern) (guard : d8124 p = 1) : d1424 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1424, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48111 p hg
    simpa only [d8124, d1424, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1424, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48113 p hg
    simpa only [d8124, d1424, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48115 (p : Pattern) (guard : d8117 p = 1) : d796 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34928 p hg
    simpa only [d8117, d796, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8126 p hg
    simpa only [d8117, d796, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48116 (p : Pattern) (guard : d8123 p = 1) : d1407 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48115 p hg
    simpa only [d8123, d1407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10094 p hg
    simpa only [d8123, d1407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48117 (p : Pattern) (guard : d8129 p = 1) : d1408 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d1408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48116 p hg
    simpa only [d8129, d1408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d1408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13603 p hg
    simpa only [d8129, d1408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48118 (p : Pattern) (guard : d8130 p = 1) : d1425 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d1425, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48114 p hg
    simpa only [d8130, d1425, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d1425, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48117 p hg
    simpa only [d8130, d1425, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48119 (p : Pattern) (guard : d8131 p = 1) : d1426 p ≤ (0 : Int) + d408 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d1426, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48109 p hg
    simpa only [d8131, d1426, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d1426, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48118 p hg
    simpa only [d8131, d1426, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48120 (p : Pattern) (guard : d8117 p = 1) : d54 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35539 p hg
    simpa only [d8117, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8075 p hg
    simpa only [d8117, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48121 (p : Pattern) (guard : d8123 p = 1) : d1411 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48120 p hg
    simpa only [d8123, d1411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4229 p hg
    simpa only [d8123, d1411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48122 (p : Pattern) (guard : d8124 p = 1) : d1412 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1412, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35542 p hg
    simpa only [d8124, d1412, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1412, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48121 p hg
    simpa only [d8124, d1412, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48123 (p : Pattern) (guard : d8117 p = 1) : d53 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34928 p hg
    simpa only [d8117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8075 p hg
    simpa only [d8117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48124 (p : Pattern) (guard : d8123 p = 1) : d1413 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48123 p hg
    simpa only [d8123, d1413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4232 p hg
    simpa only [d8123, d1413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48125 (p : Pattern) (guard : d8129 p = 1) : d1414 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d1414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48124 p hg
    simpa only [d8129, d1414, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d1414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8129, d1414, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48126 (p : Pattern) (guard : d8130 p = 1) : d1415 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d1415, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48122 p hg
    simpa only [d8130, d1415, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d1415, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48125 p hg
    simpa only [d8130, d1415, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48127 (p : Pattern) (guard : d8123 p = 1) : d1469 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1469, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41470 p hg
    simpa only [d8123, d1469, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1469, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10152 p hg
    simpa only [d8123, d1469, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48128 (p : Pattern) (guard : d8129 p = 1) : d1470 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d1470, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48127 p hg
    simpa only [d8129, d1470, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d1470, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13852 p hg
    simpa only [d8129, d1470, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48129 (p : Pattern) (guard : d0 p = 1) : d1101 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare48130 (p : Pattern) (guard : d8135 p = 1) : d1471 p ≤ (0 : Int) + d411 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d1471, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48128 p hg
    simpa only [d8135, d1471, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d1471, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48129 p hg
    simpa only [d8135, d1471, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48131 (p : Pattern) (guard : d8136 p = 1) : d1472 p ≤ (0 : Int) + d412 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d1472, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48126 p hg
    simpa only [d8136, d1472, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d1472, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48130 p hg
    simpa only [d8136, d1472, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48132 (p : Pattern) (guard : d8137 p = 1) : d1473 p ≤ (0 : Int) + d413 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d1473, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48119 p hg
    simpa only [d8137, d1473, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d1473, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48131 p hg
    simpa only [d8137, d1473, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48133 (p : Pattern) (guard : d8124 p = 1) : d1412 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1412, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35679 p hg
    simpa only [d8124, d1412, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1412, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48121 p hg
    simpa only [d8124, d1412, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48134 (p : Pattern) (guard : d8130 p = 1) : d1415 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d1415, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48133 p hg
    simpa only [d8130, d1415, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d1415, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48125 p hg
    simpa only [d8130, d1415, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48135 (p : Pattern) (guard : d8123 p = 1) : d1469 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1469, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41479 p hg
    simpa only [d8123, d1469, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1469, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10152 p hg
    simpa only [d8123, d1469, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48136 (p : Pattern) (guard : d8129 p = 1) : d1470 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d1470, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48135 p hg
    simpa only [d8129, d1470, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d1470, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13852 p hg
    simpa only [d8129, d1470, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48137 (p : Pattern) (guard : d8135 p = 1) : d1471 p ≤ (0 : Int) + d421 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d1471, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48136 p hg
    simpa only [d8135, d1471, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d1471, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48129 p hg
    simpa only [d8135, d1471, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48138 (p : Pattern) (guard : d8136 p = 1) : d1472 p ≤ (0 : Int) + d422 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d1472, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48134 p hg
    simpa only [d8136, d1472, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d1472, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48137 p hg
    simpa only [d8136, d1472, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48139 (p : Pattern) (guard : d8142 p = 1) : d1474 p ≤ (0 : Int) + d444 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8136 p = 1 := by simpa only [d8142, d1474, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48138 p hg
    simpa only [d8142, d1474, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8141 p = 1 := by simpa only [d8142, d1474, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37397 p hg
    simpa only [d8142, d1474, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48140 (p : Pattern) (guard : d8143 p = 1) : d1475 p ≤ (0 : Int) + d445 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8137 p = 1 := by simpa only [d8143, d1475, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48132 p hg
    simpa only [d8143, d1475, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8142 p = 1 := by simpa only [d8143, d1475, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48139 p hg
    simpa only [d8143, d1475, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48141 (p : Pattern) (guard : d8144 p = 1) : d1476 p ≤ (0 : Int) + d446 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8138 p = 1 := by simpa only [d8144, d1476, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48101 p hg
    simpa only [d8144, d1476, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8143 p = 1 := by simpa only [d8144, d1476, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48140 p hg
    simpa only [d8144, d1476, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48142 (p : Pattern) (guard : d8145 p = 1) : d1477 p ≤ (0 : Int) + d447 p := by
  cases selected : p 71 with
  | false =>
    have hg : d8139 p = 1 := by simpa only [d8145, d1477, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47944 p hg
    simpa only [d8145, d1477, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8144 p = 1 := by simpa only [d8145, d1477, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48141 p hg
    simpa only [d8145, d1477, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48143 (p : Pattern) (guard : d8106 p = 1) : d33 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d33, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35465 p hg
    simpa only [d8106, d33, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d33, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34721 p hg
    simpa only [d8106, d33, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48144 (p : Pattern) (guard : d8107 p = 1) : d950 p ≤ (0 : Int) + d355 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d950, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35042 p hg
    simpa only [d8107, d950, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d950, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48143 p hg
    simpa only [d8107, d950, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48145 (p : Pattern) (guard : d8113 p = 1) : d1399 p ≤ (0 : Int) + d362 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1399, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48144 p hg
    simpa only [d8113, d1399, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1399, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35570 p hg
    simpa only [d8113, d1399, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48146 (p : Pattern) (guard : d8114 p = 1) : d1400 p ≤ (0 : Int) + d363 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d1400, d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35569 p hg
    simpa only [d8114, d1400, d363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d1400, d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48145 p hg
    simpa only [d8114, d1400, d363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48147 (p : Pattern) (guard : d8107 p = 1) : d33 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35573 p hg
    simpa only [d8107, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35644 p hg
    simpa only [d8107, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48148 (p : Pattern) (guard : d8113 p = 1) : d1401 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1401, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48147 p hg
    simpa only [d8113, d1401, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1401, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35576 p hg
    simpa only [d8113, d1401, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48149 (p : Pattern) (guard : d8119 p = 1) : d1402 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1402, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48148 p hg
    simpa only [d8119, d1402, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1402, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35580 p hg
    simpa only [d8119, d1402, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48150 (p : Pattern) (guard : d8120 p = 1) : d1403 p ≤ (0 : Int) + d377 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d1403, d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48146 p hg
    simpa only [d8120, d1403, d377, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d1403, d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48149 p hg
    simpa only [d8120, d1403, d377, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48151 (p : Pattern) (guard : d8111 p = 1) : d360 p ≤ (0 : Int) + d360 p := by
  omega
theorem compare48152 (p : Pattern) (guard : d8112 p = 1) : d1165 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1165, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35420 p hg
    simpa only [d8112, d1165, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1165, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48151 p hg
    simpa only [d8112, d1165, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48153 (p : Pattern) (guard : d8113 p = 1) : d1404 p ≤ (0 : Int) + d385 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1404, d385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35593 p hg
    simpa only [d8113, d1404, d385, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1404, d385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48152 p hg
    simpa only [d8113, d1404, d385, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48154 (p : Pattern) (guard : d8111 p = 1) : d795 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d795, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35628 p hg
    simpa only [d8111, d795, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d795, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5050 p hg
    simpa only [d8111, d795, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48155 (p : Pattern) (guard : d8112 p = 1) : d796 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d796, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48069 p hg
    simpa only [d8112, d796, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d796, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48154 p hg
    simpa only [d8112, d796, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48156 (p : Pattern) (guard : d8118 p = 1) : d1405 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1405, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48155 p hg
    simpa only [d8118, d1405, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1405, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35606 p hg
    simpa only [d8118, d1405, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48157 (p : Pattern) (guard : d8119 p = 1) : d1406 p ≤ (0 : Int) + d388 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1406, d388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48153 p hg
    simpa only [d8119, d1406, d388, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1406, d388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48156 p hg
    simpa only [d8119, d1406, d388, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48158 (p : Pattern) (guard : d8118 p = 1) : d1407 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1407, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48073 p hg
    simpa only [d8118, d1407, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1407, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47853 p hg
    simpa only [d8118, d1407, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48159 (p : Pattern) (guard : d8124 p = 1) : d1408 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1408, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48158 p hg
    simpa only [d8124, d1408, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1408, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41454 p hg
    simpa only [d8124, d1408, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
