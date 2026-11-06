/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons343
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare48160 (p : Pattern) (guard : d8125 p = 1) : d1409 p ≤ (0 : Int) + d392 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d1409, d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48157 p hg
    simpa only [d8125, d1409, d392, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d1409, d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48159 p hg
    simpa only [d8125, d1409, d392, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48161 (p : Pattern) (guard : d8126 p = 1) : d1410 p ≤ (0 : Int) + d393 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d1410, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48150 p hg
    simpa only [d8126, d1410, d393, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d1410, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48160 p hg
    simpa only [d8126, d1410, d393, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48162 (p : Pattern) (guard : d8132 p = 1) : d1421 p ≤ (0 : Int) + d401 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d1421, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48161 p hg
    simpa only [d8132, d1421, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d1421, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48099 p hg
    simpa only [d8132, d1421, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48163 (p : Pattern) (guard : d8118 p = 1) : d1411 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1411, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41416 p hg
    simpa only [d8118, d1411, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1411, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34914 p hg
    simpa only [d8118, d1411, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48164 (p : Pattern) (guard : d8119 p = 1) : d1412 p ≤ (0 : Int) + d404 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1412, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35493 p hg
    simpa only [d8119, d1412, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1412, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48163 p hg
    simpa only [d8119, d1412, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48165 (p : Pattern) (guard : d8112 p = 1) : d53 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35019 p hg
    simpa only [d8112, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34928 p hg
    simpa only [d8112, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48166 (p : Pattern) (guard : d8118 p = 1) : d1413 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1413, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48165 p hg
    simpa only [d8118, d1413, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1413, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34730 p hg
    simpa only [d8118, d1413, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48167 (p : Pattern) (guard : d8124 p = 1) : d1414 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1414, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48166 p hg
    simpa only [d8124, d1414, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1414, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34736 p hg
    simpa only [d8124, d1414, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48168 (p : Pattern) (guard : d8125 p = 1) : d1415 p ≤ (0 : Int) + d406 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d1415, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48164 p hg
    simpa only [d8125, d1415, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d1415, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48167 p hg
    simpa only [d8125, d1415, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48169 (p : Pattern) (guard : d8117 p = 1) : d808 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d808, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35472 p hg
    simpa only [d8117, d808, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d808, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3640 p hg
    simpa only [d8117, d808, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48170 (p : Pattern) (guard : d8123 p = 1) : d1417 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1417, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48169 p hg
    simpa only [d8123, d1417, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1417, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4232 p hg
    simpa only [d8123, d1417, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48171 (p : Pattern) (guard : d8124 p = 1) : d1418 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1418, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48111 p hg
    simpa only [d8124, d1418, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1418, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48170 p hg
    simpa only [d8124, d1418, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48172 (p : Pattern) (guard : d8130 p = 1) : d1419 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d1419, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48171 p hg
    simpa only [d8130, d1419, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d1419, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47871 p hg
    simpa only [d8130, d1419, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48173 (p : Pattern) (guard : d8131 p = 1) : d1420 p ≤ (0 : Int) + d408 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d1420, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48168 p hg
    simpa only [d8131, d1420, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d1420, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48172 p hg
    simpa only [d8131, d1420, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48174 (p : Pattern) (guard : d8137 p = 1) : d1422 p ≤ (0 : Int) + d413 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d1422, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48173 p hg
    simpa only [d8137, d1422, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d1422, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41493 p hg
    simpa only [d8137, d1422, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48175 (p : Pattern) (guard : d8138 p = 1) : d1423 p ≤ (0 : Int) + d414 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8132 p = 1 := by simpa only [d8138, d1423, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48162 p hg
    simpa only [d8138, d1423, d414, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8137 p = 1 := by simpa only [d8138, d1423, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48174 p hg
    simpa only [d8138, d1423, d414, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48176 (p : Pattern) (guard : d8111 p = 1) : d33 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d33, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35552 p hg
    simpa only [d8111, d33, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d33, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5062 p hg
    simpa only [d8111, d33, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48177 (p : Pattern) (guard : d8112 p = 1) : d950 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d950, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35466 p hg
    simpa only [d8112, d950, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d950, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48176 p hg
    simpa only [d8112, d950, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48178 (p : Pattern) (guard : d8118 p = 1) : d1399 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1399, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48177 p hg
    simpa only [d8118, d1399, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1399, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34914 p hg
    simpa only [d8118, d1399, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48179 (p : Pattern) (guard : d8119 p = 1) : d1400 p ≤ (0 : Int) + d417 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1400, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35641 p hg
    simpa only [d8119, d1400, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1400, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48178 p hg
    simpa only [d8119, d1400, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48180 (p : Pattern) (guard : d8112 p = 1) : d33 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35644 p hg
    simpa only [d8112, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48102 p hg
    simpa only [d8112, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48181 (p : Pattern) (guard : d8118 p = 1) : d1401 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1401, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48180 p hg
    simpa only [d8118, d1401, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1401, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35502 p hg
    simpa only [d8118, d1401, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48182 (p : Pattern) (guard : d8124 p = 1) : d1402 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1402, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48181 p hg
    simpa only [d8124, d1402, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1402, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35506 p hg
    simpa only [d8124, d1402, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48183 (p : Pattern) (guard : d8125 p = 1) : d1403 p ≤ (0 : Int) + d418 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d1403, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48179 p hg
    simpa only [d8125, d1403, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d1403, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48182 p hg
    simpa only [d8125, d1403, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48184 (p : Pattern) (guard : d8117 p = 1) : d1181 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d1181, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35519 p hg
    simpa only [d8117, d1181, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d1181, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8117, d1181, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48185 (p : Pattern) (guard : d8118 p = 1) : d1416 p ≤ (0 : Int) + d362 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1416, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35660 p hg
    simpa only [d8118, d1416, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1416, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48184 p hg
    simpa only [d8118, d1416, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48186 (p : Pattern) (guard : d8117 p = 1) : d796 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d796, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35629 p hg
    simpa only [d8117, d796, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d796, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8126 p hg
    simpa only [d8117, d796, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48187 (p : Pattern) (guard : d8123 p = 1) : d1405 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1405, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48186 p hg
    simpa only [d8123, d1405, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1405, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4232 p hg
    simpa only [d8123, d1405, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48188 (p : Pattern) (guard : d8124 p = 1) : d1424 p ≤ (0 : Int) + d395 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1424, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48185 p hg
    simpa only [d8124, d1424, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1424, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48187 p hg
    simpa only [d8124, d1424, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48189 (p : Pattern) (guard : d8123 p = 1) : d1407 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1407, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48112 p hg
    simpa only [d8123, d1407, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1407, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10094 p hg
    simpa only [d8123, d1407, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48190 (p : Pattern) (guard : d8129 p = 1) : d1408 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d1408, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48189 p hg
    simpa only [d8129, d1408, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d1408, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13603 p hg
    simpa only [d8129, d1408, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48191 (p : Pattern) (guard : d8130 p = 1) : d1425 p ≤ (0 : Int) + d397 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d1425, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48188 p hg
    simpa only [d8130, d1425, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d1425, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48190 p hg
    simpa only [d8130, d1425, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48192 (p : Pattern) (guard : d8131 p = 1) : d1426 p ≤ (0 : Int) + d419 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d1426, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48183 p hg
    simpa only [d8131, d1426, d419, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d1426, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48191 p hg
    simpa only [d8131, d1426, d419, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48193 (p : Pattern) (guard : d8123 p = 1) : d1416 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1416, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35687 p hg
    simpa only [d8123, d1416, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1416, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10152 p hg
    simpa only [d8123, d1416, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48194 (p : Pattern) (guard : d8129 p = 1) : d1418 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d1418, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48193 p hg
    simpa only [d8129, d1418, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d1418, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13852 p hg
    simpa only [d8129, d1418, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48195 (p : Pattern) (guard : d0 p = 1) : d974 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare48196 (p : Pattern) (guard : d8135 p = 1) : d1419 p ≤ (0 : Int) + d421 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d1419, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48194 p hg
    simpa only [d8135, d1419, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d1419, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48195 p hg
    simpa only [d8135, d1419, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48197 (p : Pattern) (guard : d8136 p = 1) : d1420 p ≤ (0 : Int) + d422 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d1420, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48134 p hg
    simpa only [d8136, d1420, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d1420, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48196 p hg
    simpa only [d8136, d1420, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48198 (p : Pattern) (guard : d8137 p = 1) : d1427 p ≤ (0 : Int) + d423 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d1427, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48192 p hg
    simpa only [d8137, d1427, d423, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d1427, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48197 p hg
    simpa only [d8137, d1427, d423, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48199 (p : Pattern) (guard : d8124 p = 1) : d1412 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1412, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38279 p hg
    simpa only [d8124, d1412, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1412, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48121 p hg
    simpa only [d8124, d1412, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48200 (p : Pattern) (guard : d8130 p = 1) : d1415 p ≤ (0 : Int) + d399 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d1415, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48199 p hg
    simpa only [d8130, d1415, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d1415, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48125 p hg
    simpa only [d8130, d1415, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48201 (p : Pattern) (guard : d8123 p = 1) : d1416 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1416, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41498 p hg
    simpa only [d8123, d1416, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1416, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10152 p hg
    simpa only [d8123, d1416, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48202 (p : Pattern) (guard : d8129 p = 1) : d1418 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d1418, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48201 p hg
    simpa only [d8129, d1418, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d1418, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13852 p hg
    simpa only [d8129, d1418, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48203 (p : Pattern) (guard : d8135 p = 1) : d1419 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d1419, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48202 p hg
    simpa only [d8135, d1419, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d1419, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48195 p hg
    simpa only [d8135, d1419, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48204 (p : Pattern) (guard : d8136 p = 1) : d1420 p ≤ (0 : Int) + d424 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d1420, d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48200 p hg
    simpa only [d8136, d1420, d424, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d1420, d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48203 p hg
    simpa only [d8136, d1420, d424, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48205 (p : Pattern) (guard : d8142 p = 1) : d1428 p ≤ (0 : Int) + d425 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8136 p = 1 := by simpa only [d8142, d1428, d425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48204 p hg
    simpa only [d8142, d1428, d425, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8141 p = 1 := by simpa only [d8142, d1428, d425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37397 p hg
    simpa only [d8142, d1428, d425, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48206 (p : Pattern) (guard : d8143 p = 1) : d1429 p ≤ (0 : Int) + d426 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8137 p = 1 := by simpa only [d8143, d1429, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48198 p hg
    simpa only [d8143, d1429, d426, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8142 p = 1 := by simpa only [d8143, d1429, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48205 p hg
    simpa only [d8143, d1429, d426, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48207 (p : Pattern) (guard : d8144 p = 1) : d1430 p ≤ (0 : Int) + d427 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8138 p = 1 := by simpa only [d8144, d1430, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48175 p hg
    simpa only [d8144, d1430, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8143 p = 1 := by simpa only [d8144, d1430, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48206 p hg
    simpa only [d8144, d1430, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48208 (p : Pattern) (guard : d8111 p = 1) : d118 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d118, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35775 p hg
    simpa only [d8111, d118, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d118, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5171 p hg
    simpa only [d8111, d118, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48209 (p : Pattern) (guard : d8112 p = 1) : d1043 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1043, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35329 p hg
    simpa only [d8112, d1043, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1043, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48208 p hg
    simpa only [d8112, d1043, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48210 (p : Pattern) (guard : d8118 p = 1) : d1439 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1439, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48209 p hg
    simpa only [d8118, d1439, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1439, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35728 p hg
    simpa only [d8118, d1439, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48211 (p : Pattern) (guard : d8119 p = 1) : d1440 p ≤ (0 : Int) + d436 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1440, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35720 p hg
    simpa only [d8119, d1440, d436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1440, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48210 p hg
    simpa only [d8119, d1440, d436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48212 (p : Pattern) (guard : d8111 p = 1) : d118 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d118, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35736 p hg
    simpa only [d8111, d118, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d118, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5171 p hg
    simpa only [d8111, d118, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48213 (p : Pattern) (guard : d8112 p = 1) : d118 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35731 p hg
    simpa only [d8112, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48212 p hg
    simpa only [d8112, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48214 (p : Pattern) (guard : d8118 p = 1) : d1441 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1441, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48213 p hg
    simpa only [d8118, d1441, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1441, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35740 p hg
    simpa only [d8118, d1441, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48215 (p : Pattern) (guard : d8124 p = 1) : d1442 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1442, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48214 p hg
    simpa only [d8124, d1442, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1442, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35322 p hg
    simpa only [d8124, d1442, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48216 (p : Pattern) (guard : d8125 p = 1) : d1443 p ≤ (0 : Int) + d437 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d1443, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48211 p hg
    simpa only [d8125, d1443, d437, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d1443, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48215 p hg
    simpa only [d8125, d1443, d437, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48217 (p : Pattern) (guard : d5843 p = 1) : d3 p ≤ (0 : Int) + d119 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1275 p hg
    simpa only [d5843, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20196 p hg
    simpa only [d5843, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48218 (p : Pattern) (guard : d5847 p = 1) : d116 p ≤ (0 : Int) + d317 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d116, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48217 p hg
    simpa only [d5847, d116, d317, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d116, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17806 p hg
    simpa only [d5847, d116, d317, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48219 (p : Pattern) (guard : d5854 p = 1) : d116 p ≤ (0 : Int) + d318 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48218 p hg
    simpa only [d5854, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11639 p hg
    simpa only [d5854, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48220 (p : Pattern) (guard : d8099 p = 1) : d116 p ≤ (0 : Int) + d323 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48219 p hg
    simpa only [d8099, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11639 p hg
    simpa only [d8099, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48221 (p : Pattern) (guard : d8105 p = 1) : d116 p ≤ (0 : Int) + d324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48220 p hg
    simpa only [d8105, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11639 p hg
    simpa only [d8105, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48222 (p : Pattern) (guard : d8111 p = 1) : d132 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d132, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48221 p hg
    simpa only [d8111, d132, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d132, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5171 p hg
    simpa only [d8111, d132, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48223 (p : Pattern) (guard : d8117 p = 1) : d1289 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d1289, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48222 p hg
    simpa only [d8117, d1289, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d1289, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35764 p hg
    simpa only [d8117, d1289, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48224 (p : Pattern) (guard : d8118 p = 1) : d1453 p ≤ (0 : Int) + d416 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1453, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35757 p hg
    simpa only [d8118, d1453, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1453, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48223 p hg
    simpa only [d8118, d1453, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48225 (p : Pattern) (guard : d5843 p = 1) : d3 p ≤ (0 : Int) + d190 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47962 p hg
    simpa only [d5843, d190, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20196 p hg
    simpa only [d5843, d190, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48226 (p : Pattern) (guard : d5847 p = 1) : d116 p ≤ (0 : Int) + d315 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d116, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48225 p hg
    simpa only [d5847, d116, d315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d116, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17806 p hg
    simpa only [d5847, d116, d315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48227 (p : Pattern) (guard : d5854 p = 1) : d116 p ≤ (0 : Int) + d320 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48226 p hg
    simpa only [d5854, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11639 p hg
    simpa only [d5854, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48228 (p : Pattern) (guard : d8099 p = 1) : d116 p ≤ (0 : Int) + d321 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48227 p hg
    simpa only [d8099, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11639 p hg
    simpa only [d8099, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48229 (p : Pattern) (guard : d8105 p = 1) : d116 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48228 p hg
    simpa only [d8105, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11639 p hg
    simpa only [d8105, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48230 (p : Pattern) (guard : d8111 p = 1) : d132 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d132, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48229 p hg
    simpa only [d8111, d132, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d132, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5171 p hg
    simpa only [d8111, d132, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48231 (p : Pattern) (guard : d8117 p = 1) : d862 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d862, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48230 p hg
    simpa only [d8117, d862, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d862, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8214 p hg
    simpa only [d8117, d862, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48232 (p : Pattern) (guard : d8123 p = 1) : d1051 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1051, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48231 p hg
    simpa only [d8123, d1051, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1051, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d1051, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48233 (p : Pattern) (guard : d8124 p = 1) : d1460 p ≤ (0 : Int) + d417 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1460, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48224 p hg
    simpa only [d8124, d1460, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1460, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48232 p hg
    simpa only [d8124, d1460, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48234 (p : Pattern) (guard : d8117 p = 1) : d862 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d862, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35335 p hg
    simpa only [d8117, d862, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d862, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8218 p hg
    simpa only [d8117, d862, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48235 (p : Pattern) (guard : d8123 p = 1) : d1446 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1446, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48234 p hg
    simpa only [d8123, d1446, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1446, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10219 p hg
    simpa only [d8123, d1446, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48236 (p : Pattern) (guard : d8129 p = 1) : d1447 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d1447, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48235 p hg
    simpa only [d8129, d1447, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d1447, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8786 p hg
    simpa only [d8129, d1447, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48237 (p : Pattern) (guard : d8130 p = 1) : d1461 p ≤ (0 : Int) + d418 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d1461, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48233 p hg
    simpa only [d8130, d1461, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d1461, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48236 p hg
    simpa only [d8130, d1461, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48238 (p : Pattern) (guard : d8131 p = 1) : d1462 p ≤ (0 : Int) + d438 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d1462, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48216 p hg
    simpa only [d8131, d1462, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d1462, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48237 p hg
    simpa only [d8131, d1462, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48239 (p : Pattern) (guard : d8123 p = 1) : d1450 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1450, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35371 p hg
    simpa only [d8123, d1450, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1450, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4330 p hg
    simpa only [d8123, d1450, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48240 (p : Pattern) (guard : d8124 p = 1) : d1451 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1451, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35787 p hg
    simpa only [d8124, d1451, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1451, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48239 p hg
    simpa only [d8124, d1451, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48241 (p : Pattern) (guard : d8130 p = 1) : d1452 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d1452, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48240 p hg
    simpa only [d8130, d1452, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d1452, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48039 p hg
    simpa only [d8130, d1452, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48242 (p : Pattern) (guard : d8123 p = 1) : d1453 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1453, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35798 p hg
    simpa only [d8123, d1453, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1453, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10232 p hg
    simpa only [d8123, d1453, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48243 (p : Pattern) (guard : d8129 p = 1) : d1454 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d1454, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48242 p hg
    simpa only [d8129, d1454, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d1454, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8798 p hg
    simpa only [d8129, d1454, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48244 (p : Pattern) (guard : d8135 p = 1) : d1455 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d1455, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48243 p hg
    simpa only [d8135, d1455, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d1455, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48043 p hg
    simpa only [d8135, d1455, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48245 (p : Pattern) (guard : d8136 p = 1) : d1456 p ≤ (0 : Int) + d439 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d1456, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48241 p hg
    simpa only [d8136, d1456, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d1456, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48244 p hg
    simpa only [d8136, d1456, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48246 (p : Pattern) (guard : d8137 p = 1) : d1463 p ≤ (0 : Int) + d440 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d1463, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48238 p hg
    simpa only [d8137, d1463, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d1463, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48245 p hg
    simpa only [d8137, d1463, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48247 (p : Pattern) (guard : d8123 p = 1) : d1450 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1450, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41434 p hg
    simpa only [d8123, d1450, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1450, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4330 p hg
    simpa only [d8123, d1450, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48248 (p : Pattern) (guard : d8124 p = 1) : d1451 p ≤ (0 : Int) + d395 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1451, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38296 p hg
    simpa only [d8124, d1451, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1451, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48247 p hg
    simpa only [d8124, d1451, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48249 (p : Pattern) (guard : d8117 p = 1) : d132 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35283 p hg
    simpa only [d8117, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8230 p hg
    simpa only [d8117, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48250 (p : Pattern) (guard : d8123 p = 1) : d1061 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1061, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48249 p hg
    simpa only [d8123, d1061, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1061, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d1061, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48251 (p : Pattern) (guard : d8129 p = 1) : d1062 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d1062, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48250 p hg
    simpa only [d8129, d1062, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d1062, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8129, d1062, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48252 (p : Pattern) (guard : d8130 p = 1) : d1452 p ≤ (0 : Int) + d397 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d1452, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48248 p hg
    simpa only [d8130, d1452, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d1452, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48251 p hg
    simpa only [d8130, d1452, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48253 (p : Pattern) (guard : d8123 p = 1) : d1453 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1453, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41506 p hg
    simpa only [d8123, d1453, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1453, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10244 p hg
    simpa only [d8123, d1453, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48254 (p : Pattern) (guard : d8129 p = 1) : d1454 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d1454, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48253 p hg
    simpa only [d8129, d1454, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d1454, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8798 p hg
    simpa only [d8129, d1454, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48255 (p : Pattern) (guard : d8135 p = 1) : d1455 p ≤ (0 : Int) + d399 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d1455, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48254 p hg
    simpa only [d8135, d1455, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d1455, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48043 p hg
    simpa only [d8135, d1455, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48256 (p : Pattern) (guard : d8136 p = 1) : d1456 p ≤ (0 : Int) + d400 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d1456, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48252 p hg
    simpa only [d8136, d1456, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d1456, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48255 p hg
    simpa only [d8136, d1456, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48257 (p : Pattern) (guard : d8142 p = 1) : d1458 p ≤ (0 : Int) + d442 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8136 p = 1 := by simpa only [d8142, d1458, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48256 p hg
    simpa only [d8142, d1458, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8141 p = 1 := by simpa only [d8142, d1458, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38307 p hg
    simpa only [d8142, d1458, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48258 (p : Pattern) (guard : d8143 p = 1) : d1478 p ≤ (0 : Int) + d443 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8137 p = 1 := by simpa only [d8143, d1478, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48246 p hg
    simpa only [d8143, d1478, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8142 p = 1 := by simpa only [d8143, d1478, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48257 p hg
    simpa only [d8143, d1478, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48259 (p : Pattern) (guard : d8123 p = 1) : d1479 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1479, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35846 p hg
    simpa only [d8123, d1479, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1479, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4330 p hg
    simpa only [d8123, d1479, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48260 (p : Pattern) (guard : d8124 p = 1) : d1480 p ≤ (0 : Int) + d404 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1480, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35823 p hg
    simpa only [d8124, d1480, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1480, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48259 p hg
    simpa only [d8124, d1480, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48261 (p : Pattern) (guard : d8117 p = 1) : d269 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35828 p hg
    simpa only [d8117, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3860 p hg
    simpa only [d8117, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48262 (p : Pattern) (guard : d8123 p = 1) : d1481 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1481, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48261 p hg
    simpa only [d8123, d1481, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1481, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4394 p hg
    simpa only [d8123, d1481, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48263 (p : Pattern) (guard : d8129 p = 1) : d1482 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d1482, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48262 p hg
    simpa only [d8129, d1482, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d1482, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13990 p hg
    simpa only [d8129, d1482, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48264 (p : Pattern) (guard : d8130 p = 1) : d1483 p ≤ (0 : Int) + d406 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d1483, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48260 p hg
    simpa only [d8130, d1483, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d1483, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48263 p hg
    simpa only [d8130, d1483, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48265 (p : Pattern) (guard : d8123 p = 1) : d1453 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1453, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35839 p hg
    simpa only [d8123, d1453, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1453, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10259 p hg
    simpa only [d8123, d1453, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48266 (p : Pattern) (guard : d0 p = 1) : d1124 p ≤ (0 : Int) + d375 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare48267 (p : Pattern) (guard : d8129 p = 1) : d1484 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d1484, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48265 p hg
    simpa only [d8129, d1484, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d1484, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48266 p hg
    simpa only [d8129, d1484, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48268 (p : Pattern) (guard : d0 p = 1) : d1486 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare48269 (p : Pattern) (guard : d8135 p = 1) : d1487 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d1487, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48267 p hg
    simpa only [d8135, d1487, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d1487, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48268 p hg
    simpa only [d8135, d1487, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48270 (p : Pattern) (guard : d8136 p = 1) : d1488 p ≤ (0 : Int) + d408 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d1488, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48264 p hg
    simpa only [d8136, d1488, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d1488, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48269 p hg
    simpa only [d8136, d1488, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48271 (p : Pattern) (guard : d8123 p = 1) : d1489 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1489, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41521 p hg
    simpa only [d8123, d1489, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1489, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4402 p hg
    simpa only [d8123, d1489, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48272 (p : Pattern) (guard : d8129 p = 1) : d1491 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d1491, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48271 p hg
    simpa only [d8129, d1491, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d1491, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14001 p hg
    simpa only [d8129, d1491, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48273 (p : Pattern) (guard : d0 p = 1) : d1062 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare48274 (p : Pattern) (guard : d8135 p = 1) : d1492 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d1492, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48272 p hg
    simpa only [d8135, d1492, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d1492, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48273 p hg
    simpa only [d8135, d1492, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48275 (p : Pattern) (guard : d0 p = 1) : d1495 p ≤ (0 : Int) + d411 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare48276 (p : Pattern) (guard : d8141 p = 1) : d1496 p ≤ (0 : Int) + d412 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8135 p = 1 := by simpa only [d8141, d1496, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48274 p hg
    simpa only [d8141, d1496, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8141, d1496, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48275 p hg
    simpa only [d8141, d1496, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48277 (p : Pattern) (guard : d8142 p = 1) : d1497 p ≤ (0 : Int) + d413 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8136 p = 1 := by simpa only [d8142, d1497, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48270 p hg
    simpa only [d8142, d1497, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8141 p = 1 := by simpa only [d8142, d1497, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48276 p hg
    simpa only [d8142, d1497, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48278 (p : Pattern) (guard : d8123 p = 1) : d1489 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1489, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41528 p hg
    simpa only [d8123, d1489, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1489, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4402 p hg
    simpa only [d8123, d1489, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48279 (p : Pattern) (guard : d8129 p = 1) : d1491 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d1491, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48278 p hg
    simpa only [d8129, d1491, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d1491, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14001 p hg
    simpa only [d8129, d1491, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48280 (p : Pattern) (guard : d8135 p = 1) : d1492 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d1492, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48279 p hg
    simpa only [d8135, d1492, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d1492, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48273 p hg
    simpa only [d8135, d1492, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48281 (p : Pattern) (guard : d0 p = 1) : d1495 p ≤ (0 : Int) + d421 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare48282 (p : Pattern) (guard : d8141 p = 1) : d1496 p ≤ (0 : Int) + d422 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8135 p = 1 := by simpa only [d8141, d1496, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48280 p hg
    simpa only [d8141, d1496, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8141, d1496, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48281 p hg
    simpa only [d8141, d1496, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48283 (p : Pattern) (guard : d8147 p = 1) : d1498 p ≤ (0 : Int) + d444 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8141 p = 1 := by simpa only [d8147, d1498, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48282 p hg
    simpa only [d8147, d1498, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8147, d1498, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8147, d1498, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48284 (p : Pattern) (guard : d8148 p = 1) : d1499 p ≤ (0 : Int) + d445 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8142 p = 1 := by simpa only [d8148, d1499, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48277 p hg
    simpa only [d8148, d1499, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8147 p = 1 := by simpa only [d8148, d1499, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48283 p hg
    simpa only [d8148, d1499, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48285 (p : Pattern) (guard : d8149 p = 1) : d1500 p ≤ (0 : Int) + d446 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8143 p = 1 := by simpa only [d8149, d1500, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48258 p hg
    simpa only [d8149, d1500, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8148 p = 1 := by simpa only [d8149, d1500, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48284 p hg
    simpa only [d8149, d1500, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48286 (p : Pattern) (guard : d8150 p = 1) : d1501 p ≤ (0 : Int) + d447 p := by
  cases selected : p 71 with
  | false =>
    have hg : d8144 p = 1 := by simpa only [d8150, d1501, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48207 p hg
    simpa only [d8150, d1501, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8149 p = 1 := by simpa only [d8150, d1501, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48285 p hg
    simpa only [d8150, d1501, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48287 (p : Pattern) (guard : d8151 p = 1) : d1502 p ≤ (0 : Int) + d447 p := by
  cases selected : p 49 with
  | false =>
    have hg : d8145 p = 1 := by simpa only [d8151, d1502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48142 p hg
    simpa only [d8151, d1502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8150 p = 1 := by simpa only [d8151, d1502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48286 p hg
    simpa only [d8151, d1502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48288 (p : Pattern) (guard : d8152 p = 1) : d1503 p ≤ (0 : Int) + d447 p := by
  cases selected : p 48 with
  | false =>
    have hg : d8146 p = 1 := by simpa only [d8152, d1503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48057 p hg
    simpa only [d8152, d1503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8151 p = 1 := by simpa only [d8152, d1503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48287 p hg
    simpa only [d8152, d1503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48289 (p : Pattern) (guard : d8145 p = 1) : d447 p ≤ (0 : Int) + d447 p := by
  omega
theorem compare48290 (p : Pattern) (guard : d8144 p = 1) : d427 p ≤ (0 : Int) + d427 p := by
  omega
theorem compare48291 (p : Pattern) (guard : d8125 p = 1) : d437 p ≤ (0 : Int) + d437 p := by
  omega
theorem compare48292 (p : Pattern) (guard : d8131 p = 1) : d454 p ≤ (0 : Int) + d438 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d454, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48291 p hg
    simpa only [d8131, d454, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d454, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38291 p hg
    simpa only [d8131, d454, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48293 (p : Pattern) (guard : d8137 p = 1) : d458 p ≤ (0 : Int) + d440 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d458, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48292 p hg
    simpa only [d8137, d458, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d458, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41749 p hg
    simpa only [d8137, d458, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48294 (p : Pattern) (guard : d8143 p = 1) : d464 p ≤ (0 : Int) + d443 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8137 p = 1 := by simpa only [d8143, d464, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48293 p hg
    simpa only [d8143, d464, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8142 p = 1 := by simpa only [d8143, d464, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35813 p hg
    simpa only [d8143, d464, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48295 (p : Pattern) (guard : d8112 p = 1) : d346 p ≤ (0 : Int) + d346 p := by
  omega
theorem compare48296 (p : Pattern) (guard : d8118 p = 1) : d465 p ≤ (0 : Int) + d402 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d465, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48295 p hg
    simpa only [d8118, d465, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d465, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35855 p hg
    simpa only [d8118, d465, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48297 (p : Pattern) (guard : d8123 p = 1) : d403 p ≤ (0 : Int) + d403 p := by
  omega
theorem compare48298 (p : Pattern) (guard : d8124 p = 1) : d466 p ≤ (0 : Int) + d404 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d466, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48296 p hg
    simpa only [d8124, d466, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d466, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48297 p hg
    simpa only [d8124, d466, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48299 (p : Pattern) (guard : d8130 p = 1) : d467 p ≤ (0 : Int) + d406 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d467, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48298 p hg
    simpa only [d8130, d467, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d467, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46203 p hg
    simpa only [d8130, d467, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
