/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons075
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare10640 (p : Pattern) (guard : d4148 p = 1) : d1402 p ≤ (0 : Int) + d1162 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1402, d1162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10639 p hg
    simpa only [d1402, d1162, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1402, d1162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3633 p hg
    simpa only [d1402, d1162, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10641 (p : Pattern) (guard : d4148 p = 1) : d1403 p ≤ (0 : Int) + d1163 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1403, d1163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10638 p hg
    simpa only [d1403, d1163, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1403, d1163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10640 p hg
    simpa only [d1403, d1163, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10642 (p : Pattern) (guard : d4148 p = 1) : d1404 p ≤ (0 : Int) + d1166 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1404, d1166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8057 p hg
    simpa only [d1404, d1166, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1404, d1166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9809 p hg
    simpa only [d1404, d1166, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10643 (p : Pattern) (guard : d4148 p = 1) : d1405 p ≤ (0 : Int) + d1168 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1405, d1168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8060 p hg
    simpa only [d1405, d1168, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1405, d1168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3647 p hg
    simpa only [d1405, d1168, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10644 (p : Pattern) (guard : d4148 p = 1) : d1406 p ≤ (0 : Int) + d1169 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1406, d1169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10642 p hg
    simpa only [d1406, d1169, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1406, d1169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10643 p hg
    simpa only [d1406, d1169, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10645 (p : Pattern) (guard : d4148 p = 1) : d1407 p ≤ (0 : Int) + d1172 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1407, d1172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8064 p hg
    simpa only [d1407, d1172, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1407, d1172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9817 p hg
    simpa only [d1407, d1172, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10646 (p : Pattern) (guard : d4148 p = 1) : d177 p ≤ (0 : Int) + d1173 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d177, d1173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8068 p hg
    simpa only [d177, d1173, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d177, d1173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9821 p hg
    simpa only [d177, d1173, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10647 (p : Pattern) (guard : d4148 p = 1) : d1408 p ≤ (0 : Int) + d1174 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1408, d1174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10645 p hg
    simpa only [d1408, d1174, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1408, d1174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10646 p hg
    simpa only [d1408, d1174, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10648 (p : Pattern) (guard : d4148 p = 1) : d1409 p ≤ (0 : Int) + d1175 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1409, d1175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10644 p hg
    simpa only [d1409, d1175, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1409, d1175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10647 p hg
    simpa only [d1409, d1175, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10649 (p : Pattern) (guard : d4148 p = 1) : d1410 p ≤ (0 : Int) + d1176 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1410, d1176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10641 p hg
    simpa only [d1410, d1176, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1410, d1176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10648 p hg
    simpa only [d1410, d1176, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10650 (p : Pattern) (guard : d4148 p = 1) : d1411 p ≤ (0 : Int) + d1179 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1411, d1179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8076 p hg
    simpa only [d1411, d1179, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1411, d1179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3620 p hg
    simpa only [d1411, d1179, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10651 (p : Pattern) (guard : d4148 p = 1) : d1412 p ≤ (0 : Int) + d1180 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1412, d1180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3642 p hg
    simpa only [d1412, d1180, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1412, d1180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10650 p hg
    simpa only [d1412, d1180, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10652 (p : Pattern) (guard : d4148 p = 1) : d1413 p ≤ (0 : Int) + d1182 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1413, d1182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8079 p hg
    simpa only [d1413, d1182, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1413, d1182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3647 p hg
    simpa only [d1413, d1182, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10653 (p : Pattern) (guard : d4148 p = 1) : d1414 p ≤ (0 : Int) + d1183 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1414, d1183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10652 p hg
    simpa only [d1414, d1183, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1414, d1183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2348 p hg
    simpa only [d1414, d1183, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10654 (p : Pattern) (guard : d4148 p = 1) : d1415 p ≤ (0 : Int) + d1184 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1415, d1184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10651 p hg
    simpa only [d1415, d1184, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1415, d1184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10653 p hg
    simpa only [d1415, d1184, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10655 (p : Pattern) (guard : d4148 p = 1) : d1416 p ≤ (0 : Int) + d1186 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1416, d1186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8084 p hg
    simpa only [d1416, d1186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1416, d1186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9836 p hg
    simpa only [d1416, d1186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10656 (p : Pattern) (guard : d4148 p = 1) : d1417 p ≤ (0 : Int) + d1182 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1417, d1182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8086 p hg
    simpa only [d1417, d1182, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1417, d1182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3647 p hg
    simpa only [d1417, d1182, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10657 (p : Pattern) (guard : d4148 p = 1) : d1418 p ≤ (0 : Int) + d1187 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1418, d1187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10655 p hg
    simpa only [d1418, d1187, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1418, d1187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10656 p hg
    simpa only [d1418, d1187, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10658 (p : Pattern) (guard : d4148 p = 1) : d972 p ≤ (0 : Int) + d1188 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d972, d1188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8086 p hg
    simpa only [d972, d1188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d972, d1188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2348 p hg
    simpa only [d972, d1188, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10659 (p : Pattern) (guard : d4148 p = 1) : d974 p ≤ (0 : Int) + d1189 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d974, d1189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10658 p hg
    simpa only [d974, d1189, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d974, d1189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2348 p hg
    simpa only [d974, d1189, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10660 (p : Pattern) (guard : d4148 p = 1) : d1419 p ≤ (0 : Int) + d1190 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1419, d1190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10657 p hg
    simpa only [d1419, d1190, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1419, d1190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10659 p hg
    simpa only [d1419, d1190, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10661 (p : Pattern) (guard : d4148 p = 1) : d1420 p ≤ (0 : Int) + d1191 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1420, d1191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10654 p hg
    simpa only [d1420, d1191, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1420, d1191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10660 p hg
    simpa only [d1420, d1191, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10662 (p : Pattern) (guard : d4148 p = 1) : d1421 p ≤ (0 : Int) + d1192 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1421, d1192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10649 p hg
    simpa only [d1421, d1192, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1421, d1192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10661 p hg
    simpa only [d1421, d1192, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10663 (p : Pattern) (guard : d4148 p = 1) : d1412 p ≤ (0 : Int) + d1195 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1412, d1195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3658 p hg
    simpa only [d1412, d1195, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1412, d1195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10650 p hg
    simpa only [d1412, d1195, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10664 (p : Pattern) (guard : d4148 p = 1) : d1415 p ≤ (0 : Int) + d1196 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1415, d1196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10663 p hg
    simpa only [d1415, d1196, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1415, d1196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10653 p hg
    simpa only [d1415, d1196, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10665 (p : Pattern) (guard : d4148 p = 1) : d1416 p ≤ (0 : Int) + d1198 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1416, d1198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8099 p hg
    simpa only [d1416, d1198, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1416, d1198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9836 p hg
    simpa only [d1416, d1198, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10666 (p : Pattern) (guard : d4148 p = 1) : d1418 p ≤ (0 : Int) + d1199 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1418, d1199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10665 p hg
    simpa only [d1418, d1199, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1418, d1199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10656 p hg
    simpa only [d1418, d1199, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10667 (p : Pattern) (guard : d4148 p = 1) : d1419 p ≤ (0 : Int) + d1200 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1419, d1200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10666 p hg
    simpa only [d1419, d1200, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1419, d1200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10659 p hg
    simpa only [d1419, d1200, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10668 (p : Pattern) (guard : d4148 p = 1) : d1420 p ≤ (0 : Int) + d1201 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1420, d1201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10664 p hg
    simpa only [d1420, d1201, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1420, d1201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10667 p hg
    simpa only [d1420, d1201, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10669 (p : Pattern) (guard : d4148 p = 1) : d96 p ≤ (0 : Int) + d1205 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d96, d1205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3670 p hg
    simpa only [d96, d1205, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d96, d1205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9854 p hg
    simpa only [d96, d1205, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10670 (p : Pattern) (guard : d4148 p = 1) : d1422 p ≤ (0 : Int) + d1206 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1422, d1206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10668 p hg
    simpa only [d1422, d1206, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1422, d1206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10669 p hg
    simpa only [d1422, d1206, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10671 (p : Pattern) (guard : d4148 p = 1) : d1423 p ≤ (0 : Int) + d1207 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1423, d1207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10662 p hg
    simpa only [d1423, d1207, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1423, d1207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10670 p hg
    simpa only [d1423, d1207, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10672 (p : Pattern) (guard : d4148 p = 1) : d1399 p ≤ (0 : Int) + d1210 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1399, d1210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8114 p hg
    simpa only [d1399, d1210, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1399, d1210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3620 p hg
    simpa only [d1399, d1210, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10673 (p : Pattern) (guard : d4148 p = 1) : d1400 p ≤ (0 : Int) + d1211 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1400, d1211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3678 p hg
    simpa only [d1400, d1211, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1400, d1211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10672 p hg
    simpa only [d1400, d1211, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10674 (p : Pattern) (guard : d4148 p = 1) : d1401 p ≤ (0 : Int) + d1213 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1401, d1213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8118 p hg
    simpa only [d1401, d1213, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1401, d1213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3628 p hg
    simpa only [d1401, d1213, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10675 (p : Pattern) (guard : d4148 p = 1) : d1402 p ≤ (0 : Int) + d1214 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1402, d1214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10674 p hg
    simpa only [d1402, d1214, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1402, d1214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3633 p hg
    simpa only [d1402, d1214, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10676 (p : Pattern) (guard : d4148 p = 1) : d1403 p ≤ (0 : Int) + d1215 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1403, d1215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10673 p hg
    simpa only [d1403, d1215, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1403, d1215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10675 p hg
    simpa only [d1403, d1215, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10677 (p : Pattern) (guard : d4148 p = 1) : d1416 p ≤ (0 : Int) + d1216 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1416, d1216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8124 p hg
    simpa only [d1416, d1216, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1416, d1216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9836 p hg
    simpa only [d1416, d1216, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10678 (p : Pattern) (guard : d4148 p = 1) : d1405 p ≤ (0 : Int) + d1182 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1405, d1182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8127 p hg
    simpa only [d1405, d1182, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1405, d1182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3647 p hg
    simpa only [d1405, d1182, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10679 (p : Pattern) (guard : d4148 p = 1) : d1424 p ≤ (0 : Int) + d1217 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1424, d1217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10677 p hg
    simpa only [d1424, d1217, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1424, d1217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10678 p hg
    simpa only [d1424, d1217, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10680 (p : Pattern) (guard : d4148 p = 1) : d1407 p ≤ (0 : Int) + d1218 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1407, d1218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8127 p hg
    simpa only [d1407, d1218, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1407, d1218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9817 p hg
    simpa only [d1407, d1218, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10681 (p : Pattern) (guard : d4148 p = 1) : d1408 p ≤ (0 : Int) + d1219 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1408, d1219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10680 p hg
    simpa only [d1408, d1219, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1408, d1219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10646 p hg
    simpa only [d1408, d1219, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10682 (p : Pattern) (guard : d4148 p = 1) : d1425 p ≤ (0 : Int) + d1220 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1425, d1220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10679 p hg
    simpa only [d1425, d1220, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1425, d1220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10681 p hg
    simpa only [d1425, d1220, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10683 (p : Pattern) (guard : d4148 p = 1) : d1426 p ≤ (0 : Int) + d1221 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1426, d1221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10676 p hg
    simpa only [d1426, d1221, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1426, d1221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10682 p hg
    simpa only [d1426, d1221, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10684 (p : Pattern) (guard : d4148 p = 1) : d1412 p ≤ (0 : Int) + d1223 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1412, d1223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3690 p hg
    simpa only [d1412, d1223, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1412, d1223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10650 p hg
    simpa only [d1412, d1223, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10685 (p : Pattern) (guard : d4148 p = 1) : d1415 p ≤ (0 : Int) + d1224 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1415, d1224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10684 p hg
    simpa only [d1415, d1224, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1415, d1224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10653 p hg
    simpa only [d1415, d1224, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10686 (p : Pattern) (guard : d4148 p = 1) : d1416 p ≤ (0 : Int) + d1225 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1416, d1225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8076 p hg
    simpa only [d1416, d1225, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1416, d1225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9836 p hg
    simpa only [d1416, d1225, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10687 (p : Pattern) (guard : d4148 p = 1) : d1418 p ≤ (0 : Int) + d1226 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1418, d1226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10686 p hg
    simpa only [d1418, d1226, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1418, d1226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10656 p hg
    simpa only [d1418, d1226, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10688 (p : Pattern) (guard : d4148 p = 1) : d1419 p ≤ (0 : Int) + d1227 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1419, d1227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10687 p hg
    simpa only [d1419, d1227, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1419, d1227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10659 p hg
    simpa only [d1419, d1227, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10689 (p : Pattern) (guard : d4148 p = 1) : d1420 p ≤ (0 : Int) + d1228 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1420, d1228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10685 p hg
    simpa only [d1420, d1228, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1420, d1228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10688 p hg
    simpa only [d1420, d1228, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10690 (p : Pattern) (guard : d4148 p = 1) : d1427 p ≤ (0 : Int) + d1229 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1427, d1229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10683 p hg
    simpa only [d1427, d1229, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1427, d1229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10689 p hg
    simpa only [d1427, d1229, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10691 (p : Pattern) (guard : d4148 p = 1) : d1412 p ≤ (0 : Int) + d1231 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1412, d1231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3698 p hg
    simpa only [d1412, d1231, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1412, d1231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10650 p hg
    simpa only [d1412, d1231, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10692 (p : Pattern) (guard : d4148 p = 1) : d1415 p ≤ (0 : Int) + d1232 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1415, d1232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10691 p hg
    simpa only [d1415, d1232, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1415, d1232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10653 p hg
    simpa only [d1415, d1232, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10693 (p : Pattern) (guard : d4148 p = 1) : d1420 p ≤ (0 : Int) + d1233 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1420, d1233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10692 p hg
    simpa only [d1420, d1233, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1420, d1233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10688 p hg
    simpa only [d1420, d1233, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10694 (p : Pattern) (guard : d4148 p = 1) : d1428 p ≤ (0 : Int) + d1234 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1428, d1234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10693 p hg
    simpa only [d1428, d1234, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1428, d1234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2348 p hg
    simpa only [d1428, d1234, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10695 (p : Pattern) (guard : d4148 p = 1) : d1429 p ≤ (0 : Int) + d1235 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1429, d1235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10690 p hg
    simpa only [d1429, d1235, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1429, d1235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10694 p hg
    simpa only [d1429, d1235, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10696 (p : Pattern) (guard : d4148 p = 1) : d1430 p ≤ (0 : Int) + d1236 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1430, d1236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10671 p hg
    simpa only [d1430, d1236, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1430, d1236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10695 p hg
    simpa only [d1430, d1236, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10697 (p : Pattern) (guard : d4148 p = 1) : d1399 p ≤ (0 : Int) + d1239 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1399, d1239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8153 p hg
    simpa only [d1399, d1239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1399, d1239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3620 p hg
    simpa only [d1399, d1239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10698 (p : Pattern) (guard : d4148 p = 1) : d1400 p ≤ (0 : Int) + d1240 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1400, d1240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3709 p hg
    simpa only [d1400, d1240, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1400, d1240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10697 p hg
    simpa only [d1400, d1240, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10699 (p : Pattern) (guard : d4148 p = 1) : d1401 p ≤ (0 : Int) + d1242 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1401, d1242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8157 p hg
    simpa only [d1401, d1242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1401, d1242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3628 p hg
    simpa only [d1401, d1242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10700 (p : Pattern) (guard : d4148 p = 1) : d1402 p ≤ (0 : Int) + d1243 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1402, d1243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10699 p hg
    simpa only [d1402, d1243, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1402, d1243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3633 p hg
    simpa only [d1402, d1243, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10701 (p : Pattern) (guard : d4148 p = 1) : d1403 p ≤ (0 : Int) + d1244 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1403, d1244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10698 p hg
    simpa only [d1403, d1244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1403, d1244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10700 p hg
    simpa only [d1403, d1244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10702 (p : Pattern) (guard : d4148 p = 1) : d1431 p ≤ (0 : Int) + d1245 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1431, d1245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8163 p hg
    simpa only [d1431, d1245, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1431, d1245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9901 p hg
    simpa only [d1431, d1245, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10703 (p : Pattern) (guard : d4148 p = 1) : d1405 p ≤ (0 : Int) + d1246 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1405, d1246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8064 p hg
    simpa only [d1405, d1246, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1405, d1246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3647 p hg
    simpa only [d1405, d1246, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10704 (p : Pattern) (guard : d4148 p = 1) : d1432 p ≤ (0 : Int) + d1247 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1432, d1247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10702 p hg
    simpa only [d1432, d1247, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1432, d1247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10703 p hg
    simpa only [d1432, d1247, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10705 (p : Pattern) (guard : d4148 p = 1) : d1433 p ≤ (0 : Int) + d1248 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1433, d1248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10704 p hg
    simpa only [d1433, d1248, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1433, d1248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10681 p hg
    simpa only [d1433, d1248, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10706 (p : Pattern) (guard : d4148 p = 1) : d1434 p ≤ (0 : Int) + d1249 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1434, d1249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10701 p hg
    simpa only [d1434, d1249, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1434, d1249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10705 p hg
    simpa only [d1434, d1249, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10707 (p : Pattern) (guard : d4148 p = 1) : d1412 p ≤ (0 : Int) + d1251 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1412, d1251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3723 p hg
    simpa only [d1412, d1251, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1412, d1251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10650 p hg
    simpa only [d1412, d1251, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10708 (p : Pattern) (guard : d4148 p = 1) : d1415 p ≤ (0 : Int) + d1252 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1415, d1252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10707 p hg
    simpa only [d1415, d1252, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1415, d1252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10653 p hg
    simpa only [d1415, d1252, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10709 (p : Pattern) (guard : d4148 p = 1) : d1416 p ≤ (0 : Int) + d1253 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1416, d1253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8174 p hg
    simpa only [d1416, d1253, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1416, d1253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9836 p hg
    simpa only [d1416, d1253, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10710 (p : Pattern) (guard : d4148 p = 1) : d1418 p ≤ (0 : Int) + d1254 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1418, d1254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10709 p hg
    simpa only [d1418, d1254, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1418, d1254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10656 p hg
    simpa only [d1418, d1254, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10711 (p : Pattern) (guard : d4148 p = 1) : d1419 p ≤ (0 : Int) + d1255 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1419, d1255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10710 p hg
    simpa only [d1419, d1255, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1419, d1255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10659 p hg
    simpa only [d1419, d1255, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10712 (p : Pattern) (guard : d4148 p = 1) : d1420 p ≤ (0 : Int) + d1256 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1420, d1256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10708 p hg
    simpa only [d1420, d1256, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1420, d1256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10711 p hg
    simpa only [d1420, d1256, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10713 (p : Pattern) (guard : d4148 p = 1) : d1435 p ≤ (0 : Int) + d1257 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1435, d1257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10706 p hg
    simpa only [d1435, d1257, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1435, d1257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10712 p hg
    simpa only [d1435, d1257, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10714 (p : Pattern) (guard : d4148 p = 1) : d1422 p ≤ (0 : Int) + d1258 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1422, d1258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10661 p hg
    simpa only [d1422, d1258, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1422, d1258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10669 p hg
    simpa only [d1422, d1258, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10715 (p : Pattern) (guard : d4148 p = 1) : d1436 p ≤ (0 : Int) + d1259 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1436, d1259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10713 p hg
    simpa only [d1436, d1259, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1436, d1259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10714 p hg
    simpa only [d1436, d1259, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10716 (p : Pattern) (guard : d4148 p = 1) : d1399 p ≤ (0 : Int) + d1179 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1399, d1179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8182 p hg
    simpa only [d1399, d1179, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1399, d1179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3620 p hg
    simpa only [d1399, d1179, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10717 (p : Pattern) (guard : d4148 p = 1) : d1400 p ≤ (0 : Int) + d1195 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1400, d1195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3658 p hg
    simpa only [d1400, d1195, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1400, d1195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10716 p hg
    simpa only [d1400, d1195, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10718 (p : Pattern) (guard : d4148 p = 1) : d1403 p ≤ (0 : Int) + d1260 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1403, d1260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10717 p hg
    simpa only [d1403, d1260, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1403, d1260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10675 p hg
    simpa only [d1403, d1260, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10719 (p : Pattern) (guard : d4148 p = 1) : d1424 p ≤ (0 : Int) + d1199 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1424, d1199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10665 p hg
    simpa only [d1424, d1199, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1424, d1199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10678 p hg
    simpa only [d1424, d1199, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10720 (p : Pattern) (guard : d4148 p = 1) : d1425 p ≤ (0 : Int) + d1261 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1425, d1261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10719 p hg
    simpa only [d1425, d1261, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1425, d1261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10681 p hg
    simpa only [d1425, d1261, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10721 (p : Pattern) (guard : d4148 p = 1) : d1426 p ≤ (0 : Int) + d1262 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1426, d1262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10718 p hg
    simpa only [d1426, d1262, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1426, d1262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10720 p hg
    simpa only [d1426, d1262, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10722 (p : Pattern) (guard : d4148 p = 1) : d1412 p ≤ (0 : Int) + d1263 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1412, d1263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3737 p hg
    simpa only [d1412, d1263, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1412, d1263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10650 p hg
    simpa only [d1412, d1263, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10723 (p : Pattern) (guard : d4148 p = 1) : d1415 p ≤ (0 : Int) + d1264 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1415, d1264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10722 p hg
    simpa only [d1415, d1264, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1415, d1264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10653 p hg
    simpa only [d1415, d1264, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10724 (p : Pattern) (guard : d4148 p = 1) : d1420 p ≤ (0 : Int) + d1265 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1420, d1265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10723 p hg
    simpa only [d1420, d1265, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1420, d1265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10688 p hg
    simpa only [d1420, d1265, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10725 (p : Pattern) (guard : d4148 p = 1) : d1427 p ≤ (0 : Int) + d1266 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1427, d1266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10721 p hg
    simpa only [d1427, d1266, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1427, d1266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10724 p hg
    simpa only [d1427, d1266, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10726 (p : Pattern) (guard : d4148 p = 1) : d1428 p ≤ (0 : Int) + d1267 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1428, d1267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10689 p hg
    simpa only [d1428, d1267, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1428, d1267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2348 p hg
    simpa only [d1428, d1267, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10727 (p : Pattern) (guard : d4148 p = 1) : d1429 p ≤ (0 : Int) + d1268 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1429, d1268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10725 p hg
    simpa only [d1429, d1268, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1429, d1268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10726 p hg
    simpa only [d1429, d1268, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10728 (p : Pattern) (guard : d4148 p = 1) : d1437 p ≤ (0 : Int) + d1269 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1437, d1269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10715 p hg
    simpa only [d1437, d1269, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1437, d1269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10727 p hg
    simpa only [d1437, d1269, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10729 (p : Pattern) (guard : d4148 p = 1) : d1438 p ≤ (0 : Int) + d1270 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1438, d1270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10696 p hg
    simpa only [d1438, d1270, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1438, d1270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10728 p hg
    simpa only [d1438, d1270, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10730 (p : Pattern) (guard : d4148 p = 1) : d1439 p ≤ (0 : Int) + d1275 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1439, d1275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8201 p hg
    simpa only [d1439, d1275, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1439, d1275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3754 p hg
    simpa only [d1439, d1275, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10731 (p : Pattern) (guard : d4148 p = 1) : d1440 p ≤ (0 : Int) + d1276 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1440, d1276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3751 p hg
    simpa only [d1440, d1276, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1440, d1276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10730 p hg
    simpa only [d1440, d1276, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10732 (p : Pattern) (guard : d4148 p = 1) : d1441 p ≤ (0 : Int) + d1279 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1441, d1279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8205 p hg
    simpa only [d1441, d1279, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1441, d1279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3762 p hg
    simpa only [d1441, d1279, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10733 (p : Pattern) (guard : d4148 p = 1) : d1442 p ≤ (0 : Int) + d1281 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1442, d1281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10732 p hg
    simpa only [d1442, d1281, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1442, d1281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3765 p hg
    simpa only [d1442, d1281, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10734 (p : Pattern) (guard : d4148 p = 1) : d1443 p ≤ (0 : Int) + d1282 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1443, d1282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10731 p hg
    simpa only [d1443, d1282, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1443, d1282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10733 p hg
    simpa only [d1443, d1282, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10735 (p : Pattern) (guard : d4148 p = 1) : d1444 p ≤ (0 : Int) + d1285 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1444, d1285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8212 p hg
    simpa only [d1444, d1285, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1444, d1285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9944 p hg
    simpa only [d1444, d1285, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10736 (p : Pattern) (guard : d4148 p = 1) : d1051 p ≤ (0 : Int) + d1287 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1051, d1287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8215 p hg
    simpa only [d1051, d1287, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1051, d1287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2348 p hg
    simpa only [d1051, d1287, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10737 (p : Pattern) (guard : d4148 p = 1) : d1445 p ≤ (0 : Int) + d1288 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1445, d1288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10735 p hg
    simpa only [d1445, d1288, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1445, d1288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10736 p hg
    simpa only [d1445, d1288, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10738 (p : Pattern) (guard : d4148 p = 1) : d1446 p ≤ (0 : Int) + d1291 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1446, d1291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8219 p hg
    simpa only [d1446, d1291, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1446, d1291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9952 p hg
    simpa only [d1446, d1291, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10739 (p : Pattern) (guard : d4148 p = 1) : d1054 p ≤ (0 : Int) + d1292 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1054, d1292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8223 p hg
    simpa only [d1054, d1292, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1054, d1292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2348 p hg
    simpa only [d1054, d1292, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10740 (p : Pattern) (guard : d4148 p = 1) : d1447 p ≤ (0 : Int) + d1293 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1447, d1293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10738 p hg
    simpa only [d1447, d1293, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1447, d1293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10739 p hg
    simpa only [d1447, d1293, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10741 (p : Pattern) (guard : d4148 p = 1) : d1448 p ≤ (0 : Int) + d1294 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1448, d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10737 p hg
    simpa only [d1448, d1294, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1448, d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10740 p hg
    simpa only [d1448, d1294, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10742 (p : Pattern) (guard : d4148 p = 1) : d1449 p ≤ (0 : Int) + d1295 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1449, d1295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10734 p hg
    simpa only [d1449, d1295, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1449, d1295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10741 p hg
    simpa only [d1449, d1295, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10743 (p : Pattern) (guard : d4148 p = 1) : d1450 p ≤ (0 : Int) + d1298 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1450, d1298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8231 p hg
    simpa only [d1450, d1298, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1450, d1298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3754 p hg
    simpa only [d1450, d1298, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10744 (p : Pattern) (guard : d4148 p = 1) : d1451 p ≤ (0 : Int) + d1299 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1451, d1299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3774 p hg
    simpa only [d1451, d1299, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1451, d1299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10743 p hg
    simpa only [d1451, d1299, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10745 (p : Pattern) (guard : d4148 p = 1) : d1061 p ≤ (0 : Int) + d1300 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1061, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8234 p hg
    simpa only [d1061, d1300, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1061, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2348 p hg
    simpa only [d1061, d1300, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10746 (p : Pattern) (guard : d4148 p = 1) : d1062 p ≤ (0 : Int) + d1301 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1062, d1301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10745 p hg
    simpa only [d1062, d1301, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1062, d1301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2348 p hg
    simpa only [d1062, d1301, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10747 (p : Pattern) (guard : d4148 p = 1) : d1452 p ≤ (0 : Int) + d1302 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1452, d1302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10744 p hg
    simpa only [d1452, d1302, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1452, d1302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10746 p hg
    simpa only [d1452, d1302, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10748 (p : Pattern) (guard : d4148 p = 1) : d1453 p ≤ (0 : Int) + d1304 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1453, d1304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8239 p hg
    simpa only [d1453, d1304, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1453, d1304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9970 p hg
    simpa only [d1453, d1304, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10749 (p : Pattern) (guard : d4148 p = 1) : d1064 p ≤ (0 : Int) + d1300 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1064, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8241 p hg
    simpa only [d1064, d1300, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1064, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2348 p hg
    simpa only [d1064, d1300, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10750 (p : Pattern) (guard : d4148 p = 1) : d1454 p ≤ (0 : Int) + d1305 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1454, d1305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10748 p hg
    simpa only [d1454, d1305, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1454, d1305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10749 p hg
    simpa only [d1454, d1305, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10751 (p : Pattern) (guard : d4148 p = 1) : d1066 p ≤ (0 : Int) + d1301 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1066, d1301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10749 p hg
    simpa only [d1066, d1301, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1066, d1301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2348 p hg
    simpa only [d1066, d1301, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10752 (p : Pattern) (guard : d4148 p = 1) : d1455 p ≤ (0 : Int) + d1306 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1455, d1306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10750 p hg
    simpa only [d1455, d1306, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1455, d1306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10751 p hg
    simpa only [d1455, d1306, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10753 (p : Pattern) (guard : d4148 p = 1) : d1456 p ≤ (0 : Int) + d1307 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1456, d1307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10747 p hg
    simpa only [d1456, d1307, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1456, d1307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10752 p hg
    simpa only [d1456, d1307, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10754 (p : Pattern) (guard : d4148 p = 1) : d1457 p ≤ (0 : Int) + d1308 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1457, d1308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10742 p hg
    simpa only [d1457, d1308, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1457, d1308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10753 p hg
    simpa only [d1457, d1308, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10755 (p : Pattern) (guard : d4148 p = 1) : d1451 p ≤ (0 : Int) + d1310 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1451, d1310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3787 p hg
    simpa only [d1451, d1310, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1451, d1310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10743 p hg
    simpa only [d1451, d1310, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10756 (p : Pattern) (guard : d4148 p = 1) : d1452 p ≤ (0 : Int) + d1311 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1452, d1311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10755 p hg
    simpa only [d1452, d1311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1452, d1311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10746 p hg
    simpa only [d1452, d1311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10757 (p : Pattern) (guard : d4148 p = 1) : d1453 p ≤ (0 : Int) + d1313 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1453, d1313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8253 p hg
    simpa only [d1453, d1313, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1453, d1313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9970 p hg
    simpa only [d1453, d1313, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10758 (p : Pattern) (guard : d4148 p = 1) : d1454 p ≤ (0 : Int) + d1314 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1454, d1314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10757 p hg
    simpa only [d1454, d1314, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1454, d1314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10749 p hg
    simpa only [d1454, d1314, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10759 (p : Pattern) (guard : d4148 p = 1) : d1455 p ≤ (0 : Int) + d1315 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1455, d1315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10758 p hg
    simpa only [d1455, d1315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1455, d1315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10751 p hg
    simpa only [d1455, d1315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10760 (p : Pattern) (guard : d4148 p = 1) : d1456 p ≤ (0 : Int) + d1316 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1456, d1316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10756 p hg
    simpa only [d1456, d1316, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1456, d1316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10759 p hg
    simpa only [d1456, d1316, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10761 (p : Pattern) (guard : d4148 p = 1) : d1458 p ≤ (0 : Int) + d1317 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1458, d1317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10760 p hg
    simpa only [d1458, d1317, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1458, d1317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9987 p hg
    simpa only [d1458, d1317, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10762 (p : Pattern) (guard : d4148 p = 1) : d1459 p ≤ (0 : Int) + d1318 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1459, d1318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10754 p hg
    simpa only [d1459, d1318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1459, d1318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10761 p hg
    simpa only [d1459, d1318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10763 (p : Pattern) (guard : d4148 p = 1) : d1439 p ≤ (0 : Int) + d1298 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1439, d1298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8264 p hg
    simpa only [d1439, d1298, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1439, d1298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3754 p hg
    simpa only [d1439, d1298, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10764 (p : Pattern) (guard : d4148 p = 1) : d1440 p ≤ (0 : Int) + d1321 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1440, d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3799 p hg
    simpa only [d1440, d1321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1440, d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10763 p hg
    simpa only [d1440, d1321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10765 (p : Pattern) (guard : d4148 p = 1) : d1441 p ≤ (0 : Int) + d1323 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1441, d1323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8267 p hg
    simpa only [d1441, d1323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1441, d1323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3762 p hg
    simpa only [d1441, d1323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10766 (p : Pattern) (guard : d4148 p = 1) : d1442 p ≤ (0 : Int) + d1324 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1442, d1324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10765 p hg
    simpa only [d1442, d1324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1442, d1324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3765 p hg
    simpa only [d1442, d1324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10767 (p : Pattern) (guard : d4148 p = 1) : d1443 p ≤ (0 : Int) + d1325 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1443, d1325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10764 p hg
    simpa only [d1443, d1325, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1443, d1325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10766 p hg
    simpa only [d1443, d1325, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10768 (p : Pattern) (guard : d4148 p = 1) : d1453 p ≤ (0 : Int) + d1326 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1453, d1326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8273 p hg
    simpa only [d1453, d1326, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1453, d1326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9970 p hg
    simpa only [d1453, d1326, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10769 (p : Pattern) (guard : d4148 p = 1) : d1051 p ≤ (0 : Int) + d1300 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1051, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8219 p hg
    simpa only [d1051, d1300, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1051, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2348 p hg
    simpa only [d1051, d1300, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10770 (p : Pattern) (guard : d4148 p = 1) : d1460 p ≤ (0 : Int) + d1327 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1460, d1327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10768 p hg
    simpa only [d1460, d1327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1460, d1327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10769 p hg
    simpa only [d1460, d1327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10771 (p : Pattern) (guard : d4148 p = 1) : d1461 p ≤ (0 : Int) + d1328 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1461, d1328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10770 p hg
    simpa only [d1461, d1328, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1461, d1328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10740 p hg
    simpa only [d1461, d1328, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10772 (p : Pattern) (guard : d4148 p = 1) : d1462 p ≤ (0 : Int) + d1329 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1462, d1329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10767 p hg
    simpa only [d1462, d1329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1462, d1329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10771 p hg
    simpa only [d1462, d1329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10773 (p : Pattern) (guard : d4148 p = 1) : d1451 p ≤ (0 : Int) + d1330 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1451, d1330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3810 p hg
    simpa only [d1451, d1330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1451, d1330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10743 p hg
    simpa only [d1451, d1330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10774 (p : Pattern) (guard : d4148 p = 1) : d1452 p ≤ (0 : Int) + d1331 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1452, d1331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10773 p hg
    simpa only [d1452, d1331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1452, d1331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10746 p hg
    simpa only [d1452, d1331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10775 (p : Pattern) (guard : d4148 p = 1) : d1453 p ≤ (0 : Int) + d1332 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1453, d1332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8231 p hg
    simpa only [d1453, d1332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1453, d1332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9970 p hg
    simpa only [d1453, d1332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10776 (p : Pattern) (guard : d4148 p = 1) : d1454 p ≤ (0 : Int) + d1333 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1454, d1333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10775 p hg
    simpa only [d1454, d1333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1454, d1333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10749 p hg
    simpa only [d1454, d1333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10777 (p : Pattern) (guard : d4148 p = 1) : d1455 p ≤ (0 : Int) + d1334 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1455, d1334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10776 p hg
    simpa only [d1455, d1334, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1455, d1334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10751 p hg
    simpa only [d1455, d1334, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10778 (p : Pattern) (guard : d4148 p = 1) : d1456 p ≤ (0 : Int) + d1335 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1456, d1335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10774 p hg
    simpa only [d1456, d1335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1456, d1335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10777 p hg
    simpa only [d1456, d1335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10779 (p : Pattern) (guard : d4148 p = 1) : d1463 p ≤ (0 : Int) + d1336 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1463, d1336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10772 p hg
    simpa only [d1463, d1336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1463, d1336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10778 p hg
    simpa only [d1463, d1336, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
