/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons069
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare9800 (p : Pattern) (guard : d4148 p = 1) : d1155 p ≤ (0 : Int) + d1399 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1155, d1399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9799 p hg
    simpa only [d1155, d1399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1155, d1399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3620 p hg
    simpa only [d1155, d1399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9801 (p : Pattern) (guard : d4148 p = 1) : d1156 p ≤ (0 : Int) + d1400 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1156, d1400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9322 p hg
    simpa only [d1156, d1400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1156, d1400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9800 p hg
    simpa only [d1156, d1400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9802 (p : Pattern) (guard : d0 p = 1) : d360 p ≤ (0 : Int) + d33 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9803 (p : Pattern) (guard : d4148 p = 1) : d1157 p ≤ (0 : Int) + d33 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3623 p hg
    simpa only [d4148, d1157, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9802 p hg
    simpa only [d4148, d1157, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9804 (p : Pattern) (guard : d4148 p = 1) : d1159 p ≤ (0 : Int) + d1401 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1159, d1401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9803 p hg
    simpa only [d1159, d1401, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1159, d1401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9330 p hg
    simpa only [d1159, d1401, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9805 (p : Pattern) (guard : d4148 p = 1) : d1162 p ≤ (0 : Int) + d1402 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1162, d1402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9804 p hg
    simpa only [d1162, d1402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1162, d1402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9333 p hg
    simpa only [d1162, d1402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9806 (p : Pattern) (guard : d4148 p = 1) : d1163 p ≤ (0 : Int) + d1403 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1163, d1403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9801 p hg
    simpa only [d1163, d1403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1163, d1403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9805 p hg
    simpa only [d1163, d1403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9807 (p : Pattern) (guard : d0 p = 1) : d352 p ≤ (0 : Int) + d53 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9808 (p : Pattern) (guard : d4148 p = 1) : d1164 p ≤ (0 : Int) + d54 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1164, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare822 p hg
    simpa only [d4148, d1164, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1164, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9807 p hg
    simpa only [d4148, d1164, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9809 (p : Pattern) (guard : d4148 p = 1) : d1165 p ≤ (0 : Int) + d1165 p := by
  omega
theorem compare9810 (p : Pattern) (guard : d4148 p = 1) : d1166 p ≤ (0 : Int) + d1404 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1166, d1404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9808 p hg
    simpa only [d1166, d1404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1166, d1404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9809 p hg
    simpa only [d1166, d1404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9811 (p : Pattern) (guard : d0 p = 1) : d370 p ≤ (0 : Int) + d795 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9812 (p : Pattern) (guard : d4148 p = 1) : d1167 p ≤ (0 : Int) + d796 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1167, d796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare845 p hg
    simpa only [d4148, d1167, d796, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1167, d796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9811 p hg
    simpa only [d4148, d1167, d796, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9813 (p : Pattern) (guard : d4148 p = 1) : d1168 p ≤ (0 : Int) + d1405 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1168, d1405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9812 p hg
    simpa only [d1168, d1405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1168, d1405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3647 p hg
    simpa only [d1168, d1405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9814 (p : Pattern) (guard : d4148 p = 1) : d1169 p ≤ (0 : Int) + d1406 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1169, d1406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9810 p hg
    simpa only [d1169, d1406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1169, d1406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9813 p hg
    simpa only [d1169, d1406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9815 (p : Pattern) (guard : d0 p = 1) : d373 p ≤ (0 : Int) + d795 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9816 (p : Pattern) (guard : d4148 p = 1) : d1170 p ≤ (0 : Int) + d796 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1170, d796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare845 p hg
    simpa only [d4148, d1170, d796, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1170, d796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9815 p hg
    simpa only [d4148, d1170, d796, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9817 (p : Pattern) (guard : d4148 p = 1) : d1171 p ≤ (0 : Int) + d1171 p := by
  omega
theorem compare9818 (p : Pattern) (guard : d4148 p = 1) : d1172 p ≤ (0 : Int) + d1407 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1172, d1407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9816 p hg
    simpa only [d1172, d1407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1172, d1407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9817 p hg
    simpa only [d1172, d1407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9819 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d173 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9820 (p : Pattern) (guard : d4148 p = 1) : d1171 p ≤ (0 : Int) + d176 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1171, d176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8066 p hg
    simpa only [d4148, d1171, d176, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1171, d176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9819 p hg
    simpa only [d4148, d1171, d176, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9821 (p : Pattern) (guard : d4148 p = 1) : d73 p ≤ (0 : Int) + d73 p := by
  omega
theorem compare9822 (p : Pattern) (guard : d4148 p = 1) : d1173 p ≤ (0 : Int) + d177 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1173, d177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9820 p hg
    simpa only [d1173, d177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1173, d177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9821 p hg
    simpa only [d1173, d177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9823 (p : Pattern) (guard : d4148 p = 1) : d1174 p ≤ (0 : Int) + d1408 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1174, d1408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9818 p hg
    simpa only [d1174, d1408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1174, d1408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9822 p hg
    simpa only [d1174, d1408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9824 (p : Pattern) (guard : d4148 p = 1) : d1175 p ≤ (0 : Int) + d1409 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1175, d1409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9814 p hg
    simpa only [d1175, d1409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1175, d1409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9823 p hg
    simpa only [d1175, d1409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9825 (p : Pattern) (guard : d4148 p = 1) : d1176 p ≤ (0 : Int) + d1410 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1176, d1410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9806 p hg
    simpa only [d1176, d1410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1176, d1410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9824 p hg
    simpa only [d1176, d1410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9826 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d53 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9827 (p : Pattern) (guard : d4148 p = 1) : d1177 p ≤ (0 : Int) + d54 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1177, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare822 p hg
    simpa only [d4148, d1177, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1177, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9826 p hg
    simpa only [d4148, d1177, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9828 (p : Pattern) (guard : d4148 p = 1) : d1179 p ≤ (0 : Int) + d1411 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1179, d1411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9827 p hg
    simpa only [d1179, d1411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1179, d1411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3620 p hg
    simpa only [d1179, d1411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9829 (p : Pattern) (guard : d4148 p = 1) : d1180 p ≤ (0 : Int) + d1412 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1180, d1412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9342 p hg
    simpa only [d1180, d1412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1180, d1412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9828 p hg
    simpa only [d1180, d1412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9830 (p : Pattern) (guard : d4148 p = 1) : d1181 p ≤ (0 : Int) + d53 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare845 p hg
    simpa only [d4148, d1181, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9826 p hg
    simpa only [d4148, d1181, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9831 (p : Pattern) (guard : d4148 p = 1) : d1182 p ≤ (0 : Int) + d1413 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1182, d1413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9830 p hg
    simpa only [d1182, d1413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1182, d1413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3647 p hg
    simpa only [d1182, d1413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9832 (p : Pattern) (guard : d4148 p = 1) : d1183 p ≤ (0 : Int) + d1414 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1183, d1414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9831 p hg
    simpa only [d1183, d1414, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1183, d1414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2348 p hg
    simpa only [d1183, d1414, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9833 (p : Pattern) (guard : d4148 p = 1) : d1184 p ≤ (0 : Int) + d1415 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1184, d1415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9829 p hg
    simpa only [d1184, d1415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1184, d1415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9832 p hg
    simpa only [d1184, d1415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9834 (p : Pattern) (guard : d0 p = 1) : d370 p ≤ (0 : Int) + d53 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9835 (p : Pattern) (guard : d4148 p = 1) : d1185 p ≤ (0 : Int) + d54 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1185, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare822 p hg
    simpa only [d4148, d1185, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1185, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9834 p hg
    simpa only [d4148, d1185, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9836 (p : Pattern) (guard : d4148 p = 1) : d1181 p ≤ (0 : Int) + d1181 p := by
  omega
theorem compare9837 (p : Pattern) (guard : d4148 p = 1) : d1186 p ≤ (0 : Int) + d1416 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1186, d1416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9835 p hg
    simpa only [d1186, d1416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1186, d1416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9836 p hg
    simpa only [d1186, d1416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9838 (p : Pattern) (guard : d4148 p = 1) : d1181 p ≤ (0 : Int) + d808 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1181, d808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare845 p hg
    simpa only [d4148, d1181, d808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1181, d808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9340 p hg
    simpa only [d4148, d1181, d808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9839 (p : Pattern) (guard : d4148 p = 1) : d1182 p ≤ (0 : Int) + d1417 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1182, d1417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9838 p hg
    simpa only [d1182, d1417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1182, d1417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3647 p hg
    simpa only [d1182, d1417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9840 (p : Pattern) (guard : d4148 p = 1) : d1187 p ≤ (0 : Int) + d1418 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1187, d1418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9837 p hg
    simpa only [d1187, d1418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1187, d1418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9839 p hg
    simpa only [d1187, d1418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9841 (p : Pattern) (guard : d4148 p = 1) : d1188 p ≤ (0 : Int) + d972 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1188, d972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9838 p hg
    simpa only [d1188, d972, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1188, d972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2348 p hg
    simpa only [d1188, d972, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9842 (p : Pattern) (guard : d4148 p = 1) : d1189 p ≤ (0 : Int) + d974 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1189, d974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9841 p hg
    simpa only [d1189, d974, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1189, d974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2348 p hg
    simpa only [d1189, d974, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9843 (p : Pattern) (guard : d4148 p = 1) : d1190 p ≤ (0 : Int) + d1419 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1190, d1419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9840 p hg
    simpa only [d1190, d1419, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1190, d1419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9842 p hg
    simpa only [d1190, d1419, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9844 (p : Pattern) (guard : d4148 p = 1) : d1191 p ≤ (0 : Int) + d1420 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1191, d1420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9833 p hg
    simpa only [d1191, d1420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1191, d1420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9843 p hg
    simpa only [d1191, d1420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9845 (p : Pattern) (guard : d4148 p = 1) : d1192 p ≤ (0 : Int) + d1421 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1192, d1421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9825 p hg
    simpa only [d1192, d1421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1192, d1421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9844 p hg
    simpa only [d1192, d1421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9846 (p : Pattern) (guard : d4148 p = 1) : d1195 p ≤ (0 : Int) + d1412 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1195, d1412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9356 p hg
    simpa only [d1195, d1412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1195, d1412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9828 p hg
    simpa only [d1195, d1412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9847 (p : Pattern) (guard : d4148 p = 1) : d1196 p ≤ (0 : Int) + d1415 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1196, d1415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9846 p hg
    simpa only [d1196, d1415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1196, d1415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9832 p hg
    simpa only [d1196, d1415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9848 (p : Pattern) (guard : d0 p = 1) : d360 p ≤ (0 : Int) + d53 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9849 (p : Pattern) (guard : d4148 p = 1) : d1197 p ≤ (0 : Int) + d54 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1197, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare822 p hg
    simpa only [d4148, d1197, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1197, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9848 p hg
    simpa only [d4148, d1197, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9850 (p : Pattern) (guard : d4148 p = 1) : d1198 p ≤ (0 : Int) + d1416 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1198, d1416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9849 p hg
    simpa only [d1198, d1416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1198, d1416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9836 p hg
    simpa only [d1198, d1416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9851 (p : Pattern) (guard : d4148 p = 1) : d1199 p ≤ (0 : Int) + d1418 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1199, d1418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9850 p hg
    simpa only [d1199, d1418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1199, d1418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9839 p hg
    simpa only [d1199, d1418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9852 (p : Pattern) (guard : d4148 p = 1) : d1200 p ≤ (0 : Int) + d1419 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1200, d1419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9851 p hg
    simpa only [d1200, d1419, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1200, d1419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9842 p hg
    simpa only [d1200, d1419, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9853 (p : Pattern) (guard : d4148 p = 1) : d1201 p ≤ (0 : Int) + d1420 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1201, d1420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9847 p hg
    simpa only [d1201, d1420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1201, d1420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9852 p hg
    simpa only [d1201, d1420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9854 (p : Pattern) (guard : d4148 p = 1) : d95 p ≤ (0 : Int) + d95 p := by
  omega
theorem compare9855 (p : Pattern) (guard : d4148 p = 1) : d1205 p ≤ (0 : Int) + d96 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1205, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9364 p hg
    simpa only [d1205, d96, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1205, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9854 p hg
    simpa only [d1205, d96, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9856 (p : Pattern) (guard : d4148 p = 1) : d1206 p ≤ (0 : Int) + d1422 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1206, d1422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9853 p hg
    simpa only [d1206, d1422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1206, d1422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9855 p hg
    simpa only [d1206, d1422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9857 (p : Pattern) (guard : d4148 p = 1) : d1207 p ≤ (0 : Int) + d1423 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1207, d1423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9845 p hg
    simpa only [d1207, d1423, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1207, d1423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9856 p hg
    simpa only [d1207, d1423, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9858 (p : Pattern) (guard : d0 p = 1) : d373 p ≤ (0 : Int) + d33 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9859 (p : Pattern) (guard : d4148 p = 1) : d1193 p ≤ (0 : Int) + d950 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1193, d950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare822 p hg
    simpa only [d4148, d1193, d950, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1193, d950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9858 p hg
    simpa only [d4148, d1193, d950, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9860 (p : Pattern) (guard : d4148 p = 1) : d1210 p ≤ (0 : Int) + d1399 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1210, d1399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9859 p hg
    simpa only [d1210, d1399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1210, d1399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3620 p hg
    simpa only [d1210, d1399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9861 (p : Pattern) (guard : d4148 p = 1) : d1211 p ≤ (0 : Int) + d1400 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1211, d1400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9372 p hg
    simpa only [d1211, d1400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1211, d1400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9860 p hg
    simpa only [d1211, d1400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9862 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d33 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9863 (p : Pattern) (guard : d4148 p = 1) : d1212 p ≤ (0 : Int) + d33 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3623 p hg
    simpa only [d4148, d1212, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9862 p hg
    simpa only [d4148, d1212, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9864 (p : Pattern) (guard : d4148 p = 1) : d1213 p ≤ (0 : Int) + d1401 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1213, d1401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9863 p hg
    simpa only [d1213, d1401, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1213, d1401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9330 p hg
    simpa only [d1213, d1401, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9865 (p : Pattern) (guard : d4148 p = 1) : d1214 p ≤ (0 : Int) + d1402 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1214, d1402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9864 p hg
    simpa only [d1214, d1402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1214, d1402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9333 p hg
    simpa only [d1214, d1402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9866 (p : Pattern) (guard : d4148 p = 1) : d1215 p ≤ (0 : Int) + d1403 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1215, d1403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9861 p hg
    simpa only [d1215, d1403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1215, d1403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9865 p hg
    simpa only [d1215, d1403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9867 (p : Pattern) (guard : d0 p = 1) : d354 p ≤ (0 : Int) + d53 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9868 (p : Pattern) (guard : d4148 p = 1) : d1154 p ≤ (0 : Int) + d54 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1154, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare822 p hg
    simpa only [d4148, d1154, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1154, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9867 p hg
    simpa only [d4148, d1154, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9869 (p : Pattern) (guard : d4148 p = 1) : d1216 p ≤ (0 : Int) + d1416 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1216, d1416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9868 p hg
    simpa only [d1216, d1416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1216, d1416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9836 p hg
    simpa only [d1216, d1416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9870 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d795 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9871 (p : Pattern) (guard : d4148 p = 1) : d1181 p ≤ (0 : Int) + d796 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1181, d796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare845 p hg
    simpa only [d4148, d1181, d796, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1181, d796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9870 p hg
    simpa only [d4148, d1181, d796, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9872 (p : Pattern) (guard : d4148 p = 1) : d1182 p ≤ (0 : Int) + d1405 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1182, d1405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9871 p hg
    simpa only [d1182, d1405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1182, d1405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3647 p hg
    simpa only [d1182, d1405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9873 (p : Pattern) (guard : d4148 p = 1) : d1217 p ≤ (0 : Int) + d1424 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1217, d1424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9869 p hg
    simpa only [d1217, d1424, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1217, d1424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9872 p hg
    simpa only [d1217, d1424, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9874 (p : Pattern) (guard : d4148 p = 1) : d1218 p ≤ (0 : Int) + d1407 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1218, d1407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9871 p hg
    simpa only [d1218, d1407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1218, d1407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9817 p hg
    simpa only [d1218, d1407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9875 (p : Pattern) (guard : d4148 p = 1) : d1219 p ≤ (0 : Int) + d1408 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1219, d1408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9874 p hg
    simpa only [d1219, d1408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1219, d1408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9822 p hg
    simpa only [d1219, d1408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9876 (p : Pattern) (guard : d4148 p = 1) : d1220 p ≤ (0 : Int) + d1425 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1220, d1425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9873 p hg
    simpa only [d1220, d1425, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1220, d1425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9875 p hg
    simpa only [d1220, d1425, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9877 (p : Pattern) (guard : d4148 p = 1) : d1221 p ≤ (0 : Int) + d1426 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1221, d1426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9866 p hg
    simpa only [d1221, d1426, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1221, d1426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9876 p hg
    simpa only [d1221, d1426, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9878 (p : Pattern) (guard : d4148 p = 1) : d1223 p ≤ (0 : Int) + d1412 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1223, d1412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9384 p hg
    simpa only [d1223, d1412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1223, d1412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9828 p hg
    simpa only [d1223, d1412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9879 (p : Pattern) (guard : d4148 p = 1) : d1224 p ≤ (0 : Int) + d1415 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1224, d1415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9878 p hg
    simpa only [d1224, d1415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1224, d1415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9832 p hg
    simpa only [d1224, d1415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9880 (p : Pattern) (guard : d4148 p = 1) : d1225 p ≤ (0 : Int) + d1416 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1225, d1416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9827 p hg
    simpa only [d1225, d1416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1225, d1416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9836 p hg
    simpa only [d1225, d1416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9881 (p : Pattern) (guard : d4148 p = 1) : d1226 p ≤ (0 : Int) + d1418 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1226, d1418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9880 p hg
    simpa only [d1226, d1418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1226, d1418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9839 p hg
    simpa only [d1226, d1418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9882 (p : Pattern) (guard : d4148 p = 1) : d1227 p ≤ (0 : Int) + d1419 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1227, d1419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9881 p hg
    simpa only [d1227, d1419, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1227, d1419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9842 p hg
    simpa only [d1227, d1419, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9883 (p : Pattern) (guard : d4148 p = 1) : d1228 p ≤ (0 : Int) + d1420 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1228, d1420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9879 p hg
    simpa only [d1228, d1420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1228, d1420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9882 p hg
    simpa only [d1228, d1420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9884 (p : Pattern) (guard : d4148 p = 1) : d1229 p ≤ (0 : Int) + d1427 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1229, d1427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9877 p hg
    simpa only [d1229, d1427, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1229, d1427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9883 p hg
    simpa only [d1229, d1427, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9885 (p : Pattern) (guard : d4148 p = 1) : d1231 p ≤ (0 : Int) + d1412 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1231, d1412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9392 p hg
    simpa only [d1231, d1412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1231, d1412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9828 p hg
    simpa only [d1231, d1412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9886 (p : Pattern) (guard : d4148 p = 1) : d1232 p ≤ (0 : Int) + d1415 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1232, d1415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9885 p hg
    simpa only [d1232, d1415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1232, d1415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9832 p hg
    simpa only [d1232, d1415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9887 (p : Pattern) (guard : d4148 p = 1) : d1233 p ≤ (0 : Int) + d1420 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1233, d1420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9886 p hg
    simpa only [d1233, d1420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1233, d1420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9882 p hg
    simpa only [d1233, d1420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9888 (p : Pattern) (guard : d4148 p = 1) : d1234 p ≤ (0 : Int) + d1428 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1234, d1428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9887 p hg
    simpa only [d1234, d1428, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1234, d1428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2348 p hg
    simpa only [d1234, d1428, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9889 (p : Pattern) (guard : d4148 p = 1) : d1235 p ≤ (0 : Int) + d1429 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1235, d1429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9884 p hg
    simpa only [d1235, d1429, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1235, d1429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9888 p hg
    simpa only [d1235, d1429, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9890 (p : Pattern) (guard : d4148 p = 1) : d1236 p ≤ (0 : Int) + d1430 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1236, d1430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9857 p hg
    simpa only [d1236, d1430, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1236, d1430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9889 p hg
    simpa only [d1236, d1430, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9891 (p : Pattern) (guard : d4148 p = 1) : d1197 p ≤ (0 : Int) + d950 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1197, d950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare822 p hg
    simpa only [d4148, d1197, d950, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1197, d950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9802 p hg
    simpa only [d4148, d1197, d950, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9892 (p : Pattern) (guard : d4148 p = 1) : d1239 p ≤ (0 : Int) + d1399 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1239, d1399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9891 p hg
    simpa only [d1239, d1399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1239, d1399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3620 p hg
    simpa only [d1239, d1399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9893 (p : Pattern) (guard : d4148 p = 1) : d1240 p ≤ (0 : Int) + d1400 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1240, d1400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9402 p hg
    simpa only [d1240, d1400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1240, d1400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9892 p hg
    simpa only [d1240, d1400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9894 (p : Pattern) (guard : d0 p = 1) : d370 p ≤ (0 : Int) + d33 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9895 (p : Pattern) (guard : d4148 p = 1) : d1241 p ≤ (0 : Int) + d33 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3623 p hg
    simpa only [d4148, d1241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9894 p hg
    simpa only [d4148, d1241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9896 (p : Pattern) (guard : d4148 p = 1) : d1242 p ≤ (0 : Int) + d1401 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1242, d1401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9895 p hg
    simpa only [d1242, d1401, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1242, d1401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9330 p hg
    simpa only [d1242, d1401, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9897 (p : Pattern) (guard : d4148 p = 1) : d1243 p ≤ (0 : Int) + d1402 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1243, d1402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9896 p hg
    simpa only [d1243, d1402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1243, d1402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9333 p hg
    simpa only [d1243, d1402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9898 (p : Pattern) (guard : d4148 p = 1) : d1244 p ≤ (0 : Int) + d1403 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1244, d1403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9893 p hg
    simpa only [d1244, d1403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1244, d1403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9897 p hg
    simpa only [d1244, d1403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9899 (p : Pattern) (guard : d0 p = 1) : d368 p ≤ (0 : Int) + d53 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9900 (p : Pattern) (guard : d4148 p = 1) : d1208 p ≤ (0 : Int) + d54 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1208, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare822 p hg
    simpa only [d4148, d1208, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1208, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9899 p hg
    simpa only [d4148, d1208, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9901 (p : Pattern) (guard : d4148 p = 1) : d1167 p ≤ (0 : Int) + d1167 p := by
  omega
theorem compare9902 (p : Pattern) (guard : d4148 p = 1) : d1245 p ≤ (0 : Int) + d1431 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1245, d1431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9900 p hg
    simpa only [d1245, d1431, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1245, d1431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9901 p hg
    simpa only [d1245, d1431, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9903 (p : Pattern) (guard : d4148 p = 1) : d1246 p ≤ (0 : Int) + d1405 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1246, d1405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9816 p hg
    simpa only [d1246, d1405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1246, d1405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3647 p hg
    simpa only [d1246, d1405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9904 (p : Pattern) (guard : d4148 p = 1) : d1247 p ≤ (0 : Int) + d1432 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1247, d1432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9902 p hg
    simpa only [d1247, d1432, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1247, d1432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9903 p hg
    simpa only [d1247, d1432, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9905 (p : Pattern) (guard : d4148 p = 1) : d1248 p ≤ (0 : Int) + d1433 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1248, d1433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9904 p hg
    simpa only [d1248, d1433, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1248, d1433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9875 p hg
    simpa only [d1248, d1433, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9906 (p : Pattern) (guard : d4148 p = 1) : d1249 p ≤ (0 : Int) + d1434 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1249, d1434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9898 p hg
    simpa only [d1249, d1434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1249, d1434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9905 p hg
    simpa only [d1249, d1434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9907 (p : Pattern) (guard : d4148 p = 1) : d1251 p ≤ (0 : Int) + d1412 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1251, d1412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9416 p hg
    simpa only [d1251, d1412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1251, d1412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9828 p hg
    simpa only [d1251, d1412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9908 (p : Pattern) (guard : d4148 p = 1) : d1252 p ≤ (0 : Int) + d1415 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1252, d1415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9907 p hg
    simpa only [d1252, d1415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1252, d1415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9832 p hg
    simpa only [d1252, d1415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9909 (p : Pattern) (guard : d0 p = 1) : d373 p ≤ (0 : Int) + d53 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9910 (p : Pattern) (guard : d4148 p = 1) : d1193 p ≤ (0 : Int) + d54 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1193, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare822 p hg
    simpa only [d4148, d1193, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1193, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9909 p hg
    simpa only [d4148, d1193, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9911 (p : Pattern) (guard : d4148 p = 1) : d1253 p ≤ (0 : Int) + d1416 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1253, d1416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9910 p hg
    simpa only [d1253, d1416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1253, d1416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9836 p hg
    simpa only [d1253, d1416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9912 (p : Pattern) (guard : d4148 p = 1) : d1254 p ≤ (0 : Int) + d1418 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1254, d1418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9911 p hg
    simpa only [d1254, d1418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1254, d1418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9839 p hg
    simpa only [d1254, d1418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9913 (p : Pattern) (guard : d4148 p = 1) : d1255 p ≤ (0 : Int) + d1419 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1255, d1419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9912 p hg
    simpa only [d1255, d1419, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1255, d1419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9842 p hg
    simpa only [d1255, d1419, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9914 (p : Pattern) (guard : d4148 p = 1) : d1256 p ≤ (0 : Int) + d1420 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1256, d1420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9908 p hg
    simpa only [d1256, d1420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1256, d1420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9913 p hg
    simpa only [d1256, d1420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9915 (p : Pattern) (guard : d4148 p = 1) : d1257 p ≤ (0 : Int) + d1435 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1257, d1435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9906 p hg
    simpa only [d1257, d1435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1257, d1435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9914 p hg
    simpa only [d1257, d1435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9916 (p : Pattern) (guard : d4148 p = 1) : d1258 p ≤ (0 : Int) + d1422 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1258, d1422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9844 p hg
    simpa only [d1258, d1422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1258, d1422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9855 p hg
    simpa only [d1258, d1422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9917 (p : Pattern) (guard : d4148 p = 1) : d1259 p ≤ (0 : Int) + d1436 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1259, d1436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9915 p hg
    simpa only [d1259, d1436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1259, d1436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9916 p hg
    simpa only [d1259, d1436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9918 (p : Pattern) (guard : d4148 p = 1) : d1177 p ≤ (0 : Int) + d950 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1177, d950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare822 p hg
    simpa only [d4148, d1177, d950, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1177, d950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9862 p hg
    simpa only [d4148, d1177, d950, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9919 (p : Pattern) (guard : d4148 p = 1) : d1179 p ≤ (0 : Int) + d1399 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1179, d1399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9918 p hg
    simpa only [d1179, d1399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1179, d1399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3620 p hg
    simpa only [d1179, d1399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9920 (p : Pattern) (guard : d4148 p = 1) : d1195 p ≤ (0 : Int) + d1400 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1195, d1400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9356 p hg
    simpa only [d1195, d1400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1195, d1400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9919 p hg
    simpa only [d1195, d1400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9921 (p : Pattern) (guard : d4148 p = 1) : d1260 p ≤ (0 : Int) + d1403 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1260, d1403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9920 p hg
    simpa only [d1260, d1403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1260, d1403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9865 p hg
    simpa only [d1260, d1403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9922 (p : Pattern) (guard : d4148 p = 1) : d1199 p ≤ (0 : Int) + d1424 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1199, d1424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9850 p hg
    simpa only [d1199, d1424, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1199, d1424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9872 p hg
    simpa only [d1199, d1424, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9923 (p : Pattern) (guard : d4148 p = 1) : d1261 p ≤ (0 : Int) + d1425 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1261, d1425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9922 p hg
    simpa only [d1261, d1425, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1261, d1425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9875 p hg
    simpa only [d1261, d1425, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9924 (p : Pattern) (guard : d4148 p = 1) : d1262 p ≤ (0 : Int) + d1426 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1262, d1426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9921 p hg
    simpa only [d1262, d1426, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1262, d1426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9923 p hg
    simpa only [d1262, d1426, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9925 (p : Pattern) (guard : d4148 p = 1) : d1263 p ≤ (0 : Int) + d1412 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1263, d1412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9430 p hg
    simpa only [d1263, d1412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1263, d1412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9828 p hg
    simpa only [d1263, d1412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9926 (p : Pattern) (guard : d4148 p = 1) : d1264 p ≤ (0 : Int) + d1415 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1264, d1415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9925 p hg
    simpa only [d1264, d1415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1264, d1415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9832 p hg
    simpa only [d1264, d1415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9927 (p : Pattern) (guard : d4148 p = 1) : d1265 p ≤ (0 : Int) + d1420 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1265, d1420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9926 p hg
    simpa only [d1265, d1420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1265, d1420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9882 p hg
    simpa only [d1265, d1420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9928 (p : Pattern) (guard : d4148 p = 1) : d1266 p ≤ (0 : Int) + d1427 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1266, d1427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9924 p hg
    simpa only [d1266, d1427, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1266, d1427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9927 p hg
    simpa only [d1266, d1427, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9929 (p : Pattern) (guard : d4148 p = 1) : d1267 p ≤ (0 : Int) + d1428 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1267, d1428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9883 p hg
    simpa only [d1267, d1428, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1267, d1428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2348 p hg
    simpa only [d1267, d1428, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9930 (p : Pattern) (guard : d4148 p = 1) : d1268 p ≤ (0 : Int) + d1429 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1268, d1429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9928 p hg
    simpa only [d1268, d1429, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1268, d1429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9929 p hg
    simpa only [d1268, d1429, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9931 (p : Pattern) (guard : d4148 p = 1) : d1269 p ≤ (0 : Int) + d1437 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1269, d1437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9917 p hg
    simpa only [d1269, d1437, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1269, d1437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9930 p hg
    simpa only [d1269, d1437, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9932 (p : Pattern) (guard : d4148 p = 1) : d1270 p ≤ (0 : Int) + d1438 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1270, d1438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9890 p hg
    simpa only [d1270, d1438, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1270, d1438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9931 p hg
    simpa only [d1270, d1438, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9933 (p : Pattern) (guard : d0 p = 1) : d360 p ≤ (0 : Int) + d118 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9934 (p : Pattern) (guard : d4148 p = 1) : d1274 p ≤ (0 : Int) + d1043 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1274, d1043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1246 p hg
    simpa only [d4148, d1274, d1043, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1274, d1043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9933 p hg
    simpa only [d4148, d1274, d1043, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9935 (p : Pattern) (guard : d4148 p = 1) : d1275 p ≤ (0 : Int) + d1439 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1275, d1439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9934 p hg
    simpa only [d1275, d1439, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1275, d1439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3754 p hg
    simpa only [d1275, d1439, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9936 (p : Pattern) (guard : d4148 p = 1) : d1276 p ≤ (0 : Int) + d1440 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1276, d1440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9444 p hg
    simpa only [d1276, d1440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1276, d1440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9935 p hg
    simpa only [d1276, d1440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9937 (p : Pattern) (guard : d0 p = 1) : d370 p ≤ (0 : Int) + d118 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9938 (p : Pattern) (guard : d4148 p = 1) : d1277 p ≤ (0 : Int) + d118 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3757 p hg
    simpa only [d4148, d1277, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9937 p hg
    simpa only [d4148, d1277, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9939 (p : Pattern) (guard : d4148 p = 1) : d1279 p ≤ (0 : Int) + d1441 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1279, d1441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9938 p hg
    simpa only [d1279, d1441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1279, d1441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9451 p hg
    simpa only [d1279, d1441, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
