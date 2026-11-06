/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons056
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare7980 (p : Pattern) (guard : d4395 p = 1) : d1095 p ≤ (0 : Int) + d1465 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1095, d1465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7978 p hg
    simpa only [d1095, d1465, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1095, d1465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7979 p hg
    simpa only [d1095, d1465, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7981 (p : Pattern) (guard : d4395 p = 1) : d1096 p ≤ (0 : Int) + d1466 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1096, d1466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7959 p hg
    simpa only [d1096, d1466, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1096, d1466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7980 p hg
    simpa only [d1096, d1466, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7982 (p : Pattern) (guard : d4395 p = 1) : d1097 p ≤ (0 : Int) + d1467 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1097, d1467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7877 p hg
    simpa only [d1097, d1467, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1097, d1467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7981 p hg
    simpa only [d1097, d1467, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7983 (p : Pattern) (guard : d4395 p = 1) : d1098 p ≤ (0 : Int) + d1468 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1098, d1468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7909 p hg
    simpa only [d1098, d1468, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1098, d1468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7982 p hg
    simpa only [d1098, d1468, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7984 (p : Pattern) (guard : d4395 p = 1) : d968 p ≤ (0 : Int) + d1469 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d968, d1469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare845 p hg
    simpa only [d4395, d968, d1469, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d968, d1469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7864 p hg
    simpa only [d4395, d968, d1469, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7985 (p : Pattern) (guard : d4395 p = 1) : d1099 p ≤ (0 : Int) + d1470 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1099, d1470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7984 p hg
    simpa only [d1099, d1470, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1099, d1470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7822 p hg
    simpa only [d1099, d1470, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7986 (p : Pattern) (guard : d4395 p = 1) : d1101 p ≤ (0 : Int) + d1101 p := by
  omega
theorem compare7987 (p : Pattern) (guard : d4395 p = 1) : d1102 p ≤ (0 : Int) + d1471 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1102, d1471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7985 p hg
    simpa only [d1102, d1471, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1102, d1471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7986 p hg
    simpa only [d1102, d1471, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7988 (p : Pattern) (guard : d4395 p = 1) : d1103 p ≤ (0 : Int) + d1472 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1103, d1472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7863 p hg
    simpa only [d1103, d1472, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1103, d1472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7987 p hg
    simpa only [d1103, d1472, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7989 (p : Pattern) (guard : d4395 p = 1) : d1104 p ≤ (0 : Int) + d1473 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1104, d1473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7904 p hg
    simpa only [d1104, d1473, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1104, d1473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7988 p hg
    simpa only [d1104, d1473, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7990 (p : Pattern) (guard : d4395 p = 1) : d1105 p ≤ (0 : Int) + d1474 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1105, d1474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7988 p hg
    simpa only [d1105, d1474, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1105, d1474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7817 p hg
    simpa only [d1105, d1474, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7991 (p : Pattern) (guard : d4395 p = 1) : d1106 p ≤ (0 : Int) + d1475 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1106, d1475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7989 p hg
    simpa only [d1106, d1475, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1106, d1475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7990 p hg
    simpa only [d1106, d1475, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7992 (p : Pattern) (guard : d4395 p = 1) : d1107 p ≤ (0 : Int) + d1476 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1107, d1476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7899 p hg
    simpa only [d1107, d1476, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1107, d1476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7991 p hg
    simpa only [d1107, d1476, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7993 (p : Pattern) (guard : d4395 p = 1) : d1108 p ≤ (0 : Int) + d1477 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1108, d1477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7877 p hg
    simpa only [d1108, d1477, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1108, d1477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7992 p hg
    simpa only [d1108, d1477, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7994 (p : Pattern) (guard : d0 p = 1) : d448 p ≤ (0 : Int) + d1289 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7995 (p : Pattern) (guard : d4395 p = 1) : d1109 p ≤ (0 : Int) + d1453 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d1109, d1453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6529 p hg
    simpa only [d4395, d1109, d1453, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d1109, d1453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7994 p hg
    simpa only [d4395, d1109, d1453, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7996 (p : Pattern) (guard : d4395 p = 1) : d1110 p ≤ (0 : Int) + d1460 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1110, d1460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7995 p hg
    simpa only [d1110, d1460, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1110, d1460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7925 p hg
    simpa only [d1110, d1460, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7997 (p : Pattern) (guard : d4395 p = 1) : d1111 p ≤ (0 : Int) + d1461 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1111, d1461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7996 p hg
    simpa only [d1111, d1461, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1111, d1461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7930 p hg
    simpa only [d1111, d1461, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7998 (p : Pattern) (guard : d4395 p = 1) : d1112 p ≤ (0 : Int) + d1462 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1112, d1462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7922 p hg
    simpa only [d1112, d1462, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1112, d1462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7997 p hg
    simpa only [d1112, d1462, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7999 (p : Pattern) (guard : d4395 p = 1) : d1113 p ≤ (0 : Int) + d1463 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1113, d1463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7998 p hg
    simpa only [d1113, d1463, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1113, d1463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7946 p hg
    simpa only [d1113, d1463, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8000 (p : Pattern) (guard : d4395 p = 1) : d1114 p ≤ (0 : Int) + d1456 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1114, d1456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7951 p hg
    simpa only [d1114, d1456, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1114, d1456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7945 p hg
    simpa only [d1114, d1456, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8001 (p : Pattern) (guard : d4395 p = 1) : d1115 p ≤ (0 : Int) + d1458 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1115, d1458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8000 p hg
    simpa only [d1115, d1458, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1115, d1458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7957 p hg
    simpa only [d1115, d1458, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8002 (p : Pattern) (guard : d4395 p = 1) : d1116 p ≤ (0 : Int) + d1478 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1116, d1478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7999 p hg
    simpa only [d1116, d1478, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1116, d1478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8001 p hg
    simpa only [d1116, d1478, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8003 (p : Pattern) (guard : d0 p = 1) : d450 p ≤ (0 : Int) + d110 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8004 (p : Pattern) (guard : d4395 p = 1) : d1117 p ≤ (0 : Int) + d111 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d1117, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1246 p hg
    simpa only [d4395, d1117, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d1117, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8003 p hg
    simpa only [d4395, d1117, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8005 (p : Pattern) (guard : d1 p = 1) : d291 p ≤ (0 : Int) + d291 p := by
  omega
theorem compare8006 (p : Pattern) (guard : d4395 p = 1) : d1118 p ≤ (0 : Int) + d1479 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d1118, d1479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8005 p hg
    simpa only [d4395, d1118, d1479, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d1118, d1479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7935 p hg
    simpa only [d4395, d1118, d1479, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8007 (p : Pattern) (guard : d4395 p = 1) : d1119 p ≤ (0 : Int) + d1480 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1119, d1480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8004 p hg
    simpa only [d1119, d1480, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1119, d1480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8006 p hg
    simpa only [d1119, d1480, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8008 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d275 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8009 (p : Pattern) (guard : d4395 p = 1) : d1120 p ≤ (0 : Int) + d1481 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d1120, d1481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2440 p hg
    simpa only [d4395, d1120, d1481, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d1120, d1481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8008 p hg
    simpa only [d4395, d1120, d1481, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8010 (p : Pattern) (guard : d1 p = 1) : d275 p ≤ (0 : Int) + d275 p := by
  omega
theorem compare8011 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d278 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8012 (p : Pattern) (guard : d4395 p = 1) : d1121 p ≤ (0 : Int) + d279 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d1121, d279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8010 p hg
    simpa only [d4395, d1121, d279, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d1121, d279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8011 p hg
    simpa only [d4395, d1121, d279, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8013 (p : Pattern) (guard : d4395 p = 1) : d1122 p ≤ (0 : Int) + d1482 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1122, d1482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8009 p hg
    simpa only [d1122, d1482, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1122, d1482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8012 p hg
    simpa only [d1122, d1482, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8014 (p : Pattern) (guard : d4395 p = 1) : d1123 p ≤ (0 : Int) + d1483 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1123, d1483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8007 p hg
    simpa only [d1123, d1483, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1123, d1483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8013 p hg
    simpa only [d1123, d1483, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8015 (p : Pattern) (guard : d4395 p = 1) : d1124 p ≤ (0 : Int) + d1124 p := by
  omega
theorem compare8016 (p : Pattern) (guard : d4395 p = 1) : d1125 p ≤ (0 : Int) + d1484 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1125, d1484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7941 p hg
    simpa only [d1125, d1484, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1125, d1484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8015 p hg
    simpa only [d1125, d1484, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8017 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d1375 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8018 (p : Pattern) (guard : d4395 p = 1) : d1124 p ≤ (0 : Int) + d1485 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d1124, d1485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6637 p hg
    simpa only [d4395, d1124, d1485, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d1124, d1485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8017 p hg
    simpa only [d4395, d1124, d1485, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8019 (p : Pattern) (guard : d4395 p = 1) : d1129 p ≤ (0 : Int) + d1129 p := by
  omega
theorem compare8020 (p : Pattern) (guard : d4395 p = 1) : d1130 p ≤ (0 : Int) + d1486 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1130, d1486, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8018 p hg
    simpa only [d1130, d1486, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1130, d1486, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8019 p hg
    simpa only [d1130, d1486, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8021 (p : Pattern) (guard : d4395 p = 1) : d1131 p ≤ (0 : Int) + d1487 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1131, d1487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8016 p hg
    simpa only [d1131, d1487, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1131, d1487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8020 p hg
    simpa only [d1131, d1487, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8022 (p : Pattern) (guard : d4395 p = 1) : d1132 p ≤ (0 : Int) + d1488 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1132, d1488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8014 p hg
    simpa only [d1132, d1488, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1132, d1488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8021 p hg
    simpa only [d1132, d1488, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8023 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d293 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8024 (p : Pattern) (guard : d4395 p = 1) : d1089 p ≤ (0 : Int) + d1489 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d1089, d1489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1246 p hg
    simpa only [d4395, d1089, d1489, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d1089, d1489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8023 p hg
    simpa only [d4395, d1089, d1489, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8025 (p : Pattern) (guard : d1 p = 1) : d1133 p ≤ (0 : Int) + d1133 p := by
  omega
theorem compare8026 (p : Pattern) (guard : d4395 p = 1) : d1134 p ≤ (0 : Int) + d1490 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d1134, d1490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8025 p hg
    simpa only [d4395, d1134, d1490, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d1134, d1490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8011 p hg
    simpa only [d4395, d1134, d1490, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8027 (p : Pattern) (guard : d4395 p = 1) : d1135 p ≤ (0 : Int) + d1491 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1135, d1491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8024 p hg
    simpa only [d1135, d1491, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1135, d1491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8026 p hg
    simpa only [d1135, d1491, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8028 (p : Pattern) (guard : d4395 p = 1) : d1136 p ≤ (0 : Int) + d1492 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1136, d1492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8027 p hg
    simpa only [d1136, d1492, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1136, d1492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7938 p hg
    simpa only [d1136, d1492, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8029 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d1385 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8030 (p : Pattern) (guard : d4395 p = 1) : d1061 p ≤ (0 : Int) + d1493 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d1061, d1493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1434 p hg
    simpa only [d4395, d1061, d1493, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d1061, d1493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8029 p hg
    simpa only [d4395, d1061, d1493, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8031 (p : Pattern) (guard : d4395 p = 1) : d1138 p ≤ (0 : Int) + d1138 p := by
  omega
theorem compare8032 (p : Pattern) (guard : d4395 p = 1) : d1139 p ≤ (0 : Int) + d1494 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1139, d1494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8030 p hg
    simpa only [d1139, d1494, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1139, d1494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8031 p hg
    simpa only [d1139, d1494, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8033 (p : Pattern) (guard : d4395 p = 1) : d1141 p ≤ (0 : Int) + d1141 p := by
  omega
theorem compare8034 (p : Pattern) (guard : d4395 p = 1) : d1142 p ≤ (0 : Int) + d1495 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1142, d1495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8032 p hg
    simpa only [d1142, d1495, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1142, d1495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8033 p hg
    simpa only [d1142, d1495, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8035 (p : Pattern) (guard : d4395 p = 1) : d1143 p ≤ (0 : Int) + d1496 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1143, d1496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8028 p hg
    simpa only [d1143, d1496, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1143, d1496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8034 p hg
    simpa only [d1143, d1496, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8036 (p : Pattern) (guard : d4395 p = 1) : d1144 p ≤ (0 : Int) + d1497 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1144, d1497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8022 p hg
    simpa only [d1144, d1497, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1144, d1497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8035 p hg
    simpa only [d1144, d1497, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8037 (p : Pattern) (guard : d4395 p = 1) : d1145 p ≤ (0 : Int) + d1498 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1145, d1498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8035 p hg
    simpa only [d1145, d1498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1145, d1498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7817 p hg
    simpa only [d1145, d1498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8038 (p : Pattern) (guard : d4395 p = 1) : d1146 p ≤ (0 : Int) + d1499 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1146, d1499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8036 p hg
    simpa only [d1146, d1499, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1146, d1499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8037 p hg
    simpa only [d1146, d1499, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8039 (p : Pattern) (guard : d4395 p = 1) : d1147 p ≤ (0 : Int) + d1500 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1147, d1500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8002 p hg
    simpa only [d1147, d1500, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1147, d1500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8038 p hg
    simpa only [d1147, d1500, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8040 (p : Pattern) (guard : d4395 p = 1) : d1148 p ≤ (0 : Int) + d1501 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1148, d1501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7877 p hg
    simpa only [d1148, d1501, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1148, d1501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8039 p hg
    simpa only [d1148, d1501, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8041 (p : Pattern) (guard : d4395 p = 1) : d1149 p ≤ (0 : Int) + d1502 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1149, d1502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7993 p hg
    simpa only [d1149, d1502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1149, d1502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8040 p hg
    simpa only [d1149, d1502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8042 (p : Pattern) (guard : d4395 p = 1) : d1150 p ≤ (0 : Int) + d1503 p := by
  cases selected : p 48 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1150, d1503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7983 p hg
    simpa only [d1150, d1503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1150, d1503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8041 p hg
    simpa only [d1150, d1503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8043 (p : Pattern) (guard : d0 p = 1) : d346 p ≤ (0 : Int) + d1152 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8044 (p : Pattern) (guard : d4397 p = 1) : d949 p ≤ (0 : Int) + d1153 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d949, d1153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3614 p hg
    simpa only [d4397, d949, d1153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d949, d1153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8043 p hg
    simpa only [d4397, d949, d1153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8045 (p : Pattern) (guard : d0 p = 1) : d33 p ≤ (0 : Int) + d354 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8046 (p : Pattern) (guard : d4148 p = 1) : d950 p ≤ (0 : Int) + d1154 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d950, d1154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare822 p hg
    simpa only [d4148, d950, d1154, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d950, d1154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8045 p hg
    simpa only [d4148, d950, d1154, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8047 (p : Pattern) (guard : d4397 p = 1) : d951 p ≤ (0 : Int) + d1155 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d951, d1155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8046 p hg
    simpa only [d4397, d951, d1155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d951, d1155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7787 p hg
    simpa only [d4397, d951, d1155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8048 (p : Pattern) (guard : d4397 p = 1) : d952 p ≤ (0 : Int) + d1156 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d952, d1156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8044 p hg
    simpa only [d952, d1156, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d952, d1156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8047 p hg
    simpa only [d952, d1156, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8049 (p : Pattern) (guard : d0 p = 1) : d33 p ≤ (0 : Int) + d360 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8050 (p : Pattern) (guard : d4148 p = 1) : d33 p ≤ (0 : Int) + d1157 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3623 p hg
    simpa only [d4148, d1157, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8049 p hg
    simpa only [d4148, d1157, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8051 (p : Pattern) (guard : d0 p = 1) : d371 p ≤ (0 : Int) + d1158 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8052 (p : Pattern) (guard : d4397 p = 1) : d953 p ≤ (0 : Int) + d1159 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d953, d1159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8050 p hg
    simpa only [d4397, d953, d1159, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d953, d1159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8051 p hg
    simpa only [d4397, d953, d1159, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8053 (p : Pattern) (guard : d4397 p = 1) : d954 p ≤ (0 : Int) + d1161 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d954, d1161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3631 p hg
    simpa only [d4397, d954, d1161, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d954, d1161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7793 p hg
    simpa only [d4397, d954, d1161, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8054 (p : Pattern) (guard : d4397 p = 1) : d955 p ≤ (0 : Int) + d1162 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d955, d1162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8052 p hg
    simpa only [d955, d1162, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d955, d1162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8053 p hg
    simpa only [d955, d1162, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8055 (p : Pattern) (guard : d4397 p = 1) : d956 p ≤ (0 : Int) + d1163 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d956, d1163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8048 p hg
    simpa only [d956, d1163, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d956, d1163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8054 p hg
    simpa only [d956, d1163, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8056 (p : Pattern) (guard : d0 p = 1) : d53 p ≤ (0 : Int) + d352 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8057 (p : Pattern) (guard : d4148 p = 1) : d54 p ≤ (0 : Int) + d1164 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d54, d1164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare822 p hg
    simpa only [d4148, d54, d1164, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d54, d1164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8056 p hg
    simpa only [d4148, d54, d1164, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8058 (p : Pattern) (guard : d4397 p = 1) : d957 p ≤ (0 : Int) + d1166 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d957, d1166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8057 p hg
    simpa only [d4397, d957, d1166, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d957, d1166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7797 p hg
    simpa only [d4397, d957, d1166, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8059 (p : Pattern) (guard : d0 p = 1) : d795 p ≤ (0 : Int) + d370 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8060 (p : Pattern) (guard : d4148 p = 1) : d796 p ≤ (0 : Int) + d1167 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d796, d1167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare845 p hg
    simpa only [d4148, d796, d1167, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d796, d1167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8059 p hg
    simpa only [d4148, d796, d1167, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8061 (p : Pattern) (guard : d4397 p = 1) : d958 p ≤ (0 : Int) + d1168 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d958, d1168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8060 p hg
    simpa only [d4397, d958, d1168, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d958, d1168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7799 p hg
    simpa only [d4397, d958, d1168, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8062 (p : Pattern) (guard : d4397 p = 1) : d959 p ≤ (0 : Int) + d1169 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d959, d1169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8058 p hg
    simpa only [d959, d1169, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d959, d1169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8061 p hg
    simpa only [d959, d1169, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8063 (p : Pattern) (guard : d0 p = 1) : d795 p ≤ (0 : Int) + d373 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8064 (p : Pattern) (guard : d4148 p = 1) : d796 p ≤ (0 : Int) + d1170 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d796, d1170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare845 p hg
    simpa only [d4148, d796, d1170, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d796, d1170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8063 p hg
    simpa only [d4148, d796, d1170, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8065 (p : Pattern) (guard : d4397 p = 1) : d960 p ≤ (0 : Int) + d1172 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d960, d1172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8064 p hg
    simpa only [d4397, d960, d1172, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d960, d1172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7802 p hg
    simpa only [d4397, d960, d1172, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8066 (p : Pattern) (guard : d1 p = 1) : d66 p ≤ (0 : Int) + d66 p := by
  omega
theorem compare8067 (p : Pattern) (guard : d0 p = 1) : d173 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8068 (p : Pattern) (guard : d4148 p = 1) : d176 p ≤ (0 : Int) + d1171 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d176, d1171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8066 p hg
    simpa only [d4148, d176, d1171, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d176, d1171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8067 p hg
    simpa only [d4148, d176, d1171, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8069 (p : Pattern) (guard : d4397 p = 1) : d961 p ≤ (0 : Int) + d1173 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d961, d1173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8068 p hg
    simpa only [d4397, d961, d1173, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d961, d1173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7805 p hg
    simpa only [d4397, d961, d1173, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8070 (p : Pattern) (guard : d4397 p = 1) : d962 p ≤ (0 : Int) + d1174 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d962, d1174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8065 p hg
    simpa only [d962, d1174, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d962, d1174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8069 p hg
    simpa only [d962, d1174, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8071 (p : Pattern) (guard : d4397 p = 1) : d963 p ≤ (0 : Int) + d1175 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d963, d1175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8062 p hg
    simpa only [d963, d1175, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d963, d1175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8070 p hg
    simpa only [d963, d1175, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8072 (p : Pattern) (guard : d4397 p = 1) : d964 p ≤ (0 : Int) + d1176 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d964, d1176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8055 p hg
    simpa only [d964, d1176, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d964, d1176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8071 p hg
    simpa only [d964, d1176, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8073 (p : Pattern) (guard : d0 p = 1) : d361 p ≤ (0 : Int) + d1177 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8074 (p : Pattern) (guard : d4397 p = 1) : d965 p ≤ (0 : Int) + d1178 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d965, d1178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3639 p hg
    simpa only [d4397, d965, d1178, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d965, d1178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8073 p hg
    simpa only [d4397, d965, d1178, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8075 (p : Pattern) (guard : d0 p = 1) : d53 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8076 (p : Pattern) (guard : d4148 p = 1) : d54 p ≤ (0 : Int) + d1177 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d54, d1177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare822 p hg
    simpa only [d4148, d54, d1177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d54, d1177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8075 p hg
    simpa only [d4148, d54, d1177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8077 (p : Pattern) (guard : d4397 p = 1) : d966 p ≤ (0 : Int) + d1179 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d966, d1179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8076 p hg
    simpa only [d4397, d966, d1179, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d966, d1179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7812 p hg
    simpa only [d4397, d966, d1179, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8078 (p : Pattern) (guard : d4397 p = 1) : d967 p ≤ (0 : Int) + d1180 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d967, d1180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8074 p hg
    simpa only [d967, d1180, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d967, d1180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8077 p hg
    simpa only [d967, d1180, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8079 (p : Pattern) (guard : d4148 p = 1) : d53 p ≤ (0 : Int) + d1181 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare845 p hg
    simpa only [d4148, d1181, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8075 p hg
    simpa only [d4148, d1181, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8080 (p : Pattern) (guard : d4397 p = 1) : d968 p ≤ (0 : Int) + d1182 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d968, d1182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8079 p hg
    simpa only [d4397, d968, d1182, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d968, d1182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7815 p hg
    simpa only [d4397, d968, d1182, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8081 (p : Pattern) (guard : d4397 p = 1) : d969 p ≤ (0 : Int) + d1183 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d969, d1183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8080 p hg
    simpa only [d969, d1183, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d969, d1183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4234 p hg
    simpa only [d969, d1183, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8082 (p : Pattern) (guard : d4397 p = 1) : d970 p ≤ (0 : Int) + d1184 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d970, d1184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8078 p hg
    simpa only [d970, d1184, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d970, d1184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8081 p hg
    simpa only [d970, d1184, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8083 (p : Pattern) (guard : d0 p = 1) : d53 p ≤ (0 : Int) + d370 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8084 (p : Pattern) (guard : d4148 p = 1) : d54 p ≤ (0 : Int) + d1185 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d54, d1185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare822 p hg
    simpa only [d4148, d54, d1185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d54, d1185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8083 p hg
    simpa only [d4148, d54, d1185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8085 (p : Pattern) (guard : d4397 p = 1) : d971 p ≤ (0 : Int) + d1186 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d971, d1186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8084 p hg
    simpa only [d4397, d971, d1186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d971, d1186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7820 p hg
    simpa only [d4397, d971, d1186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8086 (p : Pattern) (guard : d4148 p = 1) : d808 p ≤ (0 : Int) + d1181 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d808, d1181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare845 p hg
    simpa only [d4148, d808, d1181, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d808, d1181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3640 p hg
    simpa only [d4148, d808, d1181, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8087 (p : Pattern) (guard : d4397 p = 1) : d972 p ≤ (0 : Int) + d1182 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d972, d1182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8086 p hg
    simpa only [d4397, d972, d1182, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d972, d1182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7815 p hg
    simpa only [d4397, d972, d1182, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8088 (p : Pattern) (guard : d4397 p = 1) : d973 p ≤ (0 : Int) + d1187 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d973, d1187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8085 p hg
    simpa only [d973, d1187, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d973, d1187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8087 p hg
    simpa only [d973, d1187, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8089 (p : Pattern) (guard : d4397 p = 1) : d972 p ≤ (0 : Int) + d1188 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d972, d1188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8086 p hg
    simpa only [d4397, d972, d1188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d972, d1188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4397, d972, d1188, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8090 (p : Pattern) (guard : d4397 p = 1) : d974 p ≤ (0 : Int) + d1189 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d974, d1189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8089 p hg
    simpa only [d974, d1189, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d974, d1189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4234 p hg
    simpa only [d974, d1189, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8091 (p : Pattern) (guard : d4397 p = 1) : d975 p ≤ (0 : Int) + d1190 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d975, d1190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8088 p hg
    simpa only [d975, d1190, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d975, d1190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8090 p hg
    simpa only [d975, d1190, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8092 (p : Pattern) (guard : d4397 p = 1) : d976 p ≤ (0 : Int) + d1191 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d976, d1191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8082 p hg
    simpa only [d976, d1191, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d976, d1191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8091 p hg
    simpa only [d976, d1191, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8093 (p : Pattern) (guard : d4397 p = 1) : d977 p ≤ (0 : Int) + d1192 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d977, d1192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8072 p hg
    simpa only [d977, d1192, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d977, d1192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8092 p hg
    simpa only [d977, d1192, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8094 (p : Pattern) (guard : d0 p = 1) : d389 p ≤ (0 : Int) + d1193 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8095 (p : Pattern) (guard : d4397 p = 1) : d978 p ≤ (0 : Int) + d1194 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d978, d1194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3655 p hg
    simpa only [d4397, d978, d1194, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d978, d1194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8094 p hg
    simpa only [d4397, d978, d1194, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8096 (p : Pattern) (guard : d4397 p = 1) : d979 p ≤ (0 : Int) + d1195 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d979, d1195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8095 p hg
    simpa only [d979, d1195, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d979, d1195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8077 p hg
    simpa only [d979, d1195, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8097 (p : Pattern) (guard : d4397 p = 1) : d980 p ≤ (0 : Int) + d1196 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d980, d1196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8096 p hg
    simpa only [d980, d1196, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d980, d1196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8081 p hg
    simpa only [d980, d1196, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8098 (p : Pattern) (guard : d0 p = 1) : d53 p ≤ (0 : Int) + d360 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8099 (p : Pattern) (guard : d4148 p = 1) : d54 p ≤ (0 : Int) + d1197 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d54, d1197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare822 p hg
    simpa only [d4148, d54, d1197, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d54, d1197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8098 p hg
    simpa only [d4148, d54, d1197, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8100 (p : Pattern) (guard : d4397 p = 1) : d981 p ≤ (0 : Int) + d1198 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d981, d1198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8099 p hg
    simpa only [d4397, d981, d1198, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d981, d1198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7832 p hg
    simpa only [d4397, d981, d1198, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8101 (p : Pattern) (guard : d4397 p = 1) : d982 p ≤ (0 : Int) + d1199 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d982, d1199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8100 p hg
    simpa only [d982, d1199, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d982, d1199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8087 p hg
    simpa only [d982, d1199, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8102 (p : Pattern) (guard : d4397 p = 1) : d983 p ≤ (0 : Int) + d1200 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d983, d1200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8101 p hg
    simpa only [d983, d1200, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d983, d1200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8090 p hg
    simpa only [d983, d1200, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8103 (p : Pattern) (guard : d4397 p = 1) : d984 p ≤ (0 : Int) + d1201 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d984, d1201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8097 p hg
    simpa only [d984, d1201, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d984, d1201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8102 p hg
    simpa only [d984, d1201, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8104 (p : Pattern) (guard : d4397 p = 1) : d985 p ≤ (0 : Int) + d1202 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d985, d1202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3665 p hg
    simpa only [d4397, d985, d1202, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d985, d1202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7815 p hg
    simpa only [d4397, d985, d1202, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8105 (p : Pattern) (guard : d4397 p = 1) : d986 p ≤ (0 : Int) + d1203 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d986, d1203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8104 p hg
    simpa only [d986, d1203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d986, d1203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4248 p hg
    simpa only [d986, d1203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8106 (p : Pattern) (guard : d4397 p = 1) : d987 p ≤ (0 : Int) + d1204 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d987, d1204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8105 p hg
    simpa only [d987, d1204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d987, d1204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4250 p hg
    simpa only [d987, d1204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8107 (p : Pattern) (guard : d4397 p = 1) : d95 p ≤ (0 : Int) + d95 p := by
  omega
theorem compare8108 (p : Pattern) (guard : d4397 p = 1) : d988 p ≤ (0 : Int) + d1205 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d988, d1205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8106 p hg
    simpa only [d988, d1205, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d988, d1205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8107 p hg
    simpa only [d988, d1205, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8109 (p : Pattern) (guard : d4397 p = 1) : d989 p ≤ (0 : Int) + d1206 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d989, d1206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8103 p hg
    simpa only [d989, d1206, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d989, d1206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8108 p hg
    simpa only [d989, d1206, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8110 (p : Pattern) (guard : d4397 p = 1) : d990 p ≤ (0 : Int) + d1207 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d990, d1207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8093 p hg
    simpa only [d990, d1207, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d990, d1207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8109 p hg
    simpa only [d990, d1207, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8111 (p : Pattern) (guard : d0 p = 1) : d386 p ≤ (0 : Int) + d1185 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8112 (p : Pattern) (guard : d4397 p = 1) : d991 p ≤ (0 : Int) + d1209 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d991, d1209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3675 p hg
    simpa only [d4397, d991, d1209, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d991, d1209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8111 p hg
    simpa only [d4397, d991, d1209, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8113 (p : Pattern) (guard : d0 p = 1) : d33 p ≤ (0 : Int) + d373 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8114 (p : Pattern) (guard : d4148 p = 1) : d950 p ≤ (0 : Int) + d1193 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d950, d1193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare822 p hg
    simpa only [d4148, d950, d1193, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d950, d1193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8113 p hg
    simpa only [d4148, d950, d1193, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8115 (p : Pattern) (guard : d4397 p = 1) : d992 p ≤ (0 : Int) + d1210 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d992, d1210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8114 p hg
    simpa only [d4397, d992, d1210, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d992, d1210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7812 p hg
    simpa only [d4397, d992, d1210, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8116 (p : Pattern) (guard : d4397 p = 1) : d993 p ≤ (0 : Int) + d1211 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d993, d1211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8112 p hg
    simpa only [d993, d1211, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d993, d1211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8115 p hg
    simpa only [d993, d1211, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8117 (p : Pattern) (guard : d0 p = 1) : d33 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8118 (p : Pattern) (guard : d4148 p = 1) : d33 p ≤ (0 : Int) + d1212 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3623 p hg
    simpa only [d4148, d1212, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8117 p hg
    simpa only [d4148, d1212, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8119 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d1158 p := by
  change (0 : Int) = 1 at guard
  omega
end NetHack.Sokoban22Refined85
