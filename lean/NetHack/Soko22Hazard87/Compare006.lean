import NetHack.Soko22Hazard87.Compare005
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare1500 (p : Pattern) (guard : d1106 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1095 p = 1 := by simpa only [d1106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1461 p hg
    simpa only [d1106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1105 p = 1 := by simpa only [d1106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1499 p hg
    simpa only [d1106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1501 (p : Pattern) (guard : d1107 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1106 p = 1 := by simpa only [d1107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1500 p hg
    simpa only [d1107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d135 p = 1 := by simpa only [d1107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1220 p hg
    simpa only [d1107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1502 (p : Pattern) (guard : d1108 p = 1) : d47652 p ≤ (-1 : Int) + d47731 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1107 p = 1 := by simpa only [d1108, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1501 p hg
    simpa only [d1108, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1108, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1148 p hg
    simpa only [d1108, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1503 (p : Pattern) (guard : d1109 p = 1) : d47652 p ≤ (-1 : Int) + d47731 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1098 p = 1 := by simpa only [d1109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1464 p hg
    simpa only [d1109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1108 p = 1 := by simpa only [d1109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1502 p hg
    simpa only [d1109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1504 (p : Pattern) (guard : d1385 p = 1) : d47652 p ≤ (-1 : Int) + d47732 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1385, d47732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1136 p hg
    simpa only [d1385, d47732, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1109 p = 1 := by simpa only [d1385, d47732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1503 p hg
    simpa only [d1385, d47732, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1505 (p : Pattern) (guard : d1104 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 223 with
  | false =>
    have hg : d132 p = 1 := by simpa only [d1104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1231 p hg
    simpa only [d1104, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d18 p = 1 := by simpa only [d1104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1159 p hg
    simpa only [d1104, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1506 (p : Pattern) (guard : d1105 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1104 p = 1 := by simpa only [d1105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1505 p hg
    simpa only [d1105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1156 p hg
    simpa only [d1105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1507 (p : Pattern) (guard : d1106 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1095 p = 1 := by simpa only [d1106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1489 p hg
    simpa only [d1106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1105 p = 1 := by simpa only [d1106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1506 p hg
    simpa only [d1106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1508 (p : Pattern) (guard : d1107 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1106 p = 1 := by simpa only [d1107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1507 p hg
    simpa only [d1107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d135 p = 1 := by simpa only [d1107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1234 p hg
    simpa only [d1107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1509 (p : Pattern) (guard : d1108 p = 1) : d47619 p ≤ (-1 : Int) + d47708 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1107 p = 1 := by simpa only [d1108, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1508 p hg
    simpa only [d1108, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1108, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1164 p hg
    simpa only [d1108, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1510 (p : Pattern) (guard : d1109 p = 1) : d47619 p ≤ (-1 : Int) + d47708 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1098 p = 1 := by simpa only [d1109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1492 p hg
    simpa only [d1109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1108 p = 1 := by simpa only [d1109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1509 p hg
    simpa only [d1109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1511 (p : Pattern) (guard : d1110 p = 1) : d47797 p ≤ (-1 : Int) + d47733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1109 p = 1 := by simpa only [d1110, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1510 p hg
    simpa only [d1110, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1110, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1168 p hg
    simpa only [d1110, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1512 (p : Pattern) (guard : d1386 p = 1) : d47798 p ≤ (-1 : Int) + d47734 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1385 p = 1 := by simpa only [d1386, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1504 p hg
    simpa only [d1386, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1110 p = 1 := by simpa only [d1386, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1511 p hg
    simpa only [d1386, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1513 (p : Pattern) (guard : d17974 p = 1) : d47799 p ≤ (-1 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1386 p = 1 := by simpa only [d17974, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1512 p hg
    simpa only [d17974, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17974, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1171 p hg
    simpa only [d17974, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1514 (p : Pattern) (guard : d17975 p = 1) : d47803 p ≤ (-1 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d17974 p = 1 := by simpa only [d17975, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1513 p hg
    simpa only [d17975, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17975, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1173 p hg
    simpa only [d17975, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1515 (p : Pattern) (guard : d60701 p = 1) : d47803 p ≤ (-1 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d17954 p = 1 := by simpa only [d60701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1497 p hg
    simpa only [d60701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17975 p = 1 := by simpa only [d60701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1514 p hg
    simpa only [d60701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1516 (p : Pattern) (guard : d1115 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1140 p hg
    simpa only [d1115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d18 p = 1 := by simpa only [d1115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1143 p hg
    simpa only [d1115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1517 (p : Pattern) (guard : d1116 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1115 p = 1 := by simpa only [d1116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1516 p hg
    simpa only [d1116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1140 p hg
    simpa only [d1116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1518 (p : Pattern) (guard : d1117 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1116 p = 1 := by simpa only [d1117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1517 p hg
    simpa only [d1117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d20 p = 1 := by simpa only [d1117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1145 p hg
    simpa only [d1117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1519 (p : Pattern) (guard : d1118 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1117 p = 1 := by simpa only [d1118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1518 p hg
    simpa only [d1118, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d21 p = 1 := by simpa only [d1118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1146 p hg
    simpa only [d1118, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1520 (p : Pattern) (guard : d1119 p = 1) : d47652 p ≤ (-1 : Int) + d47731 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1118 p = 1 := by simpa only [d1119, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1519 p hg
    simpa only [d1119, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1119, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1148 p hg
    simpa only [d1119, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1521 (p : Pattern) (guard : d1120 p = 1) : d47652 p ≤ (-1 : Int) + d47731 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1108 p = 1 := by simpa only [d1120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1502 p hg
    simpa only [d1120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1119 p = 1 := by simpa only [d1120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1520 p hg
    simpa only [d1120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1522 (p : Pattern) (guard : d1391 p = 1) : d47652 p ≤ (-1 : Int) + d47732 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1391, d47732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1136 p hg
    simpa only [d1391, d47732, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1120 p = 1 := by simpa only [d1391, d47732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1521 p hg
    simpa only [d1391, d47732, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1523 (p : Pattern) (guard : d1115 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1156 p hg
    simpa only [d1115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d18 p = 1 := by simpa only [d1115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1159 p hg
    simpa only [d1115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1524 (p : Pattern) (guard : d1116 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1115 p = 1 := by simpa only [d1116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1523 p hg
    simpa only [d1116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1156 p hg
    simpa only [d1116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1525 (p : Pattern) (guard : d1117 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1116 p = 1 := by simpa only [d1117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1524 p hg
    simpa only [d1117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d20 p = 1 := by simpa only [d1117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1161 p hg
    simpa only [d1117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1526 (p : Pattern) (guard : d1118 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1117 p = 1 := by simpa only [d1118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1525 p hg
    simpa only [d1118, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d21 p = 1 := by simpa only [d1118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1162 p hg
    simpa only [d1118, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1527 (p : Pattern) (guard : d1119 p = 1) : d47619 p ≤ (-1 : Int) + d47708 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1118 p = 1 := by simpa only [d1119, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1526 p hg
    simpa only [d1119, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1119, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1164 p hg
    simpa only [d1119, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1528 (p : Pattern) (guard : d1120 p = 1) : d47619 p ≤ (-1 : Int) + d47708 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1108 p = 1 := by simpa only [d1120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1509 p hg
    simpa only [d1120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1119 p = 1 := by simpa only [d1120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1527 p hg
    simpa only [d1120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1529 (p : Pattern) (guard : d1121 p = 1) : d47797 p ≤ (-1 : Int) + d47733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1120 p = 1 := by simpa only [d1121, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1528 p hg
    simpa only [d1121, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1121, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1168 p hg
    simpa only [d1121, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1530 (p : Pattern) (guard : d1392 p = 1) : d47798 p ≤ (-1 : Int) + d47734 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1391 p = 1 := by simpa only [d1392, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1522 p hg
    simpa only [d1392, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1121 p = 1 := by simpa only [d1392, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1529 p hg
    simpa only [d1392, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1531 (p : Pattern) (guard : d17976 p = 1) : d47799 p ≤ (-1 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1392 p = 1 := by simpa only [d17976, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1530 p hg
    simpa only [d17976, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17976, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1171 p hg
    simpa only [d17976, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1532 (p : Pattern) (guard : d17977 p = 1) : d47803 p ≤ (-1 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d17976 p = 1 := by simpa only [d17977, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1531 p hg
    simpa only [d17977, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17977, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1173 p hg
    simpa only [d17977, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1533 (p : Pattern) (guard : d17978 p = 1) : d47803 p ≤ (-1 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d17975 p = 1 := by simpa only [d17978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1514 p hg
    simpa only [d17978, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17977 p = 1 := by simpa only [d17978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1532 p hg
    simpa only [d17978, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1534 (p : Pattern) (guard : d60703 p = 1) : d47803 p ≤ (-1 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d60701 p = 1 := by simpa only [d60703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1515 p hg
    simpa only [d60703, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17978 p = 1 := by simpa only [d60703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1533 p hg
    simpa only [d60703, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1535 (p : Pattern) (guard : d18007 p = 1) : d47803 p ≤ (-1 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d17977 p = 1 := by simpa only [d18007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1532 p hg
    simpa only [d18007, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d18007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1175 p hg
    simpa only [d18007, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1536 (p : Pattern) (guard : d60707 p = 1) : d47803 p ≤ (-1 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d17978 p = 1 := by simpa only [d60707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1533 p hg
    simpa only [d60707, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d18007 p = 1 := by simpa only [d60707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1535 p hg
    simpa only [d60707, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1537 (p : Pattern) (guard : d60708 p = 1) : d47803 p ≤ (-1 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d60703 p = 1 := by simpa only [d60708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1534 p hg
    simpa only [d60708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60707 p = 1 := by simpa only [d60708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1536 p hg
    simpa only [d60708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1538 (p : Pattern) (guard : d60709 p = 1) : d47804 p ≤ (-1 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60709, d47804, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1135 p hg
    simpa only [d60709, d47804, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60708 p = 1 := by simpa only [d60709, d47804, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1537 p hg
    simpa only [d60709, d47804, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1539 (p : Pattern) (guard : d60710 p = 1) : d47805 p ≤ (-1 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60710, d47805, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1134 p hg
    simpa only [d60710, d47805, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60709 p = 1 := by simpa only [d60710, d47805, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1538 p hg
    simpa only [d60710, d47805, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1540 (p : Pattern) (guard : d1132 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1116 p = 1 := by simpa only [d1132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1517 p hg
    simpa only [d1132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1140 p hg
    simpa only [d1132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1541 (p : Pattern) (guard : d1133 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1132 p = 1 := by simpa only [d1133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1540 p hg
    simpa only [d1133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1140 p hg
    simpa only [d1133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1542 (p : Pattern) (guard : d1134 p = 1) : d47652 p ≤ (-1 : Int) + d47731 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1133 p = 1 := by simpa only [d1134, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1541 p hg
    simpa only [d1134, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1134, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1148 p hg
    simpa only [d1134, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1543 (p : Pattern) (guard : d1135 p = 1) : d47652 p ≤ (-1 : Int) + d47731 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1134 p = 1 := by simpa only [d1135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1542 p hg
    simpa only [d1135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1150 p hg
    simpa only [d1135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1544 (p : Pattern) (guard : d1406 p = 1) : d47652 p ≤ (-1 : Int) + d47732 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1406, d47732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1136 p hg
    simpa only [d1406, d47732, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1135 p = 1 := by simpa only [d1406, d47732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1543 p hg
    simpa only [d1406, d47732, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1545 (p : Pattern) (guard : d1132 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1116 p = 1 := by simpa only [d1132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1524 p hg
    simpa only [d1132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1156 p hg
    simpa only [d1132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1546 (p : Pattern) (guard : d1133 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1132 p = 1 := by simpa only [d1133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1545 p hg
    simpa only [d1133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1156 p hg
    simpa only [d1133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1547 (p : Pattern) (guard : d1134 p = 1) : d47619 p ≤ (-1 : Int) + d47708 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1133 p = 1 := by simpa only [d1134, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1546 p hg
    simpa only [d1134, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1134, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1164 p hg
    simpa only [d1134, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1548 (p : Pattern) (guard : d1135 p = 1) : d47619 p ≤ (-1 : Int) + d47708 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1134 p = 1 := by simpa only [d1135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1547 p hg
    simpa only [d1135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1166 p hg
    simpa only [d1135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1549 (p : Pattern) (guard : d1136 p = 1) : d47797 p ≤ (-1 : Int) + d47733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1135 p = 1 := by simpa only [d1136, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1548 p hg
    simpa only [d1136, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1136, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1168 p hg
    simpa only [d1136, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1550 (p : Pattern) (guard : d1407 p = 1) : d47798 p ≤ (-1 : Int) + d47734 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1406 p = 1 := by simpa only [d1407, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1544 p hg
    simpa only [d1407, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1136 p = 1 := by simpa only [d1407, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1549 p hg
    simpa only [d1407, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1551 (p : Pattern) (guard : d60712 p = 1) : d47799 p ≤ (-1 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1407 p = 1 := by simpa only [d60712, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1550 p hg
    simpa only [d60712, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60712, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1171 p hg
    simpa only [d60712, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1552 (p : Pattern) (guard : d60713 p = 1) : d47803 p ≤ (-1 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d60712 p = 1 := by simpa only [d60713, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1551 p hg
    simpa only [d60713, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60713, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1173 p hg
    simpa only [d60713, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1553 (p : Pattern) (guard : d60714 p = 1) : d47803 p ≤ (-1 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d60713 p = 1 := by simpa only [d60714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1552 p hg
    simpa only [d60714, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1175 p hg
    simpa only [d60714, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1554 (p : Pattern) (guard : d60715 p = 1) : d47803 p ≤ (-1 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d18007 p = 1 := by simpa only [d60715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1535 p hg
    simpa only [d60715, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60714 p = 1 := by simpa only [d60715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1553 p hg
    simpa only [d60715, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1555 (p : Pattern) (guard : d60716 p = 1) : d47803 p ≤ (-1 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d60707 p = 1 := by simpa only [d60716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1536 p hg
    simpa only [d60716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60715 p = 1 := by simpa only [d60716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1554 p hg
    simpa only [d60716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1556 (p : Pattern) (guard : d60717 p = 1) : d47804 p ≤ (-1 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60717, d47804, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1135 p hg
    simpa only [d60717, d47804, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60716 p = 1 := by simpa only [d60717, d47804, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1555 p hg
    simpa only [d60717, d47804, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1557 (p : Pattern) (guard : d60718 p = 1) : d47805 p ≤ (-1 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60718, d47805, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1134 p hg
    simpa only [d60718, d47805, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60717 p = 1 := by simpa only [d60718, d47805, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1556 p hg
    simpa only [d60718, d47805, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1558 (p : Pattern) (guard : d60719 p = 1) : d47805 p ≤ (-1 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d60710 p = 1 := by simpa only [d60719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1539 p hg
    simpa only [d60719, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60718 p = 1 := by simpa only [d60719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1557 p hg
    simpa only [d60719, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1559 (p : Pattern) (guard : d60724 p = 1) : d47805 p ≤ (-1 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d60718 p = 1 := by simpa only [d60724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1557 p hg
    simpa only [d60724, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1181 p hg
    simpa only [d60724, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1560 (p : Pattern) (guard : d60725 p = 1) : d47805 p ≤ (-1 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d60719 p = 1 := by simpa only [d60725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1558 p hg
    simpa only [d60725, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60724 p = 1 := by simpa only [d60725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1559 p hg
    simpa only [d60725, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1561 (p : Pattern) (guard : d60726 p = 1) : d47805 p ≤ (-1 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d60725 p = 1 := by simpa only [d60726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1560 p hg
    simpa only [d60726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1181 p hg
    simpa only [d60726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1562 (p : Pattern) (guard : d60727 p = 1) : d47807 p ≤ (-1 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d60726 p = 1 := by simpa only [d60727, d47807, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1561 p hg
    simpa only [d60727, d47807, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60727, d47807, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1185 p hg
    simpa only [d60727, d47807, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1563 (p : Pattern) (guard : d60728 p = 1) : d47808 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60728, d47808, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1133 p hg
    simpa only [d60728, d47808, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60727 p = 1 := by simpa only [d60728, d47808, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1562 p hg
    simpa only [d60728, d47808, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1564 (p : Pattern) (guard : d60733 p = 1) : d47805 p ≤ (-1 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d60724 p = 1 := by simpa only [d60733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1559 p hg
    simpa only [d60733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1181 p hg
    simpa only [d60733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1565 (p : Pattern) (guard : d60734 p = 1) : d47805 p ≤ (-1 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d60733 p = 1 := by simpa only [d60734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1564 p hg
    simpa only [d60734, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1181 p hg
    simpa only [d60734, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1566 (p : Pattern) (guard : d60735 p = 1) : d47807 p ≤ (-1 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d60734 p = 1 := by simpa only [d60735, d47807, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1565 p hg
    simpa only [d60735, d47807, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60735, d47807, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1185 p hg
    simpa only [d60735, d47807, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1567 (p : Pattern) (guard : d60736 p = 1) : d47808 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60736, d47808, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1133 p hg
    simpa only [d60736, d47808, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60735 p = 1 := by simpa only [d60736, d47808, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1566 p hg
    simpa only [d60736, d47808, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1568 (p : Pattern) (guard : d60737 p = 1) : d47808 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d60728 p = 1 := by simpa only [d60737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1563 p hg
    simpa only [d60737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60736 p = 1 := by simpa only [d60737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1567 p hg
    simpa only [d60737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1569 (p : Pattern) (guard : d60738 p = 1) : d47808 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d60737 p = 1 := by simpa only [d60738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1568 p hg
    simpa only [d60738, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1132 p hg
    simpa only [d60738, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1570 (p : Pattern) (guard : d60739 p = 1) : d47808 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d60738 p = 1 := by simpa only [d60739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1569 p hg
    simpa only [d60739, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1132 p hg
    simpa only [d60739, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1571 (p : Pattern) (guard : d60740 p = 1) : d47808 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d60739 p = 1 := by simpa only [d60740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1570 p hg
    simpa only [d60740, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1132 p hg
    simpa only [d60740, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1572 (p : Pattern) (guard : d60750 p = 1) : d47808 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d60736 p = 1 := by simpa only [d60750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1567 p hg
    simpa only [d60750, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1132 p hg
    simpa only [d60750, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1573 (p : Pattern) (guard : d60751 p = 1) : d47808 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d60750 p = 1 := by simpa only [d60751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1572 p hg
    simpa only [d60751, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1132 p hg
    simpa only [d60751, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1574 (p : Pattern) (guard : d60752 p = 1) : d47808 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d60751 p = 1 := by simpa only [d60752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1573 p hg
    simpa only [d60752, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1132 p hg
    simpa only [d60752, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1575 (p : Pattern) (guard : d60753 p = 1) : d47808 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d60752 p = 1 := by simpa only [d60753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1574 p hg
    simpa only [d60753, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1132 p hg
    simpa only [d60753, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1576 (p : Pattern) (guard : d61145 p = 1) : d47808 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d60740 p = 1 := by simpa only [d61145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1571 p hg
    simpa only [d61145, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60753 p = 1 := by simpa only [d61145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1575 p hg
    simpa only [d61145, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1577 (p : Pattern) (guard : d61146 p = 1) : d47808 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d61146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1132 p hg
    simpa only [d61146, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d61145 p = 1 := by simpa only [d61146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1576 p hg
    simpa only [d61146, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1578 (p : Pattern) (guard : d61147 p = 1) : d47808 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d61146 p = 1 := by simpa only [d61147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1577 p hg
    simpa only [d61147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d61147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1132 p hg
    simpa only [d61147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1579 (p : Pattern) (guard : d61148 p = 1) : d47808 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d61148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1132 p hg
    simpa only [d61148, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d61147 p = 1 := by simpa only [d61148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1578 p hg
    simpa only [d61148, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1580 (p : Pattern) (guard : d61149 p = 1) : d47808 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d61149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1132 p hg
    simpa only [d61149, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d61148 p = 1 := by simpa only [d61149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1579 p hg
    simpa only [d61149, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1581 (p : Pattern) (guard : d61150 p = 1) : d47809 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d61150, d47809, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1131 p hg
    simpa only [d61150, d47809, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d61149 p = 1 := by simpa only [d61150, d47809, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1580 p hg
    simpa only [d61150, d47809, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1582 (p : Pattern) (guard : d61151 p = 1) : d47809 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d61151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1130 p hg
    simpa only [d61151, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d61150 p = 1 := by simpa only [d61151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1581 p hg
    simpa only [d61151, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1583 (p : Pattern) (guard : d61152 p = 1) : d47809 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 69 with
  | false =>
    have hg : d61151 p = 1 := by simpa only [d61152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1582 p hg
    simpa only [d61152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d61152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1130 p hg
    simpa only [d61152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1584 (p : Pattern) (guard : d61153 p = 1) : d47809 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 51 with
  | false =>
    have hg : d61152 p = 1 := by simpa only [d61153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1583 p hg
    simpa only [d61153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d61153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1130 p hg
    simpa only [d61153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1585 (p : Pattern) (guard : d61154 p = 1) : d47809 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 50 with
  | false =>
    have hg : d61153 p = 1 := by simpa only [d61154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1584 p hg
    simpa only [d61154, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d61154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1130 p hg
    simpa only [d61154, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1586 (p : Pattern) (guard : d61155 p = 1) : d47865 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 49 with
  | false =>
    have hg : d61154 p = 1 := by simpa only [d61155, d47865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1585 p hg
    simpa only [d61155, d47865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d61155, d47865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1202 p hg
    simpa only [d61155, d47865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1587 (p : Pattern) (guard : d61156 p = 1) : d47866 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 48 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d61156, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1129 p hg
    simpa only [d61156, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d61155 p = 1 := by simpa only [d61156, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1586 p hg
    simpa only [d61156, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1588 (p : Pattern) (guard : d61157 p = 1) : d47866 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d61157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1128 p hg
    simpa only [d61157, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d61156 p = 1 := by simpa only [d61157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1587 p hg
    simpa only [d61157, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1589 (p : Pattern) (guard : d61158 p = 1) : d47866 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d61158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1128 p hg
    simpa only [d61158, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d61157 p = 1 := by simpa only [d61158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1588 p hg
    simpa only [d61158, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1590 (p : Pattern) (guard : d61159 p = 1) : d47866 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d61159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1128 p hg
    simpa only [d61159, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d61158 p = 1 := by simpa only [d61159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1589 p hg
    simpa only [d61159, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1591 (p : Pattern) (guard : d61160 p = 1) : d47866 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d61160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1128 p hg
    simpa only [d61160, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d61159 p = 1 := by simpa only [d61160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1590 p hg
    simpa only [d61160, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1592 (p : Pattern) (guard : d61161 p = 1) : d47866 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d61161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1128 p hg
    simpa only [d61161, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d61160 p = 1 := by simpa only [d61161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1591 p hg
    simpa only [d61161, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1593 (p : Pattern) (guard : d61162 p = 1) : d47866 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d61162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1128 p hg
    simpa only [d61162, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d61161 p = 1 := by simpa only [d61162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1592 p hg
    simpa only [d61162, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1594 (p : Pattern) (guard : d61163 p = 1) : d47866 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d61163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1128 p hg
    simpa only [d61163, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d61162 p = 1 := by simpa only [d61163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1593 p hg
    simpa only [d61163, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1595 (p : Pattern) (guard : d61164 p = 1) : d47866 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d61164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1128 p hg
    simpa only [d61164, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d61163 p = 1 := by simpa only [d61164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1594 p hg
    simpa only [d61164, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1596 (p : Pattern) (guard : d61165 p = 1) : d47866 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 10252 with
  | false =>
    have hg : d61144 p = 1 := by simpa only [d61165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1438 p hg
    simpa only [d61165, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d61164 p = 1 := by simpa only [d61165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1595 p hg
    simpa only [d61165, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1597 (p : Pattern) (guard : d1199 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1140 p hg
    simpa only [d1199, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d820 p = 1 := by simpa only [d1199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1439 p hg
    simpa only [d1199, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1598 (p : Pattern) (guard : d1200 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 223 with
  | false =>
    have hg : d1199 p = 1 := by simpa only [d1200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1597 p hg
    simpa only [d1200, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1140 p hg
    simpa only [d1200, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1599 (p : Pattern) (guard : d1201 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1200 p = 1 := by simpa only [d1201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1598 p hg
    simpa only [d1201, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1140 p hg
    simpa only [d1201, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1600 (p : Pattern) (guard : d308 p = 1) : d2 p ≤ (-1 : Int) + d3 p := by
  have ha := bounds2 p
  have hb := bounds3 p
  omega
theorem compare1601 (p : Pattern) (guard : d1519 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 246 with
  | false =>
    have hg : d308 p = 1 := by simpa only [d1519, d47630, d47715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1600 p hg
    simpa only [d1519, d47630, d47715, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1519, d47630, d47715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1138 p hg
    simpa only [d1519, d47630, d47715, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1602 (p : Pattern) (guard : d1520 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 226 with
  | false =>
    have hg : d309 p = 1 := by simpa only [d1520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1277 p hg
    simpa only [d1520, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1519 p = 1 := by simpa only [d1520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1601 p hg
    simpa only [d1520, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1603 (p : Pattern) (guard : d1521 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 225 with
  | false =>
    have hg : d528 p = 1 := by simpa only [d1521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1347 p hg
    simpa only [d1521, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1520 p = 1 := by simpa only [d1521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1602 p hg
    simpa only [d1521, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1604 (p : Pattern) (guard : d1522 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 224 with
  | false =>
    have hg : d820 p = 1 := by simpa only [d1522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1439 p hg
    simpa only [d1522, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1521 p = 1 := by simpa only [d1522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1603 p hg
    simpa only [d1522, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1605 (p : Pattern) (guard : d1523 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 246 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1523, d47630, d47715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1443 p hg
    simpa only [d1523, d47630, d47715, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d308 p = 1 := by simpa only [d1523, d47630, d47715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1276 p hg
    simpa only [d1523, d47630, d47715, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1606 (p : Pattern) (guard : d1524 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1523 p = 1 := by simpa only [d1524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1605 p hg
    simpa only [d1524, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1084 p = 1 := by simpa only [d1524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1444 p hg
    simpa only [d1524, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1607 (p : Pattern) (guard : d1525 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1524 p = 1 := by simpa only [d1525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1606 p hg
    simpa only [d1525, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1140 p hg
    simpa only [d1525, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1608 (p : Pattern) (guard : d1526 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1140 p hg
    simpa only [d1526, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1525 p = 1 := by simpa only [d1526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1607 p hg
    simpa only [d1526, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1609 (p : Pattern) (guard : d1527 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 223 with
  | false =>
    have hg : d1522 p = 1 := by simpa only [d1527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1604 p hg
    simpa only [d1527, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1526 p = 1 := by simpa only [d1527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1608 p hg
    simpa only [d1527, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1610 (p : Pattern) (guard : d1528 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1140 p hg
    simpa only [d1528, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1087 p = 1 := by simpa only [d1528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1447 p hg
    simpa only [d1528, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1611 (p : Pattern) (guard : d1529 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1527 p = 1 := by simpa only [d1529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1609 p hg
    simpa only [d1529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1528 p = 1 := by simpa only [d1529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1610 p hg
    simpa only [d1529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1612 (p : Pattern) (guard : d1530 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1201 p = 1 := by simpa only [d1530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1599 p hg
    simpa only [d1530, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1529 p = 1 := by simpa only [d1530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1611 p hg
    simpa only [d1530, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1613 (p : Pattern) (guard : d1203 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1140 p hg
    simpa only [d1203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d826 p = 1 := by simpa only [d1203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1452 p hg
    simpa only [d1203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1614 (p : Pattern) (guard : d1204 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 223 with
  | false =>
    have hg : d1203 p = 1 := by simpa only [d1204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1613 p hg
    simpa only [d1204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1140 p hg
    simpa only [d1204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1615 (p : Pattern) (guard : d1205 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1204 p = 1 := by simpa only [d1205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1614 p hg
    simpa only [d1205, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1140 p hg
    simpa only [d1205, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1616 (p : Pattern) (guard : d1531 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1519 p = 1 := by simpa only [d1531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1601 p hg
    simpa only [d1531, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1140 p hg
    simpa only [d1531, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1617 (p : Pattern) (guard : d1532 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1520 p = 1 := by simpa only [d1532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1602 p hg
    simpa only [d1532, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1531 p = 1 := by simpa only [d1532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1616 p hg
    simpa only [d1532, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1618 (p : Pattern) (guard : d1533 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 224 with
  | false =>
    have hg : d826 p = 1 := by simpa only [d1533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1452 p hg
    simpa only [d1533, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1532 p = 1 := by simpa only [d1533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1617 p hg
    simpa only [d1533, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1619 (p : Pattern) (guard : d1534 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 223 with
  | false =>
    have hg : d1533 p = 1 := by simpa only [d1534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1618 p hg
    simpa only [d1534, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1140 p hg
    simpa only [d1534, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1620 (p : Pattern) (guard : d1535 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1534 p = 1 := by simpa only [d1535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1619 p hg
    simpa only [d1535, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1140 p hg
    simpa only [d1535, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1621 (p : Pattern) (guard : d1536 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1205 p = 1 := by simpa only [d1536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1615 p hg
    simpa only [d1536, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1535 p = 1 := by simpa only [d1536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1620 p hg
    simpa only [d1536, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1622 (p : Pattern) (guard : d1537 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1530 p = 1 := by simpa only [d1537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1612 p hg
    simpa only [d1537, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1536 p = 1 := by simpa only [d1537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1621 p hg
    simpa only [d1537, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1623 (p : Pattern) (guard : d1538 p = 1) : d47652 p ≤ (-1 : Int) + d47731 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1537 p = 1 := by simpa only [d1538, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1622 p hg
    simpa only [d1538, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1538, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1148 p hg
    simpa only [d1538, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1624 (p : Pattern) (guard : d1539 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1521 p = 1 := by simpa only [d1539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1603 p hg
    simpa only [d1539, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1532 p = 1 := by simpa only [d1539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1617 p hg
    simpa only [d1539, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1625 (p : Pattern) (guard : d1540 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1519 p = 1 := by simpa only [d1540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1601 p hg
    simpa only [d1540, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15 p = 1 := by simpa only [d1540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1139 p hg
    simpa only [d1540, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1626 (p : Pattern) (guard : d1541 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1540 p = 1 := by simpa only [d1541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1625 p hg
    simpa only [d1541, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1140 p hg
    simpa only [d1541, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1627 (p : Pattern) (guard : d1542 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1525 p = 1 := by simpa only [d1542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1607 p hg
    simpa only [d1542, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1541 p = 1 := by simpa only [d1542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1626 p hg
    simpa only [d1542, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1628 (p : Pattern) (guard : d1543 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 223 with
  | false =>
    have hg : d1539 p = 1 := by simpa only [d1543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1624 p hg
    simpa only [d1543, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1542 p = 1 := by simpa only [d1543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1627 p hg
    simpa only [d1543, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1629 (p : Pattern) (guard : d1544 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1140 p hg
    simpa only [d1544, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1093 p = 1 := by simpa only [d1544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1459 p hg
    simpa only [d1544, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1630 (p : Pattern) (guard : d1545 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1543 p = 1 := by simpa only [d1545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1628 p hg
    simpa only [d1545, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1544 p = 1 := by simpa only [d1545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1629 p hg
    simpa only [d1545, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1631 (p : Pattern) (guard : d1546 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1529 p = 1 := by simpa only [d1546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1611 p hg
    simpa only [d1546, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1545 p = 1 := by simpa only [d1546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1630 p hg
    simpa only [d1546, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1632 (p : Pattern) (guard : d1547 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1531 p = 1 := by simpa only [d1547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1616 p hg
    simpa only [d1547, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1140 p hg
    simpa only [d1547, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1633 (p : Pattern) (guard : d1548 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1532 p = 1 := by simpa only [d1548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1617 p hg
    simpa only [d1548, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1547 p = 1 := by simpa only [d1548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1632 p hg
    simpa only [d1548, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1634 (p : Pattern) (guard : d1549 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 223 with
  | false =>
    have hg : d1548 p = 1 := by simpa only [d1549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1633 p hg
    simpa only [d1549, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1140 p hg
    simpa only [d1549, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1635 (p : Pattern) (guard : d1550 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1549 p = 1 := by simpa only [d1550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1634 p hg
    simpa only [d1550, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1140 p hg
    simpa only [d1550, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1636 (p : Pattern) (guard : d1551 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1535 p = 1 := by simpa only [d1551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1620 p hg
    simpa only [d1551, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1550 p = 1 := by simpa only [d1551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1635 p hg
    simpa only [d1551, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1637 (p : Pattern) (guard : d1552 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1546 p = 1 := by simpa only [d1552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1631 p hg
    simpa only [d1552, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1551 p = 1 := by simpa only [d1552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1636 p hg
    simpa only [d1552, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1638 (p : Pattern) (guard : d1553 p = 1) : d47652 p ≤ (-1 : Int) + d47731 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1552 p = 1 := by simpa only [d1553, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1637 p hg
    simpa only [d1553, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1553, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1148 p hg
    simpa only [d1553, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1639 (p : Pattern) (guard : d1554 p = 1) : d47652 p ≤ (-1 : Int) + d47731 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1538 p = 1 := by simpa only [d1554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1623 p hg
    simpa only [d1554, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d1554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1638 p hg
    simpa only [d1554, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1640 (p : Pattern) (guard : d1857 p = 1) : d47652 p ≤ (-1 : Int) + d47732 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1857, d47732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1136 p hg
    simpa only [d1857, d47732, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1554 p = 1 := by simpa only [d1857, d47732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1639 p hg
    simpa only [d1857, d47732, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1641 (p : Pattern) (guard : d1199 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1156 p hg
    simpa only [d1199, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d820 p = 1 := by simpa only [d1199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1467 p hg
    simpa only [d1199, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1642 (p : Pattern) (guard : d1200 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 223 with
  | false =>
    have hg : d1199 p = 1 := by simpa only [d1200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1641 p hg
    simpa only [d1200, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1156 p hg
    simpa only [d1200, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1643 (p : Pattern) (guard : d1201 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1200 p = 1 := by simpa only [d1201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1642 p hg
    simpa only [d1201, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1156 p hg
    simpa only [d1201, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1644 (p : Pattern) (guard : d308 p = 1) : d4 p ≤ (-1 : Int) + d5 p := by
  have ha := bounds4 p
  have hb := bounds5 p
  omega
theorem compare1645 (p : Pattern) (guard : d1519 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 246 with
  | false =>
    have hg : d308 p = 1 := by simpa only [d1519, d47617, d47706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1644 p hg
    simpa only [d1519, d47617, d47706, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1519, d47617, d47706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1154 p hg
    simpa only [d1519, d47617, d47706, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1646 (p : Pattern) (guard : d1520 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 226 with
  | false =>
    have hg : d309 p = 1 := by simpa only [d1520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1291 p hg
    simpa only [d1520, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1519 p = 1 := by simpa only [d1520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1645 p hg
    simpa only [d1520, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1647 (p : Pattern) (guard : d1521 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 225 with
  | false =>
    have hg : d528 p = 1 := by simpa only [d1521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1363 p hg
    simpa only [d1521, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1520 p = 1 := by simpa only [d1521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1646 p hg
    simpa only [d1521, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1648 (p : Pattern) (guard : d1522 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 224 with
  | false =>
    have hg : d820 p = 1 := by simpa only [d1522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1467 p hg
    simpa only [d1522, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1521 p = 1 := by simpa only [d1522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1647 p hg
    simpa only [d1522, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1649 (p : Pattern) (guard : d1523 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 246 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1523, d47617, d47706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1471 p hg
    simpa only [d1523, d47617, d47706, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d308 p = 1 := by simpa only [d1523, d47617, d47706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1290 p hg
    simpa only [d1523, d47617, d47706, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1650 (p : Pattern) (guard : d1524 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1523 p = 1 := by simpa only [d1524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1649 p hg
    simpa only [d1524, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1084 p = 1 := by simpa only [d1524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1472 p hg
    simpa only [d1524, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1651 (p : Pattern) (guard : d1525 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1524 p = 1 := by simpa only [d1525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1650 p hg
    simpa only [d1525, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1156 p hg
    simpa only [d1525, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1652 (p : Pattern) (guard : d1526 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1156 p hg
    simpa only [d1526, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1525 p = 1 := by simpa only [d1526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1651 p hg
    simpa only [d1526, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1653 (p : Pattern) (guard : d1527 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 223 with
  | false =>
    have hg : d1522 p = 1 := by simpa only [d1527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1648 p hg
    simpa only [d1527, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1526 p = 1 := by simpa only [d1527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1652 p hg
    simpa only [d1527, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1654 (p : Pattern) (guard : d1528 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1156 p hg
    simpa only [d1528, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1087 p = 1 := by simpa only [d1528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1475 p hg
    simpa only [d1528, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1655 (p : Pattern) (guard : d1529 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1527 p = 1 := by simpa only [d1529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1653 p hg
    simpa only [d1529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1528 p = 1 := by simpa only [d1529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1654 p hg
    simpa only [d1529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1656 (p : Pattern) (guard : d1530 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1201 p = 1 := by simpa only [d1530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1643 p hg
    simpa only [d1530, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1529 p = 1 := by simpa only [d1530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1655 p hg
    simpa only [d1530, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1657 (p : Pattern) (guard : d1203 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1156 p hg
    simpa only [d1203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d826 p = 1 := by simpa only [d1203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1480 p hg
    simpa only [d1203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1658 (p : Pattern) (guard : d1204 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 223 with
  | false =>
    have hg : d1203 p = 1 := by simpa only [d1204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1657 p hg
    simpa only [d1204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1156 p hg
    simpa only [d1204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1659 (p : Pattern) (guard : d1205 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1204 p = 1 := by simpa only [d1205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1658 p hg
    simpa only [d1205, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1156 p hg
    simpa only [d1205, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1660 (p : Pattern) (guard : d1531 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1519 p = 1 := by simpa only [d1531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1645 p hg
    simpa only [d1531, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1156 p hg
    simpa only [d1531, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1661 (p : Pattern) (guard : d1532 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1520 p = 1 := by simpa only [d1532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1646 p hg
    simpa only [d1532, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1531 p = 1 := by simpa only [d1532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1660 p hg
    simpa only [d1532, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1662 (p : Pattern) (guard : d1533 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 224 with
  | false =>
    have hg : d826 p = 1 := by simpa only [d1533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1480 p hg
    simpa only [d1533, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1532 p = 1 := by simpa only [d1533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1661 p hg
    simpa only [d1533, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1663 (p : Pattern) (guard : d1534 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 223 with
  | false =>
    have hg : d1533 p = 1 := by simpa only [d1534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1662 p hg
    simpa only [d1534, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1156 p hg
    simpa only [d1534, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1664 (p : Pattern) (guard : d1535 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1534 p = 1 := by simpa only [d1535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1663 p hg
    simpa only [d1535, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1156 p hg
    simpa only [d1535, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1665 (p : Pattern) (guard : d1536 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1205 p = 1 := by simpa only [d1536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1659 p hg
    simpa only [d1536, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1535 p = 1 := by simpa only [d1536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1664 p hg
    simpa only [d1536, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1666 (p : Pattern) (guard : d1537 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1530 p = 1 := by simpa only [d1537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1656 p hg
    simpa only [d1537, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1536 p = 1 := by simpa only [d1537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1665 p hg
    simpa only [d1537, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1667 (p : Pattern) (guard : d1538 p = 1) : d47619 p ≤ (-1 : Int) + d47708 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1537 p = 1 := by simpa only [d1538, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1666 p hg
    simpa only [d1538, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1538, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1164 p hg
    simpa only [d1538, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1668 (p : Pattern) (guard : d1539 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1521 p = 1 := by simpa only [d1539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1647 p hg
    simpa only [d1539, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1532 p = 1 := by simpa only [d1539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1661 p hg
    simpa only [d1539, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1669 (p : Pattern) (guard : d1540 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1519 p = 1 := by simpa only [d1540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1645 p hg
    simpa only [d1540, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15 p = 1 := by simpa only [d1540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1155 p hg
    simpa only [d1540, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1670 (p : Pattern) (guard : d1541 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1540 p = 1 := by simpa only [d1541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1669 p hg
    simpa only [d1541, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1156 p hg
    simpa only [d1541, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1671 (p : Pattern) (guard : d1542 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1525 p = 1 := by simpa only [d1542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1651 p hg
    simpa only [d1542, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1541 p = 1 := by simpa only [d1542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1670 p hg
    simpa only [d1542, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1672 (p : Pattern) (guard : d1543 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 223 with
  | false =>
    have hg : d1539 p = 1 := by simpa only [d1543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1668 p hg
    simpa only [d1543, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1542 p = 1 := by simpa only [d1543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1671 p hg
    simpa only [d1543, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1673 (p : Pattern) (guard : d1544 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1156 p hg
    simpa only [d1544, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1093 p = 1 := by simpa only [d1544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1487 p hg
    simpa only [d1544, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1674 (p : Pattern) (guard : d1545 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1543 p = 1 := by simpa only [d1545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1672 p hg
    simpa only [d1545, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1544 p = 1 := by simpa only [d1545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1673 p hg
    simpa only [d1545, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1675 (p : Pattern) (guard : d1546 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1529 p = 1 := by simpa only [d1546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1655 p hg
    simpa only [d1546, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1545 p = 1 := by simpa only [d1546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1674 p hg
    simpa only [d1546, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1676 (p : Pattern) (guard : d1547 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1531 p = 1 := by simpa only [d1547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1660 p hg
    simpa only [d1547, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1156 p hg
    simpa only [d1547, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1677 (p : Pattern) (guard : d1548 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1532 p = 1 := by simpa only [d1548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1661 p hg
    simpa only [d1548, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1547 p = 1 := by simpa only [d1548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1676 p hg
    simpa only [d1548, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1678 (p : Pattern) (guard : d1549 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 223 with
  | false =>
    have hg : d1548 p = 1 := by simpa only [d1549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1677 p hg
    simpa only [d1549, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1156 p hg
    simpa only [d1549, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1679 (p : Pattern) (guard : d1550 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1549 p = 1 := by simpa only [d1550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1678 p hg
    simpa only [d1550, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1156 p hg
    simpa only [d1550, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1680 (p : Pattern) (guard : d1551 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1535 p = 1 := by simpa only [d1551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1664 p hg
    simpa only [d1551, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1550 p = 1 := by simpa only [d1551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1679 p hg
    simpa only [d1551, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1681 (p : Pattern) (guard : d1552 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1546 p = 1 := by simpa only [d1552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1675 p hg
    simpa only [d1552, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1551 p = 1 := by simpa only [d1552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1680 p hg
    simpa only [d1552, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1682 (p : Pattern) (guard : d1553 p = 1) : d47619 p ≤ (-1 : Int) + d47708 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1552 p = 1 := by simpa only [d1553, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1681 p hg
    simpa only [d1553, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1553, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1164 p hg
    simpa only [d1553, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1683 (p : Pattern) (guard : d1554 p = 1) : d47619 p ≤ (-1 : Int) + d47708 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1538 p = 1 := by simpa only [d1554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1667 p hg
    simpa only [d1554, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d1554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1682 p hg
    simpa only [d1554, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1684 (p : Pattern) (guard : d1555 p = 1) : d47797 p ≤ (-1 : Int) + d47733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1554 p = 1 := by simpa only [d1555, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1683 p hg
    simpa only [d1555, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1555, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1168 p hg
    simpa only [d1555, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1685 (p : Pattern) (guard : d1858 p = 1) : d47798 p ≤ (-1 : Int) + d47734 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1857 p = 1 := by simpa only [d1858, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1640 p hg
    simpa only [d1858, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1555 p = 1 := by simpa only [d1858, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1684 p hg
    simpa only [d1858, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1686 (p : Pattern) (guard : d18134 p = 1) : d47799 p ≤ (-1 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1858 p = 1 := by simpa only [d18134, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1685 p hg
    simpa only [d18134, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d18134, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1171 p hg
    simpa only [d18134, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1687 (p : Pattern) (guard : d18135 p = 1) : d47803 p ≤ (-1 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d18134 p = 1 := by simpa only [d18135, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1686 p hg
    simpa only [d18135, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d18135, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1173 p hg
    simpa only [d18135, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1688 (p : Pattern) (guard : d1559 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1541 p = 1 := by simpa only [d1559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1626 p hg
    simpa only [d1559, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1140 p hg
    simpa only [d1559, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1689 (p : Pattern) (guard : d1560 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 223 with
  | false =>
    have hg : d1548 p = 1 := by simpa only [d1560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1633 p hg
    simpa only [d1560, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1559 p = 1 := by simpa only [d1560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1688 p hg
    simpa only [d1560, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1690 (p : Pattern) (guard : d1561 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1560 p = 1 := by simpa only [d1561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1689 p hg
    simpa only [d1561, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1115 p = 1 := by simpa only [d1561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1516 p hg
    simpa only [d1561, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1691 (p : Pattern) (guard : d1562 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1545 p = 1 := by simpa only [d1562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1630 p hg
    simpa only [d1562, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1561 p = 1 := by simpa only [d1562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1690 p hg
    simpa only [d1562, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1692 (p : Pattern) (guard : d1563 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1547 p = 1 := by simpa only [d1563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1632 p hg
    simpa only [d1563, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1140 p hg
    simpa only [d1563, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1693 (p : Pattern) (guard : d1564 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 223 with
  | false =>
    have hg : d1563 p = 1 := by simpa only [d1564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1692 p hg
    simpa only [d1564, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1140 p hg
    simpa only [d1564, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1694 (p : Pattern) (guard : d1565 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1564 p = 1 := by simpa only [d1565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1693 p hg
    simpa only [d1565, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1140 p hg
    simpa only [d1565, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1695 (p : Pattern) (guard : d1566 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1550 p = 1 := by simpa only [d1566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1635 p hg
    simpa only [d1566, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1565 p = 1 := by simpa only [d1566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1694 p hg
    simpa only [d1566, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1696 (p : Pattern) (guard : d1567 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1562 p = 1 := by simpa only [d1567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1691 p hg
    simpa only [d1567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1566 p = 1 := by simpa only [d1567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1695 p hg
    simpa only [d1567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1697 (p : Pattern) (guard : d1568 p = 1) : d47652 p ≤ (-1 : Int) + d47731 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1567 p = 1 := by simpa only [d1568, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1696 p hg
    simpa only [d1568, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1568, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1148 p hg
    simpa only [d1568, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1698 (p : Pattern) (guard : d1569 p = 1) : d47652 p ≤ (-1 : Int) + d47731 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d1569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1638 p hg
    simpa only [d1569, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1568 p = 1 := by simpa only [d1569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1697 p hg
    simpa only [d1569, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1699 (p : Pattern) (guard : d1862 p = 1) : d47652 p ≤ (-1 : Int) + d47732 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1862, d47732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1136 p hg
    simpa only [d1862, d47732, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1569 p = 1 := by simpa only [d1862, d47732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1698 p hg
    simpa only [d1862, d47732, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1700 (p : Pattern) (guard : d1559 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1541 p = 1 := by simpa only [d1559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1670 p hg
    simpa only [d1559, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1156 p hg
    simpa only [d1559, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1701 (p : Pattern) (guard : d1560 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 223 with
  | false =>
    have hg : d1548 p = 1 := by simpa only [d1560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1677 p hg
    simpa only [d1560, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1559 p = 1 := by simpa only [d1560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1700 p hg
    simpa only [d1560, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1702 (p : Pattern) (guard : d1561 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1560 p = 1 := by simpa only [d1561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1701 p hg
    simpa only [d1561, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1115 p = 1 := by simpa only [d1561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1523 p hg
    simpa only [d1561, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1703 (p : Pattern) (guard : d1562 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1545 p = 1 := by simpa only [d1562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1674 p hg
    simpa only [d1562, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1561 p = 1 := by simpa only [d1562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1702 p hg
    simpa only [d1562, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1704 (p : Pattern) (guard : d1563 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1547 p = 1 := by simpa only [d1563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1676 p hg
    simpa only [d1563, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1156 p hg
    simpa only [d1563, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1705 (p : Pattern) (guard : d1564 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 223 with
  | false =>
    have hg : d1563 p = 1 := by simpa only [d1564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1704 p hg
    simpa only [d1564, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1156 p hg
    simpa only [d1564, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1706 (p : Pattern) (guard : d1565 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1564 p = 1 := by simpa only [d1565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1705 p hg
    simpa only [d1565, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1156 p hg
    simpa only [d1565, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1707 (p : Pattern) (guard : d1566 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1550 p = 1 := by simpa only [d1566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1679 p hg
    simpa only [d1566, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1565 p = 1 := by simpa only [d1566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1706 p hg
    simpa only [d1566, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1708 (p : Pattern) (guard : d1567 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1562 p = 1 := by simpa only [d1567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1703 p hg
    simpa only [d1567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1566 p = 1 := by simpa only [d1567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1707 p hg
    simpa only [d1567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1709 (p : Pattern) (guard : d1568 p = 1) : d47619 p ≤ (-1 : Int) + d47708 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1567 p = 1 := by simpa only [d1568, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1708 p hg
    simpa only [d1568, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1568, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1164 p hg
    simpa only [d1568, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1710 (p : Pattern) (guard : d1569 p = 1) : d47619 p ≤ (-1 : Int) + d47708 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d1569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1682 p hg
    simpa only [d1569, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1568 p = 1 := by simpa only [d1569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1709 p hg
    simpa only [d1569, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1711 (p : Pattern) (guard : d1570 p = 1) : d47797 p ≤ (-1 : Int) + d47733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1569 p = 1 := by simpa only [d1570, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1710 p hg
    simpa only [d1570, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1570, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1168 p hg
    simpa only [d1570, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1712 (p : Pattern) (guard : d1863 p = 1) : d47798 p ≤ (-1 : Int) + d47734 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1862 p = 1 := by simpa only [d1863, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1699 p hg
    simpa only [d1863, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1570 p = 1 := by simpa only [d1863, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1711 p hg
    simpa only [d1863, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1713 (p : Pattern) (guard : d18155 p = 1) : d47799 p ≤ (-1 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1863 p = 1 := by simpa only [d18155, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1712 p hg
    simpa only [d18155, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d18155, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1171 p hg
    simpa only [d18155, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1714 (p : Pattern) (guard : d18156 p = 1) : d47803 p ≤ (-1 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d18155 p = 1 := by simpa only [d18156, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1713 p hg
    simpa only [d18156, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d18156, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1173 p hg
    simpa only [d18156, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1715 (p : Pattern) (guard : d60776 p = 1) : d47803 p ≤ (-1 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d18135 p = 1 := by simpa only [d60776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1687 p hg
    simpa only [d60776, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d18156 p = 1 := by simpa only [d60776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1714 p hg
    simpa only [d60776, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1716 (p : Pattern) (guard : d1575 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1140 p hg
    simpa only [d1575, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1559 p = 1 := by simpa only [d1575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1688 p hg
    simpa only [d1575, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1717 (p : Pattern) (guard : d1576 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1575 p = 1 := by simpa only [d1576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1716 p hg
    simpa only [d1576, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1115 p = 1 := by simpa only [d1576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1516 p hg
    simpa only [d1576, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1718 (p : Pattern) (guard : d1577 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1576 p = 1 := by simpa only [d1577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1717 p hg
    simpa only [d1577, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1565 p = 1 := by simpa only [d1577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1694 p hg
    simpa only [d1577, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1719 (p : Pattern) (guard : d1578 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1565 p = 1 := by simpa only [d1578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1694 p hg
    simpa only [d1578, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1140 p hg
    simpa only [d1578, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1720 (p : Pattern) (guard : d1579 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1577 p = 1 := by simpa only [d1579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1718 p hg
    simpa only [d1579, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1578 p = 1 := by simpa only [d1579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1719 p hg
    simpa only [d1579, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1721 (p : Pattern) (guard : d1580 p = 1) : d47652 p ≤ (-1 : Int) + d47731 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1579 p = 1 := by simpa only [d1580, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1720 p hg
    simpa only [d1580, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1580, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1148 p hg
    simpa only [d1580, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1722 (p : Pattern) (guard : d1581 p = 1) : d47652 p ≤ (-1 : Int) + d47731 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1568 p = 1 := by simpa only [d1581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1697 p hg
    simpa only [d1581, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1580 p = 1 := by simpa only [d1581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1721 p hg
    simpa only [d1581, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1723 (p : Pattern) (guard : d1868 p = 1) : d47652 p ≤ (-1 : Int) + d47732 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1868, d47732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1136 p hg
    simpa only [d1868, d47732, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1581 p = 1 := by simpa only [d1868, d47732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1722 p hg
    simpa only [d1868, d47732, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1724 (p : Pattern) (guard : d1575 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1156 p hg
    simpa only [d1575, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1559 p = 1 := by simpa only [d1575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1700 p hg
    simpa only [d1575, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1725 (p : Pattern) (guard : d1576 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1575 p = 1 := by simpa only [d1576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d1576, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1115 p = 1 := by simpa only [d1576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1523 p hg
    simpa only [d1576, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1726 (p : Pattern) (guard : d1577 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1576 p = 1 := by simpa only [d1577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1725 p hg
    simpa only [d1577, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1565 p = 1 := by simpa only [d1577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1706 p hg
    simpa only [d1577, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1727 (p : Pattern) (guard : d1578 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1565 p = 1 := by simpa only [d1578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1706 p hg
    simpa only [d1578, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1156 p hg
    simpa only [d1578, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1728 (p : Pattern) (guard : d1579 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1577 p = 1 := by simpa only [d1579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1726 p hg
    simpa only [d1579, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1578 p = 1 := by simpa only [d1579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1727 p hg
    simpa only [d1579, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1729 (p : Pattern) (guard : d1580 p = 1) : d47619 p ≤ (-1 : Int) + d47708 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1579 p = 1 := by simpa only [d1580, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1728 p hg
    simpa only [d1580, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1580, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1164 p hg
    simpa only [d1580, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1730 (p : Pattern) (guard : d1581 p = 1) : d47619 p ≤ (-1 : Int) + d47708 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1568 p = 1 := by simpa only [d1581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1709 p hg
    simpa only [d1581, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1580 p = 1 := by simpa only [d1581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1729 p hg
    simpa only [d1581, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1731 (p : Pattern) (guard : d1582 p = 1) : d47797 p ≤ (-1 : Int) + d47733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1581 p = 1 := by simpa only [d1582, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1730 p hg
    simpa only [d1582, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1582, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1168 p hg
    simpa only [d1582, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1732 (p : Pattern) (guard : d1869 p = 1) : d47798 p ≤ (-1 : Int) + d47734 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1868 p = 1 := by simpa only [d1869, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1723 p hg
    simpa only [d1869, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1582 p = 1 := by simpa only [d1869, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1731 p hg
    simpa only [d1869, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1733 (p : Pattern) (guard : d18188 p = 1) : d47799 p ≤ (-1 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1869 p = 1 := by simpa only [d18188, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1732 p hg
    simpa only [d18188, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d18188, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1171 p hg
    simpa only [d18188, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1734 (p : Pattern) (guard : d18189 p = 1) : d47803 p ≤ (-1 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d18188 p = 1 := by simpa only [d18189, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1733 p hg
    simpa only [d18189, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d18189, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1173 p hg
    simpa only [d18189, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1735 (p : Pattern) (guard : d60778 p = 1) : d47803 p ≤ (-1 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d18156 p = 1 := by simpa only [d60778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1714 p hg
    simpa only [d60778, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d18189 p = 1 := by simpa only [d60778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1734 p hg
    simpa only [d60778, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1736 (p : Pattern) (guard : d60779 p = 1) : d47803 p ≤ (-1 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d60776 p = 1 := by simpa only [d60779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1715 p hg
    simpa only [d60779, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60778 p = 1 := by simpa only [d60779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1735 p hg
    simpa only [d60779, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1737 (p : Pattern) (guard : d18190 p = 1) : d47803 p ≤ (-1 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d18189 p = 1 := by simpa only [d18190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1734 p hg
    simpa only [d18190, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d18190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1175 p hg
    simpa only [d18190, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1738 (p : Pattern) (guard : d60783 p = 1) : d47803 p ≤ (-1 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d60778 p = 1 := by simpa only [d60783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1735 p hg
    simpa only [d60783, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d18190 p = 1 := by simpa only [d60783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1737 p hg
    simpa only [d60783, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1739 (p : Pattern) (guard : d60784 p = 1) : d47803 p ≤ (-1 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d60779 p = 1 := by simpa only [d60784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1736 p hg
    simpa only [d60784, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60783 p = 1 := by simpa only [d60784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1738 p hg
    simpa only [d60784, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1740 (p : Pattern) (guard : d60785 p = 1) : d47804 p ≤ (-1 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60785, d47804, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1135 p hg
    simpa only [d60785, d47804, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60784 p = 1 := by simpa only [d60785, d47804, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1739 p hg
    simpa only [d60785, d47804, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1741 (p : Pattern) (guard : d60786 p = 1) : d47805 p ≤ (-1 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60786, d47805, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1134 p hg
    simpa only [d60786, d47805, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60785 p = 1 := by simpa only [d60786, d47805, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1740 p hg
    simpa only [d60786, d47805, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1742 (p : Pattern) (guard : d1593 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1576 p = 1 := by simpa only [d1593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1717 p hg
    simpa only [d1593, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1140 p hg
    simpa only [d1593, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1743 (p : Pattern) (guard : d1594 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1593 p = 1 := by simpa only [d1594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1742 p hg
    simpa only [d1594, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1140 p hg
    simpa only [d1594, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1744 (p : Pattern) (guard : d1595 p = 1) : d47652 p ≤ (-1 : Int) + d47731 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1594 p = 1 := by simpa only [d1595, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1743 p hg
    simpa only [d1595, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1595, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1148 p hg
    simpa only [d1595, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1745 (p : Pattern) (guard : d1596 p = 1) : d47652 p ≤ (-1 : Int) + d47731 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1595 p = 1 := by simpa only [d1596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1744 p hg
    simpa only [d1596, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1150 p hg
    simpa only [d1596, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1746 (p : Pattern) (guard : d1883 p = 1) : d47652 p ≤ (-1 : Int) + d47732 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1883, d47732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1136 p hg
    simpa only [d1883, d47732, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1596 p = 1 := by simpa only [d1883, d47732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1745 p hg
    simpa only [d1883, d47732, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1747 (p : Pattern) (guard : d1593 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1576 p = 1 := by simpa only [d1593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1725 p hg
    simpa only [d1593, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1156 p hg
    simpa only [d1593, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1748 (p : Pattern) (guard : d1594 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1593 p = 1 := by simpa only [d1594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1747 p hg
    simpa only [d1594, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1156 p hg
    simpa only [d1594, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1749 (p : Pattern) (guard : d1595 p = 1) : d47619 p ≤ (-1 : Int) + d47708 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1594 p = 1 := by simpa only [d1595, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1748 p hg
    simpa only [d1595, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1595, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1164 p hg
    simpa only [d1595, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
