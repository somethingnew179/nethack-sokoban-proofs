/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Comparisons010
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare1540 (p : Pattern) (guard : d0 p = 1) : d169 p ≤ (0 : Int) + d130 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1541 (p : Pattern) (guard : d868 p = 1) : d224 p ≤ (0 : Int) + d252 p := by
  cases selected : p 112 with
  | false =>
    have hg : d866 p = 1 := by simpa only [d868, d224, d252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1539 p hg
    simpa only [d868, d224, d252, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d868, d224, d252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1540 p hg
    simpa only [d868, d224, d252, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1542 (p : Pattern) (guard : d868 p = 1) : d225 p ≤ (0 : Int) + d253 p := by
  cases selected : p 106 with
  | false =>
    have hg : d868 p = 1 := by simpa only [d225, d253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1537 p hg
    simpa only [d225, d253, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d868 p = 1 := by simpa only [d225, d253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1541 p hg
    simpa only [d225, d253, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1543 (p : Pattern) (guard : d868 p = 1) : d226 p ≤ (0 : Int) + d254 p := by
  cases selected : p 86 with
  | false =>
    have hg : d868 p = 1 := by simpa only [d226, d254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1533 p hg
    simpa only [d226, d254, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d868 p = 1 := by simpa only [d226, d254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1542 p hg
    simpa only [d226, d254, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1544 (p : Pattern) (guard : d868 p = 1) : d227 p ≤ (0 : Int) + d255 p := by
  cases selected : p 80 with
  | false =>
    have hg : d868 p = 1 := by simpa only [d227, d255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1528 p hg
    simpa only [d227, d255, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d868 p = 1 := by simpa only [d227, d255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1543 p hg
    simpa only [d227, d255, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1545 (p : Pattern) (guard : d865 p = 1) : d45 p ≤ (1 : Int) + d45 p := by
  omega
theorem compare1546 (p : Pattern) (guard : d0 p = 1) : d152 p ≤ (1 : Int) + d51 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1547 (p : Pattern) (guard : d1073 p = 1) : d184 p ≤ (1 : Int) + d1074 p := by
  cases selected : p 112 with
  | false =>
    have hg : d865 p = 1 := by simpa only [d1073, d184, d1074, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1545 p hg
    simpa only [d1073, d184, d1074, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1073, d184, d1074, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1546 p hg
    simpa only [d1073, d184, d1074, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1548 (p : Pattern) (guard : d0 p = 1) : d74 p ≤ (1 : Int) + d74 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1549 (p : Pattern) (guard : d865 p = 1) : d78 p ≤ (1 : Int) + d74 p := by
  cases selected : p 113 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d865, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1548 p hg
    simpa only [d865, d78, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d865, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1402 p hg
    simpa only [d865, d78, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1550 (p : Pattern) (guard : d0 p = 1) : d155 p ≤ (1 : Int) + d80 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1551 (p : Pattern) (guard : d1073 p = 1) : d185 p ≤ (1 : Int) + d1075 p := by
  cases selected : p 112 with
  | false =>
    have hg : d865 p = 1 := by simpa only [d1073, d185, d1075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1549 p hg
    simpa only [d1073, d185, d1075, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1073, d185, d1075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1550 p hg
    simpa only [d1073, d185, d1075, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1552 (p : Pattern) (guard : d1073 p = 1) : d186 p ≤ (1 : Int) + d1076 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1073 p = 1 := by simpa only [d186, d1076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1547 p hg
    simpa only [d186, d1076, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1073 p = 1 := by simpa only [d186, d1076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1551 p hg
    simpa only [d186, d1076, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1553 (p : Pattern) (guard : d0 p = 1) : d45 p ≤ (1 : Int) + d45 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1554 (p : Pattern) (guard : d865 p = 1) : d197 p ≤ (1 : Int) + d45 p := by
  cases selected : p 113 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d865, d197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1553 p hg
    simpa only [d865, d197, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d865, d197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1397 p hg
    simpa only [d865, d197, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1555 (p : Pattern) (guard : d0 p = 1) : d155 p ≤ (1 : Int) + d102 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1556 (p : Pattern) (guard : d1073 p = 1) : d198 p ≤ (1 : Int) + d1077 p := by
  cases selected : p 112 with
  | false =>
    have hg : d865 p = 1 := by simpa only [d1073, d198, d1077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1554 p hg
    simpa only [d1073, d198, d1077, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1073, d198, d1077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1555 p hg
    simpa only [d1073, d198, d1077, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1557 (p : Pattern) (guard : d0 p = 1) : d77 p ≤ (1 : Int) + d77 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1558 (p : Pattern) (guard : d865 p = 1) : d204 p ≤ (1 : Int) + d77 p := by
  cases selected : p 113 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d865, d204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1557 p hg
    simpa only [d865, d204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d865, d204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1409 p hg
    simpa only [d865, d204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1559 (p : Pattern) (guard : d0 p = 1) : d164 p ≤ (1 : Int) + d108 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1560 (p : Pattern) (guard : d1073 p = 1) : d205 p ≤ (1 : Int) + d1078 p := by
  cases selected : p 112 with
  | false =>
    have hg : d865 p = 1 := by simpa only [d1073, d205, d1078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1558 p hg
    simpa only [d1073, d205, d1078, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1073, d205, d1078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1559 p hg
    simpa only [d1073, d205, d1078, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1561 (p : Pattern) (guard : d1073 p = 1) : d206 p ≤ (1 : Int) + d1079 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1073 p = 1 := by simpa only [d206, d1079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1556 p hg
    simpa only [d206, d1079, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1073 p = 1 := by simpa only [d206, d1079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1560 p hg
    simpa only [d206, d1079, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1562 (p : Pattern) (guard : d1073 p = 1) : d207 p ≤ (1 : Int) + d1080 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1073 p = 1 := by simpa only [d207, d1080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1552 p hg
    simpa only [d207, d1080, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1073 p = 1 := by simpa only [d207, d1080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1561 p hg
    simpa only [d207, d1080, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1563 (p : Pattern) (guard : d0 p = 1) : d155 p ≤ (1 : Int) + d51 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1564 (p : Pattern) (guard : d1073 p = 1) : d208 p ≤ (1 : Int) + d1074 p := by
  cases selected : p 112 with
  | false =>
    have hg : d865 p = 1 := by simpa only [d1073, d208, d1074, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1545 p hg
    simpa only [d1073, d208, d1074, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1073, d208, d1074, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1563 p hg
    simpa only [d1073, d208, d1074, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1565 (p : Pattern) (guard : d865 p = 1) : d77 p ≤ (1 : Int) + d77 p := by
  omega
theorem compare1566 (p : Pattern) (guard : d0 p = 1) : d164 p ≤ (1 : Int) + d80 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1567 (p : Pattern) (guard : d1073 p = 1) : d209 p ≤ (1 : Int) + d1081 p := by
  cases selected : p 112 with
  | false =>
    have hg : d865 p = 1 := by simpa only [d1073, d209, d1081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1565 p hg
    simpa only [d1073, d209, d1081, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1073, d209, d1081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1566 p hg
    simpa only [d1073, d209, d1081, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1568 (p : Pattern) (guard : d1073 p = 1) : d210 p ≤ (1 : Int) + d1082 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1073 p = 1 := by simpa only [d210, d1082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1564 p hg
    simpa only [d210, d1082, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1073 p = 1 := by simpa only [d210, d1082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1567 p hg
    simpa only [d210, d1082, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1569 (p : Pattern) (guard : d865 p = 1) : d215 p ≤ (1 : Int) + d45 p := by
  cases selected : p 113 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d865, d215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1553 p hg
    simpa only [d865, d215, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d865, d215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1419 p hg
    simpa only [d865, d215, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1570 (p : Pattern) (guard : d0 p = 1) : d164 p ≤ (1 : Int) + d102 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1571 (p : Pattern) (guard : d1073 p = 1) : d216 p ≤ (1 : Int) + d1077 p := by
  cases selected : p 112 with
  | false =>
    have hg : d865 p = 1 := by simpa only [d1073, d216, d1077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1569 p hg
    simpa only [d1073, d216, d1077, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1073, d216, d1077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1570 p hg
    simpa only [d1073, d216, d1077, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1572 (p : Pattern) (guard : d865 p = 1) : d223 p ≤ (1 : Int) + d77 p := by
  cases selected : p 113 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d865, d223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1557 p hg
    simpa only [d865, d223, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d865, d223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1430 p hg
    simpa only [d865, d223, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1573 (p : Pattern) (guard : d0 p = 1) : d169 p ≤ (1 : Int) + d112 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1574 (p : Pattern) (guard : d1073 p = 1) : d224 p ≤ (1 : Int) + d1083 p := by
  cases selected : p 112 with
  | false =>
    have hg : d865 p = 1 := by simpa only [d1073, d224, d1083, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1572 p hg
    simpa only [d1073, d224, d1083, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1073, d224, d1083, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1573 p hg
    simpa only [d1073, d224, d1083, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1575 (p : Pattern) (guard : d1073 p = 1) : d225 p ≤ (1 : Int) + d1084 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1073 p = 1 := by simpa only [d225, d1084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1571 p hg
    simpa only [d225, d1084, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1073 p = 1 := by simpa only [d225, d1084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1574 p hg
    simpa only [d225, d1084, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1576 (p : Pattern) (guard : d1073 p = 1) : d226 p ≤ (1 : Int) + d1085 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1073 p = 1 := by simpa only [d226, d1085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1568 p hg
    simpa only [d226, d1085, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1073 p = 1 := by simpa only [d226, d1085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1575 p hg
    simpa only [d226, d1085, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1577 (p : Pattern) (guard : d1073 p = 1) : d227 p ≤ (1 : Int) + d1086 p := by
  cases selected : p 80 with
  | false =>
    have hg : d1073 p = 1 := by simpa only [d227, d1086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1562 p hg
    simpa only [d227, d1086, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1073 p = 1 := by simpa only [d227, d1086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1576 p hg
    simpa only [d227, d1086, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1578 (p : Pattern) (guard : d0 p = 1) : d8 p ≤ (0 : Int) + d135 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1579 (p : Pattern) (guard : d1088 p = 1) : d8 p ≤ (0 : Int) + d456 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1088, d456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare199 p hg
    simpa only [d1088, d456, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1088, d456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1578 p hg
    simpa only [d1088, d456, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1580 (p : Pattern) (guard : d0 p = 1) : d14 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1581 (p : Pattern) (guard : d1088 p = 1) : d15 p ≤ (0 : Int) + d52 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1088, d15, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare199 p hg
    simpa only [d1088, d15, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1088, d15, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1580 p hg
    simpa only [d1088, d15, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1582 (p : Pattern) (guard : d1088 p = 1) : d16 p ≤ (0 : Int) + d457 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d16, d457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1579 p hg
    simpa only [d16, d457, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d16, d457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1581 p hg
    simpa only [d16, d457, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1583 (p : Pattern) (guard : d0 p = 1) : d8 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1584 (p : Pattern) (guard : d1088 p = 1) : d8 p ≤ (0 : Int) + d52 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1088, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare199 p hg
    simpa only [d1088, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1088, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1583 p hg
    simpa only [d1088, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1585 (p : Pattern) (guard : d1088 p = 1) : d16 p ≤ (0 : Int) + d52 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1584 p hg
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1581 p hg
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1586 (p : Pattern) (guard : d1088 p = 1) : d16 p ≤ (0 : Int) + d458 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1582 p hg
    simpa only [d458, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1585 p hg
    simpa only [d458, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1587 (p : Pattern) (guard : d0 p = 1) : d8 p ≤ (0 : Int) + d138 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1588 (p : Pattern) (guard : d1088 p = 1) : d8 p ≤ (0 : Int) + d459 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1088, d459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare199 p hg
    simpa only [d1088, d459, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1088, d459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1587 p hg
    simpa only [d1088, d459, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1589 (p : Pattern) (guard : d1088 p = 1) : d16 p ≤ (0 : Int) + d460 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d16, d460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1588 p hg
    simpa only [d16, d460, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d16, d460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1581 p hg
    simpa only [d16, d460, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1590 (p : Pattern) (guard : d0 p = 1) : d20 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1591 (p : Pattern) (guard : d1088 p = 1) : d20 p ≤ (0 : Int) + d54 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1088, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare211 p hg
    simpa only [d1088, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1088, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1590 p hg
    simpa only [d1088, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1592 (p : Pattern) (guard : d0 p = 1) : d24 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1593 (p : Pattern) (guard : d1088 p = 1) : d25 p ≤ (0 : Int) + d54 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1088, d25, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare211 p hg
    simpa only [d1088, d25, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1088, d25, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1592 p hg
    simpa only [d1088, d25, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1594 (p : Pattern) (guard : d1088 p = 1) : d26 p ≤ (0 : Int) + d54 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1591 p hg
    simpa only [d26, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1593 p hg
    simpa only [d26, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1595 (p : Pattern) (guard : d1088 p = 1) : d27 p ≤ (0 : Int) + d461 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d27, d461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1589 p hg
    simpa only [d27, d461, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d27, d461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1594 p hg
    simpa only [d27, d461, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1596 (p : Pattern) (guard : d1088 p = 1) : d28 p ≤ (0 : Int) + d462 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d28, d462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1586 p hg
    simpa only [d28, d462, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d28, d462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1595 p hg
    simpa only [d28, d462, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1597 (p : Pattern) (guard : d0 p = 1) : d33 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1598 (p : Pattern) (guard : d1088 p = 1) : d33 p ≤ (0 : Int) + d58 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1088, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare221 p hg
    simpa only [d1088, d58, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1088, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1597 p hg
    simpa only [d1088, d58, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1599 (p : Pattern) (guard : d1088 p = 1) : d34 p ≤ (0 : Int) + d58 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1088, d34, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare221 p hg
    simpa only [d1088, d34, d58, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1088, d34, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1592 p hg
    simpa only [d1088, d34, d58, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1600 (p : Pattern) (guard : d1088 p = 1) : d35 p ≤ (0 : Int) + d58 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1598 p hg
    simpa only [d35, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1599 p hg
    simpa only [d35, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1601 (p : Pattern) (guard : d1088 p = 1) : d36 p ≤ (0 : Int) + d463 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d36, d463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1582 p hg
    simpa only [d36, d463, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d36, d463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1600 p hg
    simpa only [d36, d463, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1602 (p : Pattern) (guard : d0 p = 1) : d38 p ≤ (0 : Int) + d138 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1603 (p : Pattern) (guard : d1088 p = 1) : d38 p ≤ (0 : Int) + d464 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1088, d464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare232 p hg
    simpa only [d1088, d464, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1088, d464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1602 p hg
    simpa only [d1088, d464, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1604 (p : Pattern) (guard : d0 p = 1) : d40 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1605 (p : Pattern) (guard : d1088 p = 1) : d41 p ≤ (0 : Int) + d61 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1088, d41, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare232 p hg
    simpa only [d1088, d41, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1088, d41, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1604 p hg
    simpa only [d1088, d41, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1606 (p : Pattern) (guard : d1088 p = 1) : d42 p ≤ (0 : Int) + d465 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d42, d465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1603 p hg
    simpa only [d42, d465, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d42, d465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1605 p hg
    simpa only [d42, d465, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1607 (p : Pattern) (guard : d1088 p = 1) : d43 p ≤ (0 : Int) + d466 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d43, d466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1606 p hg
    simpa only [d43, d466, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d43, d466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1594 p hg
    simpa only [d43, d466, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1608 (p : Pattern) (guard : d1088 p = 1) : d44 p ≤ (0 : Int) + d467 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d44, d467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1601 p hg
    simpa only [d44, d467, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d44, d467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1607 p hg
    simpa only [d44, d467, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1609 (p : Pattern) (guard : d1088 p = 1) : d45 p ≤ (0 : Int) + d468 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d45, d468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1596 p hg
    simpa only [d45, d468, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d45, d468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1608 p hg
    simpa only [d45, d468, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1610 (p : Pattern) (guard : d0 p = 1) : d15 p ≤ (0 : Int) + d52 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1611 (p : Pattern) (guard : d1092 p = 1) : d16 p ≤ (0 : Int) + d457 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1092, d16, d457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1579 p hg
    simpa only [d1092, d16, d457, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d16, d457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1610 p hg
    simpa only [d1092, d16, d457, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1612 (p : Pattern) (guard : d1092 p = 1) : d16 p ≤ (0 : Int) + d52 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1092, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1584 p hg
    simpa only [d1092, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1610 p hg
    simpa only [d1092, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1613 (p : Pattern) (guard : d1092 p = 1) : d16 p ≤ (0 : Int) + d458 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1611 p hg
    simpa only [d458, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1612 p hg
    simpa only [d458, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1614 (p : Pattern) (guard : d1092 p = 1) : d16 p ≤ (0 : Int) + d460 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1092, d16, d460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1588 p hg
    simpa only [d1092, d16, d460, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d16, d460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1610 p hg
    simpa only [d1092, d16, d460, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1615 (p : Pattern) (guard : d0 p = 1) : d25 p ≤ (0 : Int) + d54 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1616 (p : Pattern) (guard : d1092 p = 1) : d26 p ≤ (0 : Int) + d54 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1092, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1591 p hg
    simpa only [d1092, d26, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1615 p hg
    simpa only [d1092, d26, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1617 (p : Pattern) (guard : d1092 p = 1) : d27 p ≤ (0 : Int) + d461 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d27, d461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1614 p hg
    simpa only [d27, d461, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d27, d461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1616 p hg
    simpa only [d27, d461, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1618 (p : Pattern) (guard : d1092 p = 1) : d28 p ≤ (0 : Int) + d462 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d28, d462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1613 p hg
    simpa only [d28, d462, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d28, d462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1617 p hg
    simpa only [d28, d462, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1619 (p : Pattern) (guard : d0 p = 1) : d34 p ≤ (0 : Int) + d58 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1620 (p : Pattern) (guard : d1092 p = 1) : d35 p ≤ (0 : Int) + d58 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1092, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1598 p hg
    simpa only [d1092, d35, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1619 p hg
    simpa only [d1092, d35, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1621 (p : Pattern) (guard : d1092 p = 1) : d36 p ≤ (0 : Int) + d463 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d36, d463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1611 p hg
    simpa only [d36, d463, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d36, d463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1620 p hg
    simpa only [d36, d463, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1622 (p : Pattern) (guard : d0 p = 1) : d41 p ≤ (0 : Int) + d61 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1623 (p : Pattern) (guard : d1092 p = 1) : d42 p ≤ (0 : Int) + d465 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1092, d42, d465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1603 p hg
    simpa only [d1092, d42, d465, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d42, d465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1622 p hg
    simpa only [d1092, d42, d465, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1624 (p : Pattern) (guard : d1092 p = 1) : d43 p ≤ (0 : Int) + d466 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d43, d466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1623 p hg
    simpa only [d43, d466, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d43, d466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1616 p hg
    simpa only [d43, d466, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1625 (p : Pattern) (guard : d1092 p = 1) : d44 p ≤ (0 : Int) + d467 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d44, d467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1621 p hg
    simpa only [d44, d467, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d44, d467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1624 p hg
    simpa only [d44, d467, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1626 (p : Pattern) (guard : d1092 p = 1) : d45 p ≤ (0 : Int) + d468 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d45, d468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1618 p hg
    simpa only [d45, d468, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d45, d468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1625 p hg
    simpa only [d45, d468, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1627 (p : Pattern) (guard : d1093 p = 1) : d45 p ≤ (0 : Int) + d468 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1609 p hg
    simpa only [d1093, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d1093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1626 p hg
    simpa only [d1093, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1628 (p : Pattern) (guard : d0 p = 1) : d152 p ≤ (0 : Int) + d475 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1629 (p : Pattern) (guard : d1094 p = 1) : d184 p ≤ (0 : Int) + d476 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1093 p = 1 := by simpa only [d1094, d184, d476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1627 p hg
    simpa only [d1094, d184, d476, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1094, d184, d476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1628 p hg
    simpa only [d1094, d184, d476, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1630 (p : Pattern) (guard : d1088 p = 1) : d27 p ≤ (0 : Int) + d477 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d27, d477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1582 p hg
    simpa only [d27, d477, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d27, d477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1594 p hg
    simpa only [d27, d477, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1631 (p : Pattern) (guard : d0 p = 1) : d40 p ≤ (0 : Int) + d138 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1632 (p : Pattern) (guard : d1088 p = 1) : d40 p ≤ (0 : Int) + d478 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1088, d478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1450 p hg
    simpa only [d1088, d478, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1088, d478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1631 p hg
    simpa only [d1088, d478, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1633 (p : Pattern) (guard : d1088 p = 1) : d68 p ≤ (0 : Int) + d68 p := by
  omega
theorem compare1634 (p : Pattern) (guard : d1088 p = 1) : d69 p ≤ (0 : Int) + d479 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d69, d479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1632 p hg
    simpa only [d69, d479, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d69, d479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1633 p hg
    simpa only [d69, d479, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1635 (p : Pattern) (guard : d1088 p = 1) : d24 p ≤ (0 : Int) + d70 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1088, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1453 p hg
    simpa only [d1088, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1088, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1592 p hg
    simpa only [d1088, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1636 (p : Pattern) (guard : d1088 p = 1) : d70 p ≤ (0 : Int) + d70 p := by
  omega
theorem compare1637 (p : Pattern) (guard : d1088 p = 1) : d71 p ≤ (0 : Int) + d70 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1635 p hg
    simpa only [d71, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1636 p hg
    simpa only [d71, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1638 (p : Pattern) (guard : d1088 p = 1) : d72 p ≤ (0 : Int) + d480 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d72, d480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1634 p hg
    simpa only [d72, d480, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d72, d480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1637 p hg
    simpa only [d72, d480, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1639 (p : Pattern) (guard : d1088 p = 1) : d73 p ≤ (0 : Int) + d481 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d73, d481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1630 p hg
    simpa only [d73, d481, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d73, d481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1638 p hg
    simpa only [d73, d481, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1640 (p : Pattern) (guard : d1088 p = 1) : d74 p ≤ (0 : Int) + d482 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d74, d482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1596 p hg
    simpa only [d74, d482, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d74, d482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1639 p hg
    simpa only [d74, d482, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1641 (p : Pattern) (guard : d0 p = 1) : d8 p ≤ (0 : Int) + d142 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1642 (p : Pattern) (guard : d1088 p = 1) : d8 p ≤ (0 : Int) + d483 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1088, d483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare199 p hg
    simpa only [d1088, d483, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1088, d483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1641 p hg
    simpa only [d1088, d483, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1643 (p : Pattern) (guard : d1092 p = 1) : d16 p ≤ (0 : Int) + d484 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1092, d16, d484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1642 p hg
    simpa only [d1092, d16, d484, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d16, d484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1610 p hg
    simpa only [d1092, d16, d484, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1644 (p : Pattern) (guard : d1092 p = 1) : d27 p ≤ (0 : Int) + d485 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d27, d485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1643 p hg
    simpa only [d27, d485, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d27, d485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1616 p hg
    simpa only [d27, d485, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1645 (p : Pattern) (guard : d1092 p = 1) : d75 p ≤ (0 : Int) + d75 p := by
  omega
theorem compare1646 (p : Pattern) (guard : d1092 p = 1) : d76 p ≤ (0 : Int) + d486 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d76, d486, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1644 p hg
    simpa only [d76, d486, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d76, d486, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1645 p hg
    simpa only [d76, d486, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1647 (p : Pattern) (guard : d1092 p = 1) : d77 p ≤ (0 : Int) + d487 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d77, d487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1618 p hg
    simpa only [d77, d487, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d77, d487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1646 p hg
    simpa only [d77, d487, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1648 (p : Pattern) (guard : d1093 p = 1) : d78 p ≤ (0 : Int) + d488 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1093, d78, d488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1640 p hg
    simpa only [d1093, d78, d488, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d1093, d78, d488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1647 p hg
    simpa only [d1093, d78, d488, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1649 (p : Pattern) (guard : d0 p = 1) : d155 p ≤ (0 : Int) + d493 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1650 (p : Pattern) (guard : d1094 p = 1) : d185 p ≤ (0 : Int) + d494 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1093 p = 1 := by simpa only [d1094, d185, d494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1648 p hg
    simpa only [d1094, d185, d494, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1094, d185, d494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1649 p hg
    simpa only [d1094, d185, d494, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1651 (p : Pattern) (guard : d1094 p = 1) : d186 p ≤ (0 : Int) + d495 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1094 p = 1 := by simpa only [d186, d495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1629 p hg
    simpa only [d186, d495, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1094 p = 1 := by simpa only [d186, d495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1650 p hg
    simpa only [d186, d495, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1652 (p : Pattern) (guard : d0 p = 1) : d97 p ≤ (0 : Int) + d52 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1653 (p : Pattern) (guard : d1092 p = 1) : d187 p ≤ (0 : Int) + d457 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1092, d187, d457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1579 p hg
    simpa only [d1092, d187, d457, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d187, d457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1652 p hg
    simpa only [d1092, d187, d457, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1654 (p : Pattern) (guard : d1092 p = 1) : d187 p ≤ (0 : Int) + d52 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1092, d187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1584 p hg
    simpa only [d1092, d187, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1652 p hg
    simpa only [d1092, d187, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1655 (p : Pattern) (guard : d1092 p = 1) : d187 p ≤ (0 : Int) + d458 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1653 p hg
    simpa only [d458, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1654 p hg
    simpa only [d458, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1656 (p : Pattern) (guard : d1092 p = 1) : d187 p ≤ (0 : Int) + d460 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1092, d187, d460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1588 p hg
    simpa only [d1092, d187, d460, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d187, d460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1652 p hg
    simpa only [d1092, d187, d460, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1657 (p : Pattern) (guard : d0 p = 1) : d70 p ≤ (0 : Int) + d54 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1658 (p : Pattern) (guard : d1092 p = 1) : d188 p ≤ (0 : Int) + d54 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1092, d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1591 p hg
    simpa only [d1092, d188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1657 p hg
    simpa only [d1092, d188, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1659 (p : Pattern) (guard : d1092 p = 1) : d189 p ≤ (0 : Int) + d461 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d189, d461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1656 p hg
    simpa only [d189, d461, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d189, d461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1658 p hg
    simpa only [d189, d461, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1660 (p : Pattern) (guard : d1092 p = 1) : d190 p ≤ (0 : Int) + d462 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d190, d462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1655 p hg
    simpa only [d190, d462, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d190, d462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1659 p hg
    simpa only [d190, d462, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1661 (p : Pattern) (guard : d1092 p = 1) : d187 p ≤ (0 : Int) + d484 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1092, d187, d484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1642 p hg
    simpa only [d1092, d187, d484, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d187, d484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1652 p hg
    simpa only [d1092, d187, d484, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1662 (p : Pattern) (guard : d0 p = 1) : d70 p ≤ (0 : Int) + d58 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1663 (p : Pattern) (guard : d1092 p = 1) : d191 p ≤ (0 : Int) + d58 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1092, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1598 p hg
    simpa only [d1092, d191, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1662 p hg
    simpa only [d1092, d191, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1664 (p : Pattern) (guard : d1092 p = 1) : d192 p ≤ (0 : Int) + d496 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d192, d496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1661 p hg
    simpa only [d192, d496, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d192, d496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1663 p hg
    simpa only [d192, d496, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1665 (p : Pattern) (guard : d0 p = 1) : d38 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1666 (p : Pattern) (guard : d1088 p = 1) : d38 p ≤ (0 : Int) + d61 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1088, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare232 p hg
    simpa only [d1088, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1088, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1665 p hg
    simpa only [d1088, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1667 (p : Pattern) (guard : d0 p = 1) : d68 p ≤ (0 : Int) + d61 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1668 (p : Pattern) (guard : d1092 p = 1) : d193 p ≤ (0 : Int) + d61 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1092, d193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1666 p hg
    simpa only [d1092, d193, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1667 p hg
    simpa only [d1092, d193, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1669 (p : Pattern) (guard : d1092 p = 1) : d194 p ≤ (0 : Int) + d473 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d194, d473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1668 p hg
    simpa only [d194, d473, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d194, d473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1658 p hg
    simpa only [d194, d473, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1670 (p : Pattern) (guard : d1092 p = 1) : d195 p ≤ (0 : Int) + d497 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d195, d497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1664 p hg
    simpa only [d195, d497, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d195, d497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1669 p hg
    simpa only [d195, d497, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1671 (p : Pattern) (guard : d1092 p = 1) : d196 p ≤ (0 : Int) + d498 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d196, d498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1660 p hg
    simpa only [d196, d498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d196, d498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1670 p hg
    simpa only [d196, d498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1672 (p : Pattern) (guard : d1093 p = 1) : d197 p ≤ (0 : Int) + d499 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1093, d197, d499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1609 p hg
    simpa only [d1093, d197, d499, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d1093, d197, d499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1671 p hg
    simpa only [d1093, d197, d499, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1673 (p : Pattern) (guard : d0 p = 1) : d155 p ≤ (0 : Int) + d508 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1674 (p : Pattern) (guard : d1094 p = 1) : d198 p ≤ (0 : Int) + d509 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1093 p = 1 := by simpa only [d1094, d198, d509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1672 p hg
    simpa only [d1094, d198, d509, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1094, d198, d509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1673 p hg
    simpa only [d1094, d198, d509, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1675 (p : Pattern) (guard : d1088 p = 1) : d16 p ≤ (0 : Int) + d484 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d16, d484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1642 p hg
    simpa only [d16, d484, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d16, d484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1581 p hg
    simpa only [d16, d484, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1676 (p : Pattern) (guard : d1088 p = 1) : d27 p ≤ (0 : Int) + d485 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d27, d485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1675 p hg
    simpa only [d27, d485, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d27, d485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1594 p hg
    simpa only [d27, d485, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1677 (p : Pattern) (guard : d1088 p = 1) : d75 p ≤ (0 : Int) + d75 p := by
  omega
theorem compare1678 (p : Pattern) (guard : d1088 p = 1) : d76 p ≤ (0 : Int) + d486 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d76, d486, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1676 p hg
    simpa only [d76, d486, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d76, d486, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1677 p hg
    simpa only [d76, d486, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1679 (p : Pattern) (guard : d1088 p = 1) : d77 p ≤ (0 : Int) + d487 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d77, d487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1596 p hg
    simpa only [d77, d487, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d77, d487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1678 p hg
    simpa only [d77, d487, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban32Refined
