/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban12CostPartition.Comparisons010
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare1540 (p : Pattern) (guard : d743 p = 1) : d316 p ≤ (12 : Int) + d134 p := by
  cases selected : p 132 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d743, d316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1496 p hg
    simpa only [d743, d316, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d743, d316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1539 p hg
    simpa only [d743, d316, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1541 (p : Pattern) (guard : d0 p = 1) : d317 p ≤ (12 : Int) + d152 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1542 (p : Pattern) (guard : d1 p = 1) : d137 p ≤ (12 : Int) + d56 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d137, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1503 p hg
    simpa only [d137, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d137, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare636 p hg
    simpa only [d137, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1543 (p : Pattern) (guard : d1 p = 1) : d139 p ≤ (12 : Int) + d57 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d139, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1504 p hg
    simpa only [d139, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d139, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1542 p hg
    simpa only [d139, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1544 (p : Pattern) (guard : d1 p = 1) : d153 p ≤ (12 : Int) + d57 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare631 p hg
    simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1543 p hg
    simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1545 (p : Pattern) (guard : d742 p = 1) : d191 p ≤ (12 : Int) + d57 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d742, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1544 p hg
    simpa only [d742, d191, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d742, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1497 p hg
    simpa only [d742, d191, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1546 (p : Pattern) (guard : d1 p = 1) : d143 p ≤ (12 : Int) + d61 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d143, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1510 p hg
    simpa only [d143, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d143, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare648 p hg
    simpa only [d143, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1547 (p : Pattern) (guard : d1 p = 1) : d144 p ≤ (12 : Int) + d62 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d144, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1542 p hg
    simpa only [d144, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d144, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1546 p hg
    simpa only [d144, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1548 (p : Pattern) (guard : d1 p = 1) : d146 p ≤ (12 : Int) + d63 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d146, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1512 p hg
    simpa only [d146, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d146, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1547 p hg
    simpa only [d146, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1549 (p : Pattern) (guard : d1 p = 1) : d155 p ≤ (12 : Int) + d63 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare640 p hg
    simpa only [d155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1548 p hg
    simpa only [d155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1550 (p : Pattern) (guard : d742 p = 1) : d253 p ≤ (12 : Int) + d63 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d742, d253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1549 p hg
    simpa only [d742, d253, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d742, d253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1499 p hg
    simpa only [d742, d253, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1551 (p : Pattern) (guard : d742 p = 1) : d254 p ≤ (12 : Int) + d64 p := by
  cases selected : p 141 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d254, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1545 p hg
    simpa only [d254, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d254, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1550 p hg
    simpa only [d254, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1552 (p : Pattern) (guard : d742 p = 1) : d66 p ≤ (12 : Int) + d66 p := by
  omega
theorem compare1553 (p : Pattern) (guard : d742 p = 1) : d255 p ≤ (12 : Int) + d67 p := by
  cases selected : p 134 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d255, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1551 p hg
    simpa only [d255, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d255, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1552 p hg
    simpa only [d255, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1554 (p : Pattern) (guard : d1 p = 1) : d55 p ≤ (12 : Int) + d137 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1524 p hg
    simpa only [d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare636 p hg
    simpa only [d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1555 (p : Pattern) (guard : d1 p = 1) : d55 p ≤ (12 : Int) + d138 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare635 p hg
    simpa only [d138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1554 p hg
    simpa only [d138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1556 (p : Pattern) (guard : d1 p = 1) : d55 p ≤ (12 : Int) + d139 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1525 p hg
    simpa only [d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1554 p hg
    simpa only [d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1557 (p : Pattern) (guard : d1 p = 1) : d55 p ≤ (12 : Int) + d140 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1555 p hg
    simpa only [d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1556 p hg
    simpa only [d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1558 (p : Pattern) (guard : d0 p = 1) : d55 p ≤ (12 : Int) + d141 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1559 (p : Pattern) (guard : d742 p = 1) : d55 p ≤ (12 : Int) + d142 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d742, d142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1557 p hg
    simpa only [d742, d142, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d742, d142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1558 p hg
    simpa only [d742, d142, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1560 (p : Pattern) (guard : d1 p = 1) : d60 p ≤ (12 : Int) + d143 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1530 p hg
    simpa only [d143, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare648 p hg
    simpa only [d143, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1561 (p : Pattern) (guard : d1 p = 1) : d65 p ≤ (12 : Int) + d144 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d65, d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1554 p hg
    simpa only [d65, d144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d65, d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1560 p hg
    simpa only [d65, d144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1562 (p : Pattern) (guard : d1 p = 1) : d65 p ≤ (12 : Int) + d145 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare647 p hg
    simpa only [d145, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1561 p hg
    simpa only [d145, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1563 (p : Pattern) (guard : d1 p = 1) : d65 p ≤ (12 : Int) + d146 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1532 p hg
    simpa only [d146, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1561 p hg
    simpa only [d146, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1564 (p : Pattern) (guard : d1 p = 1) : d65 p ≤ (12 : Int) + d147 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1562 p hg
    simpa only [d147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1563 p hg
    simpa only [d147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1565 (p : Pattern) (guard : d0 p = 1) : d65 p ≤ (12 : Int) + d148 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1566 (p : Pattern) (guard : d742 p = 1) : d65 p ≤ (12 : Int) + d149 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d742, d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1564 p hg
    simpa only [d742, d149, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d742, d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1565 p hg
    simpa only [d742, d149, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1567 (p : Pattern) (guard : d742 p = 1) : d66 p ≤ (12 : Int) + d150 p := by
  cases selected : p 141 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d66, d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1559 p hg
    simpa only [d66, d150, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d66, d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1566 p hg
    simpa only [d66, d150, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1568 (p : Pattern) (guard : d742 p = 1) : d66 p ≤ (12 : Int) + d151 p := by
  cases selected : p 134 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1567 p hg
    simpa only [d151, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1552 p hg
    simpa only [d151, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1569 (p : Pattern) (guard : d742 p = 1) : d256 p ≤ (12 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d256, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1553 p hg
    simpa only [d256, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d256, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1568 p hg
    simpa only [d256, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1570 (p : Pattern) (guard : d743 p = 1) : d318 p ≤ (12 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d743, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1541 p hg
    simpa only [d743, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d743, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1569 p hg
    simpa only [d743, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1571 (p : Pattern) (guard : d743 p = 1) : d319 p ≤ (12 : Int) + d814 p := by
  cases selected : p 108 with
  | false =>
    have hg : d743 p = 1 := by simpa only [d319, d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1540 p hg
    simpa only [d319, d814, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d743 p = 1 := by simpa only [d319, d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1570 p hg
    simpa only [d319, d814, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1572 (p : Pattern) (guard : d0 p = 1) : d55 p ≤ (0 : Int) + d122 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1573 (p : Pattern) (guard : d742 p = 1) : d229 p ≤ (0 : Int) + d179 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d742, d229, d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare324 p hg
    simpa only [d742, d229, d179, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d742, d229, d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1572 p hg
    simpa only [d742, d229, d179, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1574 (p : Pattern) (guard : d0 p = 1) : d65 p ≤ (0 : Int) + d129 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1575 (p : Pattern) (guard : d742 p = 1) : d230 p ≤ (0 : Int) + d237 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d742, d230, d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare327 p hg
    simpa only [d742, d230, d237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d742, d230, d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1574 p hg
    simpa only [d742, d230, d237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1576 (p : Pattern) (guard : d742 p = 1) : d231 p ≤ (0 : Int) + d238 p := by
  cases selected : p 141 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d231, d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1573 p hg
    simpa only [d231, d238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d231, d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1575 p hg
    simpa only [d231, d238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1577 (p : Pattern) (guard : d742 p = 1) : d232 p ≤ (0 : Int) + d239 p := by
  cases selected : p 134 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d232, d239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1464 p hg
    simpa only [d232, d239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d232, d239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1576 p hg
    simpa only [d232, d239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1578 (p : Pattern) (guard : d742 p = 1) : d242 p ≤ (0 : Int) + d242 p := by
  omega
theorem compare1579 (p : Pattern) (guard : d742 p = 1) : d315 p ≤ (0 : Int) + d243 p := by
  cases selected : p 133 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d315, d243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1577 p hg
    simpa only [d315, d243, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d315, d243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1578 p hg
    simpa only [d315, d243, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1580 (p : Pattern) (guard : d742 p = 1) : d244 p ≤ (0 : Int) + d244 p := by
  omega
theorem compare1581 (p : Pattern) (guard : d742 p = 1) : d316 p ≤ (0 : Int) + d245 p := by
  cases selected : p 132 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d316, d245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1579 p hg
    simpa only [d316, d245, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d316, d245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1580 p hg
    simpa only [d316, d245, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1582 (p : Pattern) (guard : d0 p = 1) : d55 p ≤ (0 : Int) + d153 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1583 (p : Pattern) (guard : d742 p = 1) : d68 p ≤ (0 : Int) + d186 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d742, d68, d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare208 p hg
    simpa only [d742, d68, d186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d742, d68, d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1582 p hg
    simpa only [d742, d68, d186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1584 (p : Pattern) (guard : d0 p = 1) : d65 p ≤ (0 : Int) + d155 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1585 (p : Pattern) (guard : d742 p = 1) : d69 p ≤ (0 : Int) + d246 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d742, d69, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare320 p hg
    simpa only [d742, d69, d246, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d742, d69, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1584 p hg
    simpa only [d742, d69, d246, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1586 (p : Pattern) (guard : d742 p = 1) : d70 p ≤ (0 : Int) + d247 p := by
  cases selected : p 141 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d70, d247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1583 p hg
    simpa only [d70, d247, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d70, d247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1585 p hg
    simpa only [d70, d247, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1587 (p : Pattern) (guard : d742 p = 1) : d71 p ≤ (0 : Int) + d248 p := by
  cases selected : p 134 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d71, d248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1586 p hg
    simpa only [d71, d248, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d71, d248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare346 p hg
    simpa only [d71, d248, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1588 (p : Pattern) (guard : d742 p = 1) : d251 p ≤ (0 : Int) + d251 p := by
  omega
theorem compare1589 (p : Pattern) (guard : d742 p = 1) : d317 p ≤ (0 : Int) + d252 p := by
  cases selected : p 133 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d317, d252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1587 p hg
    simpa only [d317, d252, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d317, d252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1588 p hg
    simpa only [d317, d252, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1590 (p : Pattern) (guard : d742 p = 1) : d256 p ≤ (0 : Int) + d256 p := by
  omega
theorem compare1591 (p : Pattern) (guard : d742 p = 1) : d318 p ≤ (0 : Int) + d257 p := by
  cases selected : p 132 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d318, d257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1589 p hg
    simpa only [d318, d257, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d318, d257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1590 p hg
    simpa only [d318, d257, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1592 (p : Pattern) (guard : d742 p = 1) : d319 p ≤ (0 : Int) + d258 p := by
  cases selected : p 108 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d319, d258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1581 p hg
    simpa only [d319, d258, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d319, d258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1591 p hg
    simpa only [d319, d258, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1593 (p : Pattern) (guard : d0 p = 1) : d55 p ≤ (2 : Int) + d57 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1594 (p : Pattern) (guard : d742 p = 1) : d68 p ≤ (2 : Int) + d57 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d742, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare50 p hg
    simpa only [d742, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d742, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1593 p hg
    simpa only [d742, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1595 (p : Pattern) (guard : d0 p = 1) : d65 p ≤ (2 : Int) + d63 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1596 (p : Pattern) (guard : d742 p = 1) : d69 p ≤ (2 : Int) + d63 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d742, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare53 p hg
    simpa only [d742, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d742, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1595 p hg
    simpa only [d742, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1597 (p : Pattern) (guard : d742 p = 1) : d70 p ≤ (2 : Int) + d64 p := by
  cases selected : p 141 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d70, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1594 p hg
    simpa only [d70, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d70, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1596 p hg
    simpa only [d70, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1598 (p : Pattern) (guard : d0 p = 1) : d55 p ≤ (2 : Int) + d122 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1599 (p : Pattern) (guard : d742 p = 1) : d229 p ≤ (2 : Int) + d179 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d742, d229, d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare57 p hg
    simpa only [d742, d229, d179, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d742, d229, d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1598 p hg
    simpa only [d742, d229, d179, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1600 (p : Pattern) (guard : d0 p = 1) : d65 p ≤ (2 : Int) + d129 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1601 (p : Pattern) (guard : d742 p = 1) : d230 p ≤ (2 : Int) + d237 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d742, d230, d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare64 p hg
    simpa only [d742, d230, d237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d742, d230, d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1600 p hg
    simpa only [d742, d230, d237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1602 (p : Pattern) (guard : d742 p = 1) : d231 p ≤ (2 : Int) + d238 p := by
  cases selected : p 141 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d231, d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1599 p hg
    simpa only [d231, d238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d231, d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1601 p hg
    simpa only [d231, d238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1603 (p : Pattern) (guard : d742 p = 1) : d232 p ≤ (2 : Int) + d239 p := by
  cases selected : p 134 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d232, d239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1597 p hg
    simpa only [d232, d239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d232, d239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1602 p hg
    simpa only [d232, d239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1604 (p : Pattern) (guard : d742 p = 1) : d242 p ≤ (2 : Int) + d242 p := by
  omega
theorem compare1605 (p : Pattern) (guard : d742 p = 1) : d315 p ≤ (2 : Int) + d243 p := by
  cases selected : p 133 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d315, d243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1603 p hg
    simpa only [d315, d243, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d315, d243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1604 p hg
    simpa only [d315, d243, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1606 (p : Pattern) (guard : d742 p = 1) : d244 p ≤ (2 : Int) + d244 p := by
  omega
theorem compare1607 (p : Pattern) (guard : d742 p = 1) : d316 p ≤ (2 : Int) + d245 p := by
  cases selected : p 132 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d316, d245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1605 p hg
    simpa only [d316, d245, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d316, d245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1606 p hg
    simpa only [d316, d245, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1608 (p : Pattern) (guard : d0 p = 1) : d55 p ≤ (2 : Int) + d153 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1609 (p : Pattern) (guard : d742 p = 1) : d68 p ≤ (2 : Int) + d186 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d742, d68, d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare50 p hg
    simpa only [d742, d68, d186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d742, d68, d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1608 p hg
    simpa only [d742, d68, d186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1610 (p : Pattern) (guard : d0 p = 1) : d65 p ≤ (2 : Int) + d155 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1611 (p : Pattern) (guard : d742 p = 1) : d69 p ≤ (2 : Int) + d246 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d742, d69, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare53 p hg
    simpa only [d742, d69, d246, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d742, d69, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1610 p hg
    simpa only [d742, d69, d246, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1612 (p : Pattern) (guard : d742 p = 1) : d70 p ≤ (2 : Int) + d247 p := by
  cases selected : p 141 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d70, d247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1609 p hg
    simpa only [d70, d247, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d70, d247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1611 p hg
    simpa only [d70, d247, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1613 (p : Pattern) (guard : d742 p = 1) : d71 p ≤ (2 : Int) + d248 p := by
  cases selected : p 134 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d71, d248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1612 p hg
    simpa only [d71, d248, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d71, d248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare134 p hg
    simpa only [d71, d248, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1614 (p : Pattern) (guard : d742 p = 1) : d251 p ≤ (2 : Int) + d251 p := by
  omega
theorem compare1615 (p : Pattern) (guard : d742 p = 1) : d317 p ≤ (2 : Int) + d252 p := by
  cases selected : p 133 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d317, d252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1613 p hg
    simpa only [d317, d252, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d317, d252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1614 p hg
    simpa only [d317, d252, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1616 (p : Pattern) (guard : d742 p = 1) : d256 p ≤ (2 : Int) + d256 p := by
  omega
theorem compare1617 (p : Pattern) (guard : d742 p = 1) : d318 p ≤ (2 : Int) + d257 p := by
  cases selected : p 132 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d318, d257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1615 p hg
    simpa only [d318, d257, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d318, d257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1616 p hg
    simpa only [d318, d257, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1618 (p : Pattern) (guard : d742 p = 1) : d319 p ≤ (2 : Int) + d258 p := by
  cases selected : p 108 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d319, d258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1607 p hg
    simpa only [d319, d258, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d319, d258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1617 p hg
    simpa only [d319, d258, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1619 (p : Pattern) (guard : d798 p = 1) : d68 p ≤ (0 : Int) + d114 p := by
  cases selected : p 158 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d798, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare473 p hg
    simpa only [d798, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d798, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1471 p hg
    simpa only [d798, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1620 (p : Pattern) (guard : d798 p = 1) : d69 p ≤ (0 : Int) + d116 p := by
  cases selected : p 158 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d798, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare474 p hg
    simpa only [d798, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d798, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1473 p hg
    simpa only [d798, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1621 (p : Pattern) (guard : d798 p = 1) : d70 p ≤ (0 : Int) + d335 p := by
  cases selected : p 141 with
  | false =>
    have hg : d798 p = 1 := by simpa only [d70, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1619 p hg
    simpa only [d70, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d798 p = 1 := by simpa only [d70, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1620 p hg
    simpa only [d70, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1622 (p : Pattern) (guard : d798 p = 1) : d229 p ≤ (0 : Int) + d107 p := by
  cases selected : p 158 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d798, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare477 p hg
    simpa only [d798, d229, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d798, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1465 p hg
    simpa only [d798, d229, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1623 (p : Pattern) (guard : d798 p = 1) : d230 p ≤ (0 : Int) + d110 p := by
  cases selected : p 158 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d798, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare481 p hg
    simpa only [d798, d230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d798, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1467 p hg
    simpa only [d798, d230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1624 (p : Pattern) (guard : d798 p = 1) : d231 p ≤ (0 : Int) + d336 p := by
  cases selected : p 141 with
  | false =>
    have hg : d798 p = 1 := by simpa only [d231, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1622 p hg
    simpa only [d231, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d798 p = 1 := by simpa only [d231, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1623 p hg
    simpa only [d231, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1625 (p : Pattern) (guard : d798 p = 1) : d232 p ≤ (0 : Int) + d337 p := by
  cases selected : p 134 with
  | false =>
    have hg : d798 p = 1 := by simpa only [d232, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1621 p hg
    simpa only [d232, d337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d798 p = 1 := by simpa only [d232, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1624 p hg
    simpa only [d232, d337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1626 (p : Pattern) (guard : d798 p = 1) : d68 p ≤ (0 : Int) + d338 p := by
  cases selected : p 158 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d798, d68, d338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare473 p hg
    simpa only [d798, d68, d338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d798, d68, d338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare728 p hg
    simpa only [d798, d68, d338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1627 (p : Pattern) (guard : d798 p = 1) : d69 p ≤ (0 : Int) + d339 p := by
  cases selected : p 158 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d798, d69, d339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare474 p hg
    simpa only [d798, d69, d339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d798, d69, d339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare732 p hg
    simpa only [d798, d69, d339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1628 (p : Pattern) (guard : d798 p = 1) : d70 p ≤ (0 : Int) + d340 p := by
  cases selected : p 141 with
  | false =>
    have hg : d798 p = 1 := by simpa only [d70, d340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1626 p hg
    simpa only [d70, d340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d798 p = 1 := by simpa only [d70, d340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1627 p hg
    simpa only [d70, d340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1629 (p : Pattern) (guard : d798 p = 1) : d181 p ≤ (0 : Int) + d211 p := by
  cases selected : p 158 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d798, d181, d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare490 p hg
    simpa only [d798, d181, d211, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d798, d181, d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare728 p hg
    simpa only [d798, d181, d211, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1630 (p : Pattern) (guard : d798 p = 1) : d240 p ≤ (0 : Int) + d212 p := by
  cases selected : p 158 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d798, d240, d212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare493 p hg
    simpa only [d798, d240, d212, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d798, d240, d212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare732 p hg
    simpa only [d798, d240, d212, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1631 (p : Pattern) (guard : d798 p = 1) : d241 p ≤ (0 : Int) + d213 p := by
  cases selected : p 141 with
  | false =>
    have hg : d798 p = 1 := by simpa only [d241, d213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1629 p hg
    simpa only [d241, d213, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d798 p = 1 := by simpa only [d241, d213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1630 p hg
    simpa only [d241, d213, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1632 (p : Pattern) (guard : d798 p = 1) : d242 p ≤ (0 : Int) + d341 p := by
  cases selected : p 134 with
  | false =>
    have hg : d798 p = 1 := by simpa only [d242, d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1628 p hg
    simpa only [d242, d341, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d798 p = 1 := by simpa only [d242, d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1631 p hg
    simpa only [d242, d341, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1633 (p : Pattern) (guard : d798 p = 1) : d315 p ≤ (0 : Int) + d342 p := by
  cases selected : p 133 with
  | false =>
    have hg : d798 p = 1 := by simpa only [d315, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1625 p hg
    simpa only [d315, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d798 p = 1 := by simpa only [d315, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1632 p hg
    simpa only [d315, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1634 (p : Pattern) (guard : d798 p = 1) : d244 p ≤ (0 : Int) + d343 p := by
  cases selected : p 133 with
  | false =>
    have hg : d798 p = 1 := by simpa only [d244, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1632 p hg
    simpa only [d244, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d798 p = 1 := by simpa only [d244, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare511 p hg
    simpa only [d244, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1635 (p : Pattern) (guard : d798 p = 1) : d316 p ≤ (0 : Int) + d344 p := by
  cases selected : p 132 with
  | false =>
    have hg : d798 p = 1 := by simpa only [d316, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1633 p hg
    simpa only [d316, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d798 p = 1 := by simpa only [d316, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1634 p hg
    simpa only [d316, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1636 (p : Pattern) (guard : d798 p = 1) : d71 p ≤ (0 : Int) + d345 p := by
  cases selected : p 134 with
  | false =>
    have hg : d798 p = 1 := by simpa only [d71, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1621 p hg
    simpa only [d71, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d798 p = 1 := by simpa only [d71, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare511 p hg
    simpa only [d71, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1637 (p : Pattern) (guard : d798 p = 1) : d188 p ≤ (0 : Int) + d347 p := by
  cases selected : p 158 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d798, d188, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare504 p hg
    simpa only [d798, d188, d347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d798, d188, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare728 p hg
    simpa only [d798, d188, d347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1638 (p : Pattern) (guard : d798 p = 1) : d249 p ≤ (0 : Int) + d349 p := by
  cases selected : p 158 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d798, d249, d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare508 p hg
    simpa only [d798, d249, d349, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d798, d249, d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare732 p hg
    simpa only [d798, d249, d349, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1639 (p : Pattern) (guard : d798 p = 1) : d250 p ≤ (0 : Int) + d350 p := by
  cases selected : p 141 with
  | false =>
    have hg : d798 p = 1 := by simpa only [d250, d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1637 p hg
    simpa only [d250, d350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d798 p = 1 := by simpa only [d250, d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1638 p hg
    simpa only [d250, d350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1640 (p : Pattern) (guard : d798 p = 1) : d251 p ≤ (0 : Int) + d351 p := by
  cases selected : p 134 with
  | false =>
    have hg : d798 p = 1 := by simpa only [d251, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1639 p hg
    simpa only [d251, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d798 p = 1 := by simpa only [d251, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare511 p hg
    simpa only [d251, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1641 (p : Pattern) (guard : d798 p = 1) : d317 p ≤ (0 : Int) + d352 p := by
  cases selected : p 133 with
  | false =>
    have hg : d798 p = 1 := by simpa only [d317, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1636 p hg
    simpa only [d317, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d798 p = 1 := by simpa only [d317, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1640 p hg
    simpa only [d317, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1642 (p : Pattern) (guard : d794 p = 1) : d153 p ≤ (0 : Int) + d114 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d794, d153, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare208 p hg
    simpa only [d794, d153, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d794, d153, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare503 p hg
    simpa only [d794, d153, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1643 (p : Pattern) (guard : d798 p = 1) : d191 p ≤ (0 : Int) + d338 p := by
  cases selected : p 158 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d798, d191, d338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1642 p hg
    simpa only [d798, d191, d338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d798, d191, d338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare728 p hg
    simpa only [d798, d191, d338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1644 (p : Pattern) (guard : d794 p = 1) : d155 p ≤ (0 : Int) + d116 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d794, d155, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare320 p hg
    simpa only [d794, d155, d116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d794, d155, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare507 p hg
    simpa only [d794, d155, d116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1645 (p : Pattern) (guard : d798 p = 1) : d253 p ≤ (0 : Int) + d339 p := by
  cases selected : p 158 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d798, d253, d339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1644 p hg
    simpa only [d798, d253, d339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d798, d253, d339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare732 p hg
    simpa only [d798, d253, d339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1646 (p : Pattern) (guard : d798 p = 1) : d254 p ≤ (0 : Int) + d340 p := by
  cases selected : p 141 with
  | false =>
    have hg : d798 p = 1 := by simpa only [d254, d340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1643 p hg
    simpa only [d254, d340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d798 p = 1 := by simpa only [d254, d340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1645 p hg
    simpa only [d254, d340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1647 (p : Pattern) (guard : d798 p = 1) : d255 p ≤ (0 : Int) + d353 p := by
  cases selected : p 134 with
  | false =>
    have hg : d798 p = 1 := by simpa only [d255, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1646 p hg
    simpa only [d255, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d798 p = 1 := by simpa only [d255, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare511 p hg
    simpa only [d255, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1648 (p : Pattern) (guard : d798 p = 1) : d256 p ≤ (0 : Int) + d354 p := by
  cases selected : p 133 with
  | false =>
    have hg : d798 p = 1 := by simpa only [d256, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1647 p hg
    simpa only [d256, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d798 p = 1 := by simpa only [d256, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare511 p hg
    simpa only [d256, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1649 (p : Pattern) (guard : d798 p = 1) : d318 p ≤ (0 : Int) + d355 p := by
  cases selected : p 132 with
  | false =>
    have hg : d798 p = 1 := by simpa only [d318, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1641 p hg
    simpa only [d318, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d798 p = 1 := by simpa only [d318, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1648 p hg
    simpa only [d318, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1650 (p : Pattern) (guard : d798 p = 1) : d319 p ≤ (0 : Int) + d356 p := by
  cases selected : p 108 with
  | false =>
    have hg : d798 p = 1 := by simpa only [d319, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1635 p hg
    simpa only [d319, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d798 p = 1 := by simpa only [d319, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1649 p hg
    simpa only [d319, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1651 (p : Pattern) (guard : d0 p = 1) : d57 p ≤ (0 : Int) + d56 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1652 (p : Pattern) (guard : d1 p = 1) : d7 p ≤ (0 : Int) + d56 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare282 p hg
    simpa only [d56, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare286 p hg
    simpa only [d56, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1653 (p : Pattern) (guard : d0 p = 1) : d56 p ≤ (0 : Int) + d56 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1654 (p : Pattern) (guard : d758 p = 1) : d57 p ≤ (0 : Int) + d56 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d758, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1652 p hg
    simpa only [d758, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d758, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1653 p hg
    simpa only [d758, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1655 (p : Pattern) (guard : d1000 p = 1) : d57 p ≤ (0 : Int) + d56 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1651 p hg
    simpa only [d1000, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d758 p = 1 := by simpa only [d1000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1654 p hg
    simpa only [d1000, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1656 (p : Pattern) (guard : d0 p = 1) : d55 p ≤ (0 : Int) + d56 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1657 (p : Pattern) (guard : d1001 p = 1) : d68 p ≤ (0 : Int) + d56 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1000 p = 1 := by simpa only [d1001, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1655 p hg
    simpa only [d1001, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1001, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1656 p hg
    simpa only [d1001, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1658 (p : Pattern) (guard : d0 p = 1) : d63 p ≤ (0 : Int) + d62 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1659 (p : Pattern) (guard : d1 p = 1) : d11 p ≤ (0 : Int) + d61 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare295 p hg
    simpa only [d61, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare301 p hg
    simpa only [d61, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1660 (p : Pattern) (guard : d1 p = 1) : d12 p ≤ (0 : Int) + d62 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d12, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1652 p hg
    simpa only [d12, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d12, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1659 p hg
    simpa only [d12, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1661 (p : Pattern) (guard : d0 p = 1) : d62 p ≤ (0 : Int) + d62 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1662 (p : Pattern) (guard : d758 p = 1) : d63 p ≤ (0 : Int) + d62 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d758, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1660 p hg
    simpa only [d758, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d758, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1661 p hg
    simpa only [d758, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1663 (p : Pattern) (guard : d1000 p = 1) : d63 p ≤ (0 : Int) + d62 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1658 p hg
    simpa only [d1000, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d758 p = 1 := by simpa only [d1000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1662 p hg
    simpa only [d1000, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1664 (p : Pattern) (guard : d0 p = 1) : d65 p ≤ (0 : Int) + d62 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1665 (p : Pattern) (guard : d1001 p = 1) : d69 p ≤ (0 : Int) + d62 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1000 p = 1 := by simpa only [d1001, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1663 p hg
    simpa only [d1001, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1001, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1664 p hg
    simpa only [d1001, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1666 (p : Pattern) (guard : d1001 p = 1) : d70 p ≤ (0 : Int) + d451 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1001 p = 1 := by simpa only [d70, d451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1657 p hg
    simpa only [d70, d451, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1001 p = 1 := by simpa only [d70, d451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1665 p hg
    simpa only [d70, d451, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1667 (p : Pattern) (guard : d758 p = 1) : d106 p ≤ (0 : Int) + d55 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d758, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare286 p hg
    simpa only [d758, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d758, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare728 p hg
    simpa only [d758, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1668 (p : Pattern) (guard : d1000 p = 1) : d106 p ≤ (0 : Int) + d55 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare476 p hg
    simpa only [d1000, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d758 p = 1 := by simpa only [d1000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1667 p hg
    simpa only [d1000, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1669 (p : Pattern) (guard : d1001 p = 1) : d229 p ≤ (0 : Int) + d55 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1000 p = 1 := by simpa only [d1001, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1668 p hg
    simpa only [d1001, d229, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1001, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare728 p hg
    simpa only [d1001, d229, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1670 (p : Pattern) (guard : d758 p = 1) : d109 p ≤ (0 : Int) + d65 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d758, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare457 p hg
    simpa only [d758, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d758, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare732 p hg
    simpa only [d758, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1671 (p : Pattern) (guard : d1000 p = 1) : d109 p ≤ (0 : Int) + d65 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare480 p hg
    simpa only [d1000, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d758 p = 1 := by simpa only [d1000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1670 p hg
    simpa only [d1000, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1672 (p : Pattern) (guard : d1001 p = 1) : d230 p ≤ (0 : Int) + d65 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1000 p = 1 := by simpa only [d1001, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1671 p hg
    simpa only [d1001, d230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1001, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare732 p hg
    simpa only [d1001, d230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1673 (p : Pattern) (guard : d1001 p = 1) : d231 p ≤ (0 : Int) + d66 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1001 p = 1 := by simpa only [d231, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1669 p hg
    simpa only [d231, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1001 p = 1 := by simpa only [d231, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1672 p hg
    simpa only [d231, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1674 (p : Pattern) (guard : d1001 p = 1) : d232 p ≤ (0 : Int) + d1002 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1001 p = 1 := by simpa only [d232, d1002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1666 p hg
    simpa only [d232, d1002, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1001 p = 1 := by simpa only [d232, d1002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1673 p hg
    simpa only [d232, d1002, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1675 (p : Pattern) (guard : d1001 p = 1) : d68 p ≤ (0 : Int) + d456 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1000 p = 1 := by simpa only [d1001, d68, d456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1655 p hg
    simpa only [d1001, d68, d456, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1001, d68, d456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare728 p hg
    simpa only [d1001, d68, d456, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1676 (p : Pattern) (guard : d1001 p = 1) : d69 p ≤ (0 : Int) + d457 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1000 p = 1 := by simpa only [d1001, d69, d457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1663 p hg
    simpa only [d1001, d69, d457, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1001, d69, d457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare732 p hg
    simpa only [d1001, d69, d457, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1677 (p : Pattern) (guard : d1001 p = 1) : d70 p ≤ (0 : Int) + d458 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1001 p = 1 := by simpa only [d70, d458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1675 p hg
    simpa only [d70, d458, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1001 p = 1 := by simpa only [d70, d458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1676 p hg
    simpa only [d70, d458, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1678 (p : Pattern) (guard : d758 p = 1) : d121 p ≤ (0 : Int) + d55 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d758, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare452 p hg
    simpa only [d758, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d758, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare728 p hg
    simpa only [d758, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1679 (p : Pattern) (guard : d1000 p = 1) : d122 p ≤ (0 : Int) + d55 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1000, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare476 p hg
    simpa only [d1000, d122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d758 p = 1 := by simpa only [d1000, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1678 p hg
    simpa only [d1000, d122, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban12CostPartition
