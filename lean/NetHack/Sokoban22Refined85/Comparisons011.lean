/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons010
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare1540 (p : Pattern) (guard : d1 p = 1) : d82 p ≤ (0 : Int) + d94 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d82, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1531 p hg
    simpa only [d82, d94, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d82, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1539 p hg
    simpa only [d82, d94, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1541 (p : Pattern) (guard : d1 p = 1) : d32 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1508 p hg
    simpa only [d32, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d32, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1542 (p : Pattern) (guard : d1 p = 1) : d53 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1508 p hg
    simpa only [d53, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1541 p hg
    simpa only [d53, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1543 (p : Pattern) (guard : d1 p = 1) : d54 p ≤ (0 : Int) + d63 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d54, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1524 p hg
    simpa only [d54, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d54, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1542 p hg
    simpa only [d54, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1544 (p : Pattern) (guard : d1 p = 1) : d55 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1527 p hg
    simpa only [d55, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare870 p hg
    simpa only [d55, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1545 (p : Pattern) (guard : d1 p = 1) : d56 p ≤ (0 : Int) + d91 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d56, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1543 p hg
    simpa only [d56, d91, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d56, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1544 p hg
    simpa only [d56, d91, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1546 (p : Pattern) (guard : d1 p = 1) : d61 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1527 p hg
    simpa only [d61, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare851 p hg
    simpa only [d61, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1547 (p : Pattern) (guard : d1 p = 1) : d64 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1546 p hg
    simpa only [d64, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare735 p hg
    simpa only [d64, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1548 (p : Pattern) (guard : d1 p = 1) : d65 p ≤ (0 : Int) + d93 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d65, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1545 p hg
    simpa only [d65, d93, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d65, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1547 p hg
    simpa only [d65, d93, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1549 (p : Pattern) (guard : d1 p = 1) : d83 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare959 p hg
    simpa only [d83, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d83, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1550 (p : Pattern) (guard : d1 p = 1) : d84 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1549 p hg
    simpa only [d84, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d84, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1551 (p : Pattern) (guard : d1 p = 1) : d85 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1550 p hg
    simpa only [d85, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d85, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1552 (p : Pattern) (guard : d1 p = 1) : d86 p ≤ (0 : Int) + d95 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d86, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1548 p hg
    simpa only [d86, d95, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d86, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1551 p hg
    simpa only [d86, d95, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1553 (p : Pattern) (guard : d1 p = 1) : d87 p ≤ (0 : Int) + d96 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d87, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1540 p hg
    simpa only [d87, d96, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d87, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1552 p hg
    simpa only [d87, d96, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1554 (p : Pattern) (guard : d1 p = 1) : d88 p ≤ (0 : Int) + d97 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d88, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1517 p hg
    simpa only [d88, d97, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d88, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1553 p hg
    simpa only [d88, d97, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1555 (p : Pattern) (guard : d0 p = 1) : d99 p ≤ (0 : Int) + d97 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1556 (p : Pattern) (guard : d4066 p = 1) : d100 p ≤ (0 : Int) + d97 p := by
  cases selected : p 116 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4066, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1554 p hg
    simpa only [d4066, d100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4066, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1555 p hg
    simpa only [d4066, d100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1557 (p : Pattern) (guard : d4103 p = 1) : d101 p ≤ (0 : Int) + d97 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4103, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1486 p hg
    simpa only [d4103, d101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4066 p = 1 := by simpa only [d4103, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1556 p hg
    simpa only [d4103, d101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1558 (p : Pattern) (guard : d0 p = 1) : d164 p ≤ (0 : Int) + d163 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1559 (p : Pattern) (guard : d1 p = 1) : d122 p ≤ (0 : Int) + d148 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d122, d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1405 p hg
    simpa only [d122, d148, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d122, d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1399 p hg
    simpa only [d122, d148, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1560 (p : Pattern) (guard : d1 p = 1) : d123 p ≤ (0 : Int) + d149 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d123, d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1398 p hg
    simpa only [d123, d149, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d123, d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1559 p hg
    simpa only [d123, d149, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1561 (p : Pattern) (guard : d1 p = 1) : d1 p ≤ (0 : Int) + d12 p := by
  change (1 : Int) ≤ (0 : Int) + 12
  decide
theorem compare1562 (p : Pattern) (guard : d1 p = 1) : d102 p ≤ (0 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1561 p hg
    simpa only [d102, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d102, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1563 (p : Pattern) (guard : d1 p = 1) : d103 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1561 p hg
    simpa only [d103, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1562 p hg
    simpa only [d103, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1564 (p : Pattern) (guard : d1 p = 1) : d124 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1563 p hg
    simpa only [d124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1565 (p : Pattern) (guard : d1 p = 1) : d126 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1564 p hg
    simpa only [d126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1328 p hg
    simpa only [d126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1566 (p : Pattern) (guard : d1 p = 1) : d127 p ≤ (0 : Int) + d150 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d127, d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1560 p hg
    simpa only [d127, d150, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d127, d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1565 p hg
    simpa only [d127, d150, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1567 (p : Pattern) (guard : d1 p = 1) : d129 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1565 p hg
    simpa only [d129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1292 p hg
    simpa only [d129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1568 (p : Pattern) (guard : d1 p = 1) : d130 p ≤ (0 : Int) + d151 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d130, d151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1566 p hg
    simpa only [d130, d151, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d130, d151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1567 p hg
    simpa only [d130, d151, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1569 (p : Pattern) (guard : d1 p = 1) : d131 p ≤ (0 : Int) + d152 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d131, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1396 p hg
    simpa only [d131, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d131, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1568 p hg
    simpa only [d131, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1570 (p : Pattern) (guard : d1 p = 1) : d138 p ≤ (0 : Int) + d138 p := by
  omega
theorem compare1571 (p : Pattern) (guard : d1 p = 1) : d3 p ≤ (0 : Int) + d12 p := by
  change (3 : Int) ≤ (0 : Int) + 12
  decide
theorem compare1572 (p : Pattern) (guard : d1 p = 1) : d115 p ≤ (0 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1571 p hg
    simpa only [d115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1573 (p : Pattern) (guard : d1 p = 1) : d116 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1571 p hg
    simpa only [d116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1572 p hg
    simpa only [d116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1574 (p : Pattern) (guard : d1 p = 1) : d139 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1573 p hg
    simpa only [d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1575 (p : Pattern) (guard : d1 p = 1) : d140 p ≤ (0 : Int) + d153 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d140, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1559 p hg
    simpa only [d140, d153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d140, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1574 p hg
    simpa only [d140, d153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1576 (p : Pattern) (guard : d1 p = 1) : d141 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1328 p hg
    simpa only [d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare816 p hg
    simpa only [d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1577 (p : Pattern) (guard : d1 p = 1) : d142 p ≤ (0 : Int) + d154 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d142, d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1575 p hg
    simpa only [d142, d154, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d142, d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1576 p hg
    simpa only [d142, d154, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1578 (p : Pattern) (guard : d1 p = 1) : d143 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1328 p hg
    simpa only [d143, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare744 p hg
    simpa only [d143, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1579 (p : Pattern) (guard : d1 p = 1) : d144 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1578 p hg
    simpa only [d144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1580 (p : Pattern) (guard : d1 p = 1) : d145 p ≤ (0 : Int) + d155 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d145, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1577 p hg
    simpa only [d145, d155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d145, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1579 p hg
    simpa only [d145, d155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1581 (p : Pattern) (guard : d1 p = 1) : d146 p ≤ (0 : Int) + d156 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d146, d156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1570 p hg
    simpa only [d146, d156, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d146, d156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1580 p hg
    simpa only [d146, d156, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1582 (p : Pattern) (guard : d1 p = 1) : d147 p ≤ (0 : Int) + d157 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d147, d157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1569 p hg
    simpa only [d147, d157, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d147, d157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1581 p hg
    simpa only [d147, d157, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1583 (p : Pattern) (guard : d1 p = 1) : d1 p ≤ (0 : Int) + d10 p := by
  change (1 : Int) ≤ (0 : Int) + 10
  decide
theorem compare1584 (p : Pattern) (guard : d1 p = 1) : d102 p ≤ (0 : Int) + d57 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d102, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1583 p hg
    simpa only [d102, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d102, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d102, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1585 (p : Pattern) (guard : d1 p = 1) : d103 p ≤ (0 : Int) + d58 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d103, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1583 p hg
    simpa only [d103, d58, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d103, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1584 p hg
    simpa only [d103, d58, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1586 (p : Pattern) (guard : d1 p = 1) : d104 p ≤ (0 : Int) + d59 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d104, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1585 p hg
    simpa only [d104, d59, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d104, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d104, d59, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1587 (p : Pattern) (guard : d1 p = 1) : d105 p ≤ (0 : Int) + d60 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d105, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1585 p hg
    simpa only [d105, d60, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d105, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1586 p hg
    simpa only [d105, d60, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1588 (p : Pattern) (guard : d1 p = 1) : d104 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1563 p hg
    simpa only [d104, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d104, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1589 (p : Pattern) (guard : d1 p = 1) : d105 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1563 p hg
    simpa only [d105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1588 p hg
    simpa only [d105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1590 (p : Pattern) (guard : d1 p = 1) : d105 p ≤ (0 : Int) + d112 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1587 p hg
    simpa only [d112, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1589 p hg
    simpa only [d112, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1591 (p : Pattern) (guard : d1 p = 1) : d110 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1589 p hg
    simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1323 p hg
    simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1592 (p : Pattern) (guard : d1 p = 1) : d111 p ≤ (0 : Int) + d159 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d111, d159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1590 p hg
    simpa only [d111, d159, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d111, d159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1591 p hg
    simpa only [d111, d159, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1593 (p : Pattern) (guard : d1 p = 1) : d113 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1591 p hg
    simpa only [d113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1271 p hg
    simpa only [d113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1594 (p : Pattern) (guard : d1 p = 1) : d114 p ≤ (0 : Int) + d160 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d114, d160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1592 p hg
    simpa only [d114, d160, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d114, d160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1593 p hg
    simpa only [d114, d160, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1595 (p : Pattern) (guard : d1 p = 1) : d117 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1573 p hg
    simpa only [d117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1596 (p : Pattern) (guard : d1 p = 1) : d132 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1573 p hg
    simpa only [d132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1595 p hg
    simpa only [d132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1597 (p : Pattern) (guard : d1 p = 1) : d149 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1596 p hg
    simpa only [d149, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1299 p hg
    simpa only [d149, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1598 (p : Pattern) (guard : d1 p = 1) : d150 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1597 p hg
    simpa only [d150, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d150, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1599 (p : Pattern) (guard : d1 p = 1) : d151 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1598 p hg
    simpa only [d151, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d151, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1600 (p : Pattern) (guard : d1 p = 1) : d152 p ≤ (0 : Int) + d161 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d152, d161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1594 p hg
    simpa only [d152, d161, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d152, d161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1599 p hg
    simpa only [d152, d161, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1601 (p : Pattern) (guard : d1 p = 1) : d133 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1589 p hg
    simpa only [d133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1596 p hg
    simpa only [d133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1602 (p : Pattern) (guard : d1 p = 1) : d134 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1323 p hg
    simpa only [d134, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare851 p hg
    simpa only [d134, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1603 (p : Pattern) (guard : d1 p = 1) : d135 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1601 p hg
    simpa only [d135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1602 p hg
    simpa only [d135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1604 (p : Pattern) (guard : d1 p = 1) : d136 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1323 p hg
    simpa only [d136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare734 p hg
    simpa only [d136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1605 (p : Pattern) (guard : d1 p = 1) : d137 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1604 p hg
    simpa only [d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1606 (p : Pattern) (guard : d1 p = 1) : d138 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1603 p hg
    simpa only [d138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1605 p hg
    simpa only [d138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1607 (p : Pattern) (guard : d1 p = 1) : d153 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1299 p hg
    simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1608 (p : Pattern) (guard : d1 p = 1) : d154 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1607 p hg
    simpa only [d154, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d154, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1609 (p : Pattern) (guard : d1 p = 1) : d155 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1608 p hg
    simpa only [d155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1610 (p : Pattern) (guard : d1 p = 1) : d156 p ≤ (0 : Int) + d12 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1606 p hg
    simpa only [d156, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1609 p hg
    simpa only [d156, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1611 (p : Pattern) (guard : d1 p = 1) : d157 p ≤ (0 : Int) + d162 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d157, d162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1600 p hg
    simpa only [d157, d162, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d157, d162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1610 p hg
    simpa only [d157, d162, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1612 (p : Pattern) (guard : d1 p = 1) : d158 p ≤ (0 : Int) + d163 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d158, d163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1582 p hg
    simpa only [d158, d163, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d158, d163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1611 p hg
    simpa only [d158, d163, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1613 (p : Pattern) (guard : d0 p = 1) : d165 p ≤ (0 : Int) + d163 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1614 (p : Pattern) (guard : d4066 p = 1) : d166 p ≤ (0 : Int) + d163 p := by
  cases selected : p 116 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4066, d166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1612 p hg
    simpa only [d4066, d166, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4066, d166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1613 p hg
    simpa only [d4066, d166, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1615 (p : Pattern) (guard : d4103 p = 1) : d167 p ≤ (0 : Int) + d163 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4103, d167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1558 p hg
    simpa only [d4103, d167, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4066 p = 1 := by simpa only [d4103, d167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1614 p hg
    simpa only [d4103, d167, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1616 (p : Pattern) (guard : d4103 p = 1) : d168 p ≤ (0 : Int) + d4104 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4103 p = 1 := by simpa only [d168, d4104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1557 p hg
    simpa only [d168, d4104, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4103 p = 1 := by simpa only [d168, d4104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1615 p hg
    simpa only [d168, d4104, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1617 (p : Pattern) (guard : d4103 p = 1) : d169 p ≤ (0 : Int) + d4105 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4103 p = 1 := by simpa only [d169, d4105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1557 p hg
    simpa only [d169, d4105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4103 p = 1 := by simpa only [d169, d4105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1616 p hg
    simpa only [d169, d4105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1618 (p : Pattern) (guard : d1 p = 1) : d170 p ≤ (0 : Int) + d78 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d170, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1210 p hg
    simpa only [d170, d78, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d170, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare784 p hg
    simpa only [d170, d78, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1619 (p : Pattern) (guard : d1 p = 1) : d171 p ≤ (0 : Int) + d79 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d171, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare845 p hg
    simpa only [d171, d79, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d171, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1618 p hg
    simpa only [d171, d79, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1620 (p : Pattern) (guard : d1 p = 1) : d172 p ≤ (0 : Int) + d62 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d172, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1534 p hg
    simpa only [d172, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d172, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare787 p hg
    simpa only [d172, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1621 (p : Pattern) (guard : d1 p = 1) : d173 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare957 p hg
    simpa only [d173, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d173, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1622 (p : Pattern) (guard : d1 p = 1) : d174 p ≤ (0 : Int) + d63 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d174, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1620 p hg
    simpa only [d174, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d174, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1621 p hg
    simpa only [d174, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1623 (p : Pattern) (guard : d1 p = 1) : d175 p ≤ (0 : Int) + d80 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d175, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1619 p hg
    simpa only [d175, d80, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d175, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1622 p hg
    simpa only [d175, d80, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1624 (p : Pattern) (guard : d1 p = 1) : d176 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1509 p hg
    simpa only [d176, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1621 p hg
    simpa only [d176, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1625 (p : Pattern) (guard : d1 p = 1) : d177 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1624 p hg
    simpa only [d177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare745 p hg
    simpa only [d177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1626 (p : Pattern) (guard : d1 p = 1) : d178 p ≤ (0 : Int) + d81 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d178, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1623 p hg
    simpa only [d178, d81, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d178, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1625 p hg
    simpa only [d178, d81, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1627 (p : Pattern) (guard : d1 p = 1) : d179 p ≤ (0 : Int) + d82 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d179, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare778 p hg
    simpa only [d179, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d179, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1626 p hg
    simpa only [d179, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1628 (p : Pattern) (guard : d1 p = 1) : d180 p ≤ (0 : Int) + d83 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d180, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1618 p hg
    simpa only [d180, d83, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d180, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare902 p hg
    simpa only [d180, d83, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1629 (p : Pattern) (guard : d1 p = 1) : d181 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1621 p hg
    simpa only [d181, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare744 p hg
    simpa only [d181, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1630 (p : Pattern) (guard : d1 p = 1) : d182 p ≤ (0 : Int) + d84 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d182, d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1628 p hg
    simpa only [d182, d84, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d182, d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1629 p hg
    simpa only [d182, d84, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1631 (p : Pattern) (guard : d1 p = 1) : d183 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1621 p hg
    simpa only [d183, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d183, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1632 (p : Pattern) (guard : d1 p = 1) : d184 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1631 p hg
    simpa only [d184, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d184, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1633 (p : Pattern) (guard : d1 p = 1) : d185 p ≤ (0 : Int) + d85 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d185, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1630 p hg
    simpa only [d185, d85, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d185, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1632 p hg
    simpa only [d185, d85, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1634 (p : Pattern) (guard : d1 p = 1) : d186 p ≤ (0 : Int) + d86 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d186, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare805 p hg
    simpa only [d186, d86, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d186, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1633 p hg
    simpa only [d186, d86, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1635 (p : Pattern) (guard : d1 p = 1) : d187 p ≤ (0 : Int) + d87 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d187, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1627 p hg
    simpa only [d187, d87, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d187, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1634 p hg
    simpa only [d187, d87, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1636 (p : Pattern) (guard : d1 p = 1) : d188 p ≤ (0 : Int) + d90 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d188, d90, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1525 p hg
    simpa only [d188, d90, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d188, d90, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1537 p hg
    simpa only [d188, d90, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1637 (p : Pattern) (guard : d1 p = 1) : d189 p ≤ (0 : Int) + d92 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d189, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1636 p hg
    simpa only [d189, d92, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d189, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1538 p hg
    simpa only [d189, d92, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1638 (p : Pattern) (guard : d1 p = 1) : d8 p ≤ (0 : Int) + d12 p := by
  change (8 : Int) ≤ (0 : Int) + 12
  decide
theorem compare1639 (p : Pattern) (guard : d1 p = 1) : d190 p ≤ (0 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1638 p hg
    simpa only [d190, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d190, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1640 (p : Pattern) (guard : d1 p = 1) : d191 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1638 p hg
    simpa only [d191, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1639 p hg
    simpa only [d191, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1641 (p : Pattern) (guard : d1 p = 1) : d192 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1640 p hg
    simpa only [d192, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d192, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1642 (p : Pattern) (guard : d1 p = 1) : d193 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1640 p hg
    simpa only [d193, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1641 p hg
    simpa only [d193, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1643 (p : Pattern) (guard : d1 p = 1) : d194 p ≤ (0 : Int) + d63 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d194, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare941 p hg
    simpa only [d194, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d194, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1642 p hg
    simpa only [d194, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1644 (p : Pattern) (guard : d1 p = 1) : d195 p ≤ (0 : Int) + d91 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d195, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1643 p hg
    simpa only [d195, d91, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d195, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d195, d91, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1645 (p : Pattern) (guard : d1 p = 1) : d196 p ≤ (0 : Int) + d93 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d196, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1644 p hg
    simpa only [d196, d93, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d196, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d196, d93, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1646 (p : Pattern) (guard : d1 p = 1) : d197 p ≤ (0 : Int) + d94 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d197, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1637 p hg
    simpa only [d197, d94, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d197, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1645 p hg
    simpa only [d197, d94, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1647 (p : Pattern) (guard : d1 p = 1) : d53 p ≤ (0 : Int) + d63 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1536 p hg
    simpa only [d63, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1542 p hg
    simpa only [d63, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1648 (p : Pattern) (guard : d1 p = 1) : d198 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1527 p hg
    simpa only [d198, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare734 p hg
    simpa only [d198, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1649 (p : Pattern) (guard : d1 p = 1) : d199 p ≤ (0 : Int) + d91 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d199, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1647 p hg
    simpa only [d199, d91, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d199, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1648 p hg
    simpa only [d199, d91, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1650 (p : Pattern) (guard : d1 p = 1) : d200 p ≤ (0 : Int) + d93 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d200, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1649 p hg
    simpa only [d200, d93, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d200, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1550 p hg
    simpa only [d200, d93, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1651 (p : Pattern) (guard : d1 p = 1) : d201 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1642 p hg
    simpa only [d201, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d201, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1652 (p : Pattern) (guard : d1 p = 1) : d202 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1651 p hg
    simpa only [d202, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d202, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1653 (p : Pattern) (guard : d1 p = 1) : d203 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1652 p hg
    simpa only [d203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1654 (p : Pattern) (guard : d1 p = 1) : d204 p ≤ (0 : Int) + d95 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d204, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1650 p hg
    simpa only [d204, d95, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d204, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1653 p hg
    simpa only [d204, d95, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1655 (p : Pattern) (guard : d1 p = 1) : d205 p ≤ (0 : Int) + d96 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d205, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1646 p hg
    simpa only [d205, d96, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d205, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1654 p hg
    simpa only [d205, d96, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1656 (p : Pattern) (guard : d1 p = 1) : d206 p ≤ (0 : Int) + d97 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d206, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1635 p hg
    simpa only [d206, d97, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d206, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1655 p hg
    simpa only [d206, d97, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1657 (p : Pattern) (guard : d0 p = 1) : d207 p ≤ (0 : Int) + d97 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1658 (p : Pattern) (guard : d4066 p = 1) : d208 p ≤ (0 : Int) + d97 p := by
  cases selected : p 116 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4066, d208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1656 p hg
    simpa only [d4066, d208, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4066, d208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1657 p hg
    simpa only [d4066, d208, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1659 (p : Pattern) (guard : d4103 p = 1) : d209 p ≤ (0 : Int) + d97 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4103, d209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1486 p hg
    simpa only [d4103, d209, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4066 p = 1 := by simpa only [d4103, d209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1658 p hg
    simpa only [d4103, d209, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1660 (p : Pattern) (guard : d4103 p = 1) : d210 p ≤ (0 : Int) + d97 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4103 p = 1 := by simpa only [d210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1557 p hg
    simpa only [d210, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4103 p = 1 := by simpa only [d210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1659 p hg
    simpa only [d210, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1661 (p : Pattern) (guard : d0 p = 1) : d225 p ≤ (0 : Int) + d224 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1662 (p : Pattern) (guard : d1 p = 1) : d226 p ≤ (0 : Int) + d148 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d226, d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1277 p hg
    simpa only [d226, d148, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d226, d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1399 p hg
    simpa only [d226, d148, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1663 (p : Pattern) (guard : d1 p = 1) : d227 p ≤ (0 : Int) + d149 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d227, d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1434 p hg
    simpa only [d227, d149, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d227, d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1662 p hg
    simpa only [d227, d149, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1664 (p : Pattern) (guard : d1 p = 1) : d215 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1328 p hg
    simpa only [d215, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d215, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1665 (p : Pattern) (guard : d1 p = 1) : d228 p ≤ (0 : Int) + d150 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d228, d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1663 p hg
    simpa only [d228, d150, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d228, d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1664 p hg
    simpa only [d228, d150, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1666 (p : Pattern) (guard : d1 p = 1) : d229 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1282 p hg
    simpa only [d229, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d229, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1667 (p : Pattern) (guard : d1 p = 1) : d230 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1666 p hg
    simpa only [d230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1668 (p : Pattern) (guard : d1 p = 1) : d231 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1667 p hg
    simpa only [d231, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d231, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1669 (p : Pattern) (guard : d1 p = 1) : d232 p ≤ (0 : Int) + d151 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d232, d151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1665 p hg
    simpa only [d232, d151, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d232, d151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1668 p hg
    simpa only [d232, d151, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1670 (p : Pattern) (guard : d1 p = 1) : d233 p ≤ (0 : Int) + d152 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d233, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1396 p hg
    simpa only [d233, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d233, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1669 p hg
    simpa only [d233, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1671 (p : Pattern) (guard : d1 p = 1) : d234 p ≤ (0 : Int) + d148 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d234, d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1417 p hg
    simpa only [d234, d148, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d234, d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1399 p hg
    simpa only [d234, d148, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1672 (p : Pattern) (guard : d1 p = 1) : d235 p ≤ (0 : Int) + d153 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d235, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1671 p hg
    simpa only [d235, d153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d235, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1328 p hg
    simpa only [d235, d153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1673 (p : Pattern) (guard : d1 p = 1) : d236 p ≤ (0 : Int) + d154 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d236, d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1672 p hg
    simpa only [d236, d154, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d236, d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1667 p hg
    simpa only [d236, d154, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1674 (p : Pattern) (guard : d1 p = 1) : d237 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare910 p hg
    simpa only [d237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1675 (p : Pattern) (guard : d1 p = 1) : d238 p ≤ (0 : Int) + d155 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d238, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1673 p hg
    simpa only [d238, d155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d238, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1674 p hg
    simpa only [d238, d155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1676 (p : Pattern) (guard : d1 p = 1) : d239 p ≤ (0 : Int) + d221 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d239, d221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1411 p hg
    simpa only [d239, d221, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d239, d221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1675 p hg
    simpa only [d239, d221, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1677 (p : Pattern) (guard : d1 p = 1) : d240 p ≤ (0 : Int) + d222 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d240, d222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1670 p hg
    simpa only [d240, d222, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d240, d222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1676 p hg
    simpa only [d240, d222, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1678 (p : Pattern) (guard : d1 p = 1) : d241 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1596 p hg
    simpa only [d241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare734 p hg
    simpa only [d241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1679 (p : Pattern) (guard : d1 p = 1) : d242 p ≤ (0 : Int) + d159 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d242, d159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1590 p hg
    simpa only [d242, d159, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d242, d159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1678 p hg
    simpa only [d242, d159, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
