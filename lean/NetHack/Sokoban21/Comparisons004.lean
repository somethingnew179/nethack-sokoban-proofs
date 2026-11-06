/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons003
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c560 (pattern : Twelve) (guard : d1839 pattern = 1) : d1314 pattern ≤ (0 : Int) + d1419 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d1314, d1419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c556 pattern childGuard
    simpa only [d1314, d1419, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d1314, d1419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c559 pattern childGuard
    simpa only [d1314, d1419, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c561 (pattern : Twelve) (guard : d1839 pattern = 1) : d1315 pattern ≤ (0 : Int) + d1420 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d1315, d1420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c548 pattern childGuard
    simpa only [d1315, d1420, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d1315, d1420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c445 pattern childGuard
    simpa only [d1315, d1420, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c562 (pattern : Twelve) (guard : d1839 pattern = 1) : d1319 pattern ≤ (0 : Int) + d1422 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d1319, d1422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c560 pattern childGuard
    simpa only [d1319, d1422, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d1319, d1422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c561 pattern childGuard
    simpa only [d1319, d1422, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c563 (pattern : Twelve) (guard : d1839 pattern = 1) : d1321 pattern ≤ (0 : Int) + d1423 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d1321, d1423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c553 pattern childGuard
    simpa only [d1321, d1423, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d1321, d1423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c562 pattern childGuard
    simpa only [d1321, d1423, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c564 (pattern : Twelve) (guard : d0 pattern = 1) : d1301 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c565 (pattern : Twelve) (guard : d1839 pattern = 1) : d1309 pattern ≤ (0 : Int) + d1414 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1839, d1309, d1414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c543 pattern childGuard
    simpa only [d1839, d1309, d1414, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1839, d1309, d1414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c564 pattern childGuard
    simpa only [d1839, d1309, d1414, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c566 (pattern : Twelve) (guard : d0 pattern = 1) : d1302 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c567 (pattern : Twelve) (guard : d1839 pattern = 1) : d1310 pattern ≤ (0 : Int) + d1413 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1839, d1310, d1413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c546 pattern childGuard
    simpa only [d1839, d1310, d1413, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1839, d1310, d1413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c566 pattern childGuard
    simpa only [d1839, d1310, d1413, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c568 (pattern : Twelve) (guard : d1839 pattern = 1) : d1316 pattern ≤ (0 : Int) + d1418 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d1316, d1418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c565 pattern childGuard
    simpa only [d1316, d1418, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d1316, d1418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c567 pattern childGuard
    simpa only [d1316, d1418, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c569 (pattern : Twelve) (guard : d0 pattern = 1) : d1303 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c570 (pattern : Twelve) (guard : d1839 pattern = 1) : d1311 pattern ≤ (0 : Int) + d1415 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1839, d1311, d1415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c554 pattern childGuard
    simpa only [d1839, d1311, d1415, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1839, d1311, d1415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c569 pattern childGuard
    simpa only [d1839, d1311, d1415, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c571 (pattern : Twelve) (guard : d0 pattern = 1) : d1304 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c572 (pattern : Twelve) (guard : d1839 pattern = 1) : d1312 pattern ≤ (0 : Int) + d1416 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1839, d1312, d1416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c557 pattern childGuard
    simpa only [d1839, d1312, d1416, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1839, d1312, d1416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c571 pattern childGuard
    simpa only [d1839, d1312, d1416, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c573 (pattern : Twelve) (guard : d1839 pattern = 1) : d1317 pattern ≤ (0 : Int) + d1419 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d1317, d1419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c570 pattern childGuard
    simpa only [d1317, d1419, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d1317, d1419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c572 pattern childGuard
    simpa only [d1317, d1419, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c574 (pattern : Twelve) (guard : d1839 pattern = 1) : d1318 pattern ≤ (0 : Int) + d1420 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d1318, d1420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c567 pattern childGuard
    simpa only [d1318, d1420, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d1318, d1420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c445 pattern childGuard
    simpa only [d1318, d1420, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c575 (pattern : Twelve) (guard : d1839 pattern = 1) : d1320 pattern ≤ (0 : Int) + d1422 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d1320, d1422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c573 pattern childGuard
    simpa only [d1320, d1422, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d1320, d1422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c574 pattern childGuard
    simpa only [d1320, d1422, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c576 (pattern : Twelve) (guard : d1839 pattern = 1) : d1322 pattern ≤ (0 : Int) + d1424 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d1322, d1424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c568 pattern childGuard
    simpa only [d1322, d1424, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d1322, d1424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c575 pattern childGuard
    simpa only [d1322, d1424, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c577 (pattern : Twelve) (guard : d1839 pattern = 1) : d1323 pattern ≤ (0 : Int) + d1425 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d1323, d1425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c563 pattern childGuard
    simpa only [d1323, d1425, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d1323, d1425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c576 pattern childGuard
    simpa only [d1323, d1425, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c578 (pattern : Twelve) (guard : d1839 pattern = 1) : d1321 pattern ≤ (0 : Int) + d1424 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d1321, d1424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c552 pattern childGuard
    simpa only [d1321, d1424, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d1321, d1424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c562 pattern childGuard
    simpa only [d1321, d1424, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c579 (pattern : Twelve) (guard : d1839 pattern = 1) : d1323 pattern ≤ (0 : Int) + d1424 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d1323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c578 pattern childGuard
    simpa only [d1323, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d1323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c576 pattern childGuard
    simpa only [d1323, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c580 (pattern : Twelve) (guard : d1839 pattern = 1) : d1323 pattern ≤ (0 : Int) + d1426 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d1426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c577 pattern childGuard
    simpa only [d1426, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d1426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c579 pattern childGuard
    simpa only [d1426, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c581 (pattern : Twelve) (guard : d1839 pattern = 1) : d1323 pattern ≤ (0 : Int) + d1427 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d1427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c580 pattern childGuard
    simpa only [d1427, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d1427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c579 pattern childGuard
    simpa only [d1427, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c582 (pattern : Twelve) (guard : d1 pattern = 1) : d1649 pattern ≤ (0 : Int) + d1649 pattern := by
  omega
theorem c583 (pattern : Twelve) (guard : d0 pattern = 1) : d1650 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c584 (pattern : Twelve) (guard : d1839 pattern = 1) : d1656 pattern ≤ (0 : Int) + d1705 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1839, d1656, d1705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c582 pattern childGuard
    simpa only [d1839, d1656, d1705, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1839, d1656, d1705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c583 pattern childGuard
    simpa only [d1839, d1656, d1705, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c585 (pattern : Twelve) (guard : d1 pattern = 1) : d1651 pattern ≤ (0 : Int) + d1651 pattern := by
  omega
theorem c586 (pattern : Twelve) (guard : d1839 pattern = 1) : d1657 pattern ≤ (0 : Int) + d1706 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1839, d1657, d1706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c585 pattern childGuard
    simpa only [d1839, d1657, d1706, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1839, d1657, d1706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c558 pattern childGuard
    simpa only [d1839, d1657, d1706, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c587 (pattern : Twelve) (guard : d1839 pattern = 1) : d1660 pattern ≤ (0 : Int) + d1709 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d1660, d1709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c584 pattern childGuard
    simpa only [d1660, d1709, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d1660, d1709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c586 pattern childGuard
    simpa only [d1660, d1709, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c588 (pattern : Twelve) (guard : d1 pattern = 1) : d1652 pattern ≤ (0 : Int) + d1652 pattern := by
  omega
theorem c589 (pattern : Twelve) (guard : d0 pattern = 1) : d1653 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c590 (pattern : Twelve) (guard : d1839 pattern = 1) : d1658 pattern ≤ (0 : Int) + d1707 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1839, d1658, d1707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c588 pattern childGuard
    simpa only [d1839, d1658, d1707, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1839, d1658, d1707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c589 pattern childGuard
    simpa only [d1839, d1658, d1707, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c591 (pattern : Twelve) (guard : d1 pattern = 1) : d1654 pattern ≤ (0 : Int) + d1654 pattern := by
  omega
theorem c592 (pattern : Twelve) (guard : d0 pattern = 1) : d1655 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c593 (pattern : Twelve) (guard : d1839 pattern = 1) : d1659 pattern ≤ (0 : Int) + d1708 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1839, d1659, d1708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c591 pattern childGuard
    simpa only [d1839, d1659, d1708, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1839, d1659, d1708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c592 pattern childGuard
    simpa only [d1839, d1659, d1708, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c594 (pattern : Twelve) (guard : d1839 pattern = 1) : d1661 pattern ≤ (0 : Int) + d1710 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d1661, d1710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c590 pattern childGuard
    simpa only [d1661, d1710, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d1661, d1710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c593 pattern childGuard
    simpa only [d1661, d1710, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c595 (pattern : Twelve) (guard : d1839 pattern = 1) : d1662 pattern ≤ (0 : Int) + d1711 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d1662, d1711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c586 pattern childGuard
    simpa only [d1662, d1711, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d1662, d1711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c445 pattern childGuard
    simpa only [d1662, d1711, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c596 (pattern : Twelve) (guard : d1839 pattern = 1) : d1663 pattern ≤ (0 : Int) + d1712 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d1663, d1712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c594 pattern childGuard
    simpa only [d1663, d1712, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d1663, d1712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c595 pattern childGuard
    simpa only [d1663, d1712, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c597 (pattern : Twelve) (guard : d1839 pattern = 1) : d1664 pattern ≤ (0 : Int) + d1713 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d1664, d1713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c587 pattern childGuard
    simpa only [d1664, d1713, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d1664, d1713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c596 pattern childGuard
    simpa only [d1664, d1713, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c598 (pattern : Twelve) (guard : d1 pattern = 1) : d156 pattern ≤ (0 : Int) + d156 pattern := by
  omega
theorem c599 (pattern : Twelve) (guard : d1 pattern = 1) : d907 pattern ≤ (0 : Int) + d907 pattern := by
  omega
theorem c600 (pattern : Twelve) (guard : d1 pattern = 1) : d1354 pattern ≤ (0 : Int) + d1354 pattern := by
  omega
theorem c601 (pattern : Twelve) (guard : d1 pattern = 1) : d1678 pattern ≤ (0 : Int) + d1678 pattern := by
  omega
theorem c602 (pattern : Twelve) (guard : d1 pattern = 1) : d221 pattern ≤ (0 : Int) + d221 pattern := by
  omega
theorem c603 (pattern : Twelve) (guard : d1 pattern = 1) : d926 pattern ≤ (0 : Int) + d926 pattern := by
  omega
theorem c604 (pattern : Twelve) (guard : d1 pattern = 1) : d1367 pattern ≤ (0 : Int) + d1367 pattern := by
  omega
theorem c605 (pattern : Twelve) (guard : d1 pattern = 1) : d1685 pattern ≤ (0 : Int) + d1685 pattern := by
  omega
theorem c606 (pattern : Twelve) (guard : d1 pattern = 1) : d110 pattern ≤ (0 : Int) + d110 pattern := by
  omega
theorem c607 (pattern : Twelve) (guard : d0 pattern = 1) : d111 pattern ≤ (0 : Int) + d217 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c608 (pattern : Twelve) (guard : d1841 pattern = 1) : d114 pattern ≤ (0 : Int) + d345 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1841, d114, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c606 pattern childGuard
    simpa only [d1841, d114, d345, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1841, d114, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c607 pattern childGuard
    simpa only [d1841, d114, d345, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c609 (pattern : Twelve) (guard : d1 pattern = 1) : d112 pattern ≤ (0 : Int) + d112 pattern := by
  omega
theorem c610 (pattern : Twelve) (guard : d0 pattern = 1) : d113 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c611 (pattern : Twelve) (guard : d1841 pattern = 1) : d115 pattern ≤ (0 : Int) + d346 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1841, d115, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c609 pattern childGuard
    simpa only [d1841, d115, d346, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1841, d115, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c610 pattern childGuard
    simpa only [d1841, d115, d346, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c612 (pattern : Twelve) (guard : d1841 pattern = 1) : d116 pattern ≤ (0 : Int) + d348 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1841 pattern = 1 := by simpa only [d116, d348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c608 pattern childGuard
    simpa only [d116, d348, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1841 pattern = 1 := by simpa only [d116, d348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c611 pattern childGuard
    simpa only [d116, d348, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c613 (pattern : Twelve) (guard : d0 pattern = 1) : d111 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c614 (pattern : Twelve) (guard : d1841 pattern = 1) : d114 pattern ≤ (0 : Int) + d347 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1841, d114, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c606 pattern childGuard
    simpa only [d1841, d114, d347, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1841, d114, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c613 pattern childGuard
    simpa only [d1841, d114, d347, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c615 (pattern : Twelve) (guard : d1841 pattern = 1) : d116 pattern ≤ (0 : Int) + d349 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1841 pattern = 1 := by simpa only [d116, d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c614 pattern childGuard
    simpa only [d116, d349, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1841 pattern = 1 := by simpa only [d116, d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c611 pattern childGuard
    simpa only [d116, d349, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c616 (pattern : Twelve) (guard : d1841 pattern = 1) : d116 pattern ≤ (0 : Int) + d350 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1841 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c612 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1841 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c615 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c617 (pattern : Twelve) (guard : d1841 pattern = 1) : d116 pattern ≤ (0 : Int) + d351 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1841 pattern = 1 := by simpa only [d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c616 pattern childGuard
    simpa only [d351, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1841 pattern = 1 := by simpa only [d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c615 pattern childGuard
    simpa only [d351, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c618 (pattern : Twelve) (guard : d0 pattern = 1) : d867 pattern ≤ (0 : Int) + d922 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c619 (pattern : Twelve) (guard : d1841 pattern = 1) : d869 pattern ≤ (0 : Int) + d1011 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1841, d869, d1011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c27 pattern childGuard
    simpa only [d1841, d869, d1011, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1841, d869, d1011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c618 pattern childGuard
    simpa only [d1841, d869, d1011, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c620 (pattern : Twelve) (guard : d0 pattern = 1) : d868 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c621 (pattern : Twelve) (guard : d1841 pattern = 1) : d870 pattern ≤ (0 : Int) + d1012 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1841, d870, d1012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c34 pattern childGuard
    simpa only [d1841, d870, d1012, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1841, d870, d1012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c620 pattern childGuard
    simpa only [d1841, d870, d1012, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c622 (pattern : Twelve) (guard : d1841 pattern = 1) : d871 pattern ≤ (0 : Int) + d1014 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1841 pattern = 1 := by simpa only [d871, d1014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c619 pattern childGuard
    simpa only [d871, d1014, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1841 pattern = 1 := by simpa only [d871, d1014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c621 pattern childGuard
    simpa only [d871, d1014, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c623 (pattern : Twelve) (guard : d0 pattern = 1) : d867 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c624 (pattern : Twelve) (guard : d1841 pattern = 1) : d869 pattern ≤ (0 : Int) + d1013 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1841, d869, d1013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c27 pattern childGuard
    simpa only [d1841, d869, d1013, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1841, d869, d1013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c623 pattern childGuard
    simpa only [d1841, d869, d1013, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c625 (pattern : Twelve) (guard : d1841 pattern = 1) : d871 pattern ≤ (0 : Int) + d1015 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1841 pattern = 1 := by simpa only [d871, d1015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c624 pattern childGuard
    simpa only [d871, d1015, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1841 pattern = 1 := by simpa only [d871, d1015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c621 pattern childGuard
    simpa only [d871, d1015, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c626 (pattern : Twelve) (guard : d1841 pattern = 1) : d871 pattern ≤ (0 : Int) + d1016 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1841 pattern = 1 := by simpa only [d1016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c622 pattern childGuard
    simpa only [d1016, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1841 pattern = 1 := by simpa only [d1016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c625 pattern childGuard
    simpa only [d1016, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c627 (pattern : Twelve) (guard : d1841 pattern = 1) : d871 pattern ≤ (0 : Int) + d1017 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1841 pattern = 1 := by simpa only [d1017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c626 pattern childGuard
    simpa only [d1017, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1841 pattern = 1 := by simpa only [d1017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c625 pattern childGuard
    simpa only [d1017, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c628 (pattern : Twelve) (guard : d0 pattern = 1) : d1319 pattern ≤ (0 : Int) + d1363 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c629 (pattern : Twelve) (guard : d1841 pattern = 1) : d1321 pattern ≤ (0 : Int) + d1428 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1841, d1321, d1428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c50 pattern childGuard
    simpa only [d1841, d1321, d1428, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1841, d1321, d1428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c628 pattern childGuard
    simpa only [d1841, d1321, d1428, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c630 (pattern : Twelve) (guard : d0 pattern = 1) : d1320 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c631 (pattern : Twelve) (guard : d1841 pattern = 1) : d1322 pattern ≤ (0 : Int) + d1429 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1841, d1322, d1429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c57 pattern childGuard
    simpa only [d1841, d1322, d1429, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1841, d1322, d1429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c630 pattern childGuard
    simpa only [d1841, d1322, d1429, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c632 (pattern : Twelve) (guard : d1841 pattern = 1) : d1323 pattern ≤ (0 : Int) + d1431 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1841 pattern = 1 := by simpa only [d1323, d1431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c629 pattern childGuard
    simpa only [d1323, d1431, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1841 pattern = 1 := by simpa only [d1323, d1431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c631 pattern childGuard
    simpa only [d1323, d1431, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c633 (pattern : Twelve) (guard : d0 pattern = 1) : d1319 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c634 (pattern : Twelve) (guard : d1841 pattern = 1) : d1321 pattern ≤ (0 : Int) + d1430 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1841, d1321, d1430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c50 pattern childGuard
    simpa only [d1841, d1321, d1430, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1841, d1321, d1430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c633 pattern childGuard
    simpa only [d1841, d1321, d1430, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c635 (pattern : Twelve) (guard : d1841 pattern = 1) : d1323 pattern ≤ (0 : Int) + d1432 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1841 pattern = 1 := by simpa only [d1323, d1432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c634 pattern childGuard
    simpa only [d1323, d1432, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1841 pattern = 1 := by simpa only [d1323, d1432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c631 pattern childGuard
    simpa only [d1323, d1432, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c636 (pattern : Twelve) (guard : d1841 pattern = 1) : d1323 pattern ≤ (0 : Int) + d1433 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1841 pattern = 1 := by simpa only [d1433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c632 pattern childGuard
    simpa only [d1433, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1841 pattern = 1 := by simpa only [d1433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c635 pattern childGuard
    simpa only [d1433, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c637 (pattern : Twelve) (guard : d1841 pattern = 1) : d1323 pattern ≤ (0 : Int) + d1434 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1841 pattern = 1 := by simpa only [d1434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c636 pattern childGuard
    simpa only [d1434, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1841 pattern = 1 := by simpa only [d1434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c635 pattern childGuard
    simpa only [d1434, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c638 (pattern : Twelve) (guard : d0 pattern = 1) : d1663 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c639 (pattern : Twelve) (guard : d1841 pattern = 1) : d1664 pattern ≤ (0 : Int) + d1714 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1841, d1664, d1714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c71 pattern childGuard
    simpa only [d1841, d1664, d1714, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1841, d1664, d1714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c638 pattern childGuard
    simpa only [d1841, d1664, d1714, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c640 (pattern : Twelve) (guard : d0 pattern = 1) : d213 pattern ≤ (0 : Int) + d103 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c641 (pattern : Twelve) (guard : d1835 pattern = 1) : d222 pattern ≤ (0 : Int) + d110 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1835, d222, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4 pattern childGuard
    simpa only [d1835, d222, d110, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1835, d222, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c640 pattern childGuard
    simpa only [d1835, d222, d110, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c642 (pattern : Twelve) (guard : d0 pattern = 1) : d215 pattern ≤ (0 : Int) + d105 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c643 (pattern : Twelve) (guard : d1835 pattern = 1) : d223 pattern ≤ (0 : Int) + d111 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1835, d223, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7 pattern childGuard
    simpa only [d1835, d223, d111, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1835, d223, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c642 pattern childGuard
    simpa only [d1835, d223, d111, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c644 (pattern : Twelve) (guard : d1835 pattern = 1) : d228 pattern ≤ (0 : Int) + d114 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1835 pattern = 1 := by simpa only [d228, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c641 pattern childGuard
    simpa only [d228, d114, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1835 pattern = 1 := by simpa only [d228, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c643 pattern childGuard
    simpa only [d228, d114, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c645 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d107 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c646 (pattern : Twelve) (guard : d1835 pattern = 1) : d224 pattern ≤ (0 : Int) + d112 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1835, d224, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11 pattern childGuard
    simpa only [d1835, d224, d112, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1835, d224, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c645 pattern childGuard
    simpa only [d1835, d224, d112, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c647 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d109 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c648 (pattern : Twelve) (guard : d1835 pattern = 1) : d225 pattern ≤ (0 : Int) + d113 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1835, d225, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14 pattern childGuard
    simpa only [d1835, d225, d113, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1835, d225, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c647 pattern childGuard
    simpa only [d1835, d225, d113, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c649 (pattern : Twelve) (guard : d1835 pattern = 1) : d229 pattern ≤ (0 : Int) + d115 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1835 pattern = 1 := by simpa only [d229, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c646 pattern childGuard
    simpa only [d229, d115, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1835 pattern = 1 := by simpa only [d229, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c648 pattern childGuard
    simpa only [d229, d115, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c650 (pattern : Twelve) (guard : d1835 pattern = 1) : d231 pattern ≤ (0 : Int) + d116 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1835 pattern = 1 := by simpa only [d231, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c644 pattern childGuard
    simpa only [d231, d116, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1835 pattern = 1 := by simpa only [d231, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c649 pattern childGuard
    simpa only [d231, d116, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c651 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d103 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c652 (pattern : Twelve) (guard : d1835 pattern = 1) : d226 pattern ≤ (0 : Int) + d110 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1835, d226, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4 pattern childGuard
    simpa only [d1835, d226, d110, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1835, d226, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c651 pattern childGuard
    simpa only [d1835, d226, d110, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c653 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d105 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c654 (pattern : Twelve) (guard : d1835 pattern = 1) : d227 pattern ≤ (0 : Int) + d111 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1835, d227, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7 pattern childGuard
    simpa only [d1835, d227, d111, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1835, d227, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c653 pattern childGuard
    simpa only [d1835, d227, d111, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c655 (pattern : Twelve) (guard : d1835 pattern = 1) : d230 pattern ≤ (0 : Int) + d114 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1835 pattern = 1 := by simpa only [d230, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c652 pattern childGuard
    simpa only [d230, d114, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1835 pattern = 1 := by simpa only [d230, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c654 pattern childGuard
    simpa only [d230, d114, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c656 (pattern : Twelve) (guard : d1835 pattern = 1) : d232 pattern ≤ (0 : Int) + d116 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1835 pattern = 1 := by simpa only [d232, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c655 pattern childGuard
    simpa only [d232, d116, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1835 pattern = 1 := by simpa only [d232, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c649 pattern childGuard
    simpa only [d232, d116, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c657 (pattern : Twelve) (guard : d1835 pattern = 1) : d233 pattern ≤ (0 : Int) + d116 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1835 pattern = 1 := by simpa only [d233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c650 pattern childGuard
    simpa only [d233, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1835 pattern = 1 := by simpa only [d233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c656 pattern childGuard
    simpa only [d233, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c658 (pattern : Twelve) (guard : d1835 pattern = 1) : d234 pattern ≤ (0 : Int) + d116 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1835 pattern = 1 := by simpa only [d234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c657 pattern childGuard
    simpa only [d234, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1835 pattern = 1 := by simpa only [d234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c656 pattern childGuard
    simpa only [d234, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c659 (pattern : Twelve) (guard : d0 pattern = 1) : d918 pattern ≤ (0 : Int) + d861 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c660 (pattern : Twelve) (guard : d1835 pattern = 1) : d927 pattern ≤ (0 : Int) + d861 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1835, d927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c27 pattern childGuard
    simpa only [d1835, d927, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1835, d927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c659 pattern childGuard
    simpa only [d1835, d927, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c661 (pattern : Twelve) (guard : d0 pattern = 1) : d920 pattern ≤ (0 : Int) + d863 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c662 (pattern : Twelve) (guard : d1835 pattern = 1) : d928 pattern ≤ (0 : Int) + d867 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1835, d928, d867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c30 pattern childGuard
    simpa only [d1835, d928, d867, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1835, d928, d867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c661 pattern childGuard
    simpa only [d1835, d928, d867, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c663 (pattern : Twelve) (guard : d1835 pattern = 1) : d933 pattern ≤ (0 : Int) + d869 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1835 pattern = 1 := by simpa only [d933, d869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c660 pattern childGuard
    simpa only [d933, d869, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1835 pattern = 1 := by simpa only [d933, d869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c662 pattern childGuard
    simpa only [d933, d869, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c664 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d864 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c665 (pattern : Twelve) (guard : d1835 pattern = 1) : d929 pattern ≤ (0 : Int) + d864 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1835, d929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c34 pattern childGuard
    simpa only [d1835, d929, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1835, d929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c664 pattern childGuard
    simpa only [d1835, d929, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c666 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d866 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c667 (pattern : Twelve) (guard : d1835 pattern = 1) : d930 pattern ≤ (0 : Int) + d868 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1835, d930, d868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c37 pattern childGuard
    simpa only [d1835, d930, d868, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1835, d930, d868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c666 pattern childGuard
    simpa only [d1835, d930, d868, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c668 (pattern : Twelve) (guard : d1835 pattern = 1) : d934 pattern ≤ (0 : Int) + d870 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1835 pattern = 1 := by simpa only [d934, d870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c665 pattern childGuard
    simpa only [d934, d870, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1835 pattern = 1 := by simpa only [d934, d870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c667 pattern childGuard
    simpa only [d934, d870, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c669 (pattern : Twelve) (guard : d1835 pattern = 1) : d936 pattern ≤ (0 : Int) + d871 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1835 pattern = 1 := by simpa only [d936, d871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c663 pattern childGuard
    simpa only [d936, d871, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1835 pattern = 1 := by simpa only [d936, d871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c668 pattern childGuard
    simpa only [d936, d871, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c670 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d861 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c671 (pattern : Twelve) (guard : d1835 pattern = 1) : d931 pattern ≤ (0 : Int) + d861 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1835, d931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c27 pattern childGuard
    simpa only [d1835, d931, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1835, d931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c670 pattern childGuard
    simpa only [d1835, d931, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c672 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d863 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c673 (pattern : Twelve) (guard : d1835 pattern = 1) : d932 pattern ≤ (0 : Int) + d867 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1835, d932, d867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c30 pattern childGuard
    simpa only [d1835, d932, d867, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1835, d932, d867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c672 pattern childGuard
    simpa only [d1835, d932, d867, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c674 (pattern : Twelve) (guard : d1835 pattern = 1) : d935 pattern ≤ (0 : Int) + d869 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1835 pattern = 1 := by simpa only [d935, d869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c671 pattern childGuard
    simpa only [d935, d869, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1835 pattern = 1 := by simpa only [d935, d869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c673 pattern childGuard
    simpa only [d935, d869, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c675 (pattern : Twelve) (guard : d1835 pattern = 1) : d937 pattern ≤ (0 : Int) + d871 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1835 pattern = 1 := by simpa only [d937, d871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c674 pattern childGuard
    simpa only [d937, d871, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1835 pattern = 1 := by simpa only [d937, d871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c668 pattern childGuard
    simpa only [d937, d871, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c676 (pattern : Twelve) (guard : d1835 pattern = 1) : d938 pattern ≤ (0 : Int) + d871 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1835 pattern = 1 := by simpa only [d938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c669 pattern childGuard
    simpa only [d938, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1835 pattern = 1 := by simpa only [d938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c675 pattern childGuard
    simpa only [d938, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c677 (pattern : Twelve) (guard : d1835 pattern = 1) : d939 pattern ≤ (0 : Int) + d871 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1835 pattern = 1 := by simpa only [d939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c676 pattern childGuard
    simpa only [d939, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1835 pattern = 1 := by simpa only [d939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c675 pattern childGuard
    simpa only [d939, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c678 (pattern : Twelve) (guard : d0 pattern = 1) : d1360 pattern ≤ (0 : Int) + d1313 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c679 (pattern : Twelve) (guard : d1835 pattern = 1) : d1368 pattern ≤ (0 : Int) + d1313 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1835, d1368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c50 pattern childGuard
    simpa only [d1835, d1368, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1835, d1368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c678 pattern childGuard
    simpa only [d1835, d1368, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c680 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1315 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c681 (pattern : Twelve) (guard : d1835 pattern = 1) : d1369 pattern ≤ (0 : Int) + d1319 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1835, d1369, d1319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c53 pattern childGuard
    simpa only [d1835, d1369, d1319, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1835, d1369, d1319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c680 pattern childGuard
    simpa only [d1835, d1369, d1319, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c682 (pattern : Twelve) (guard : d1835 pattern = 1) : d1373 pattern ≤ (0 : Int) + d1321 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1835 pattern = 1 := by simpa only [d1373, d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c679 pattern childGuard
    simpa only [d1373, d1321, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1835 pattern = 1 := by simpa only [d1373, d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c681 pattern childGuard
    simpa only [d1373, d1321, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c683 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1316 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c684 (pattern : Twelve) (guard : d1835 pattern = 1) : d1370 pattern ≤ (0 : Int) + d1316 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1835, d1370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c57 pattern childGuard
    simpa only [d1835, d1370, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1835, d1370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c683 pattern childGuard
    simpa only [d1835, d1370, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c685 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1318 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c686 (pattern : Twelve) (guard : d1835 pattern = 1) : d1371 pattern ≤ (0 : Int) + d1320 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1835, d1371, d1320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c60 pattern childGuard
    simpa only [d1835, d1371, d1320, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1835, d1371, d1320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c685 pattern childGuard
    simpa only [d1835, d1371, d1320, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c687 (pattern : Twelve) (guard : d1835 pattern = 1) : d1374 pattern ≤ (0 : Int) + d1322 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1835 pattern = 1 := by simpa only [d1374, d1322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c684 pattern childGuard
    simpa only [d1374, d1322, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1835 pattern = 1 := by simpa only [d1374, d1322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c686 pattern childGuard
    simpa only [d1374, d1322, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c688 (pattern : Twelve) (guard : d1835 pattern = 1) : d1376 pattern ≤ (0 : Int) + d1323 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1835 pattern = 1 := by simpa only [d1376, d1323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c682 pattern childGuard
    simpa only [d1376, d1323, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1835 pattern = 1 := by simpa only [d1376, d1323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c687 pattern childGuard
    simpa only [d1376, d1323, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c689 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1313 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c690 (pattern : Twelve) (guard : d1835 pattern = 1) : d1372 pattern ≤ (0 : Int) + d1313 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1835, d1372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c50 pattern childGuard
    simpa only [d1835, d1372, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1835, d1372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c689 pattern childGuard
    simpa only [d1835, d1372, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c691 (pattern : Twelve) (guard : d1835 pattern = 1) : d1375 pattern ≤ (0 : Int) + d1321 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1835 pattern = 1 := by simpa only [d1375, d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c690 pattern childGuard
    simpa only [d1375, d1321, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1835 pattern = 1 := by simpa only [d1375, d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c681 pattern childGuard
    simpa only [d1375, d1321, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c692 (pattern : Twelve) (guard : d1835 pattern = 1) : d1377 pattern ≤ (0 : Int) + d1323 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1835 pattern = 1 := by simpa only [d1377, d1323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c691 pattern childGuard
    simpa only [d1377, d1323, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1835 pattern = 1 := by simpa only [d1377, d1323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c687 pattern childGuard
    simpa only [d1377, d1323, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c693 (pattern : Twelve) (guard : d1835 pattern = 1) : d1378 pattern ≤ (0 : Int) + d1323 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1835 pattern = 1 := by simpa only [d1378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c688 pattern childGuard
    simpa only [d1378, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1835 pattern = 1 := by simpa only [d1378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c692 pattern childGuard
    simpa only [d1378, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c694 (pattern : Twelve) (guard : d1835 pattern = 1) : d1379 pattern ≤ (0 : Int) + d1323 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1835 pattern = 1 := by simpa only [d1379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c693 pattern childGuard
    simpa only [d1379, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1835 pattern = 1 := by simpa only [d1379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c692 pattern childGuard
    simpa only [d1379, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c695 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1660 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c696 (pattern : Twelve) (guard : d1835 pattern = 1) : d1686 pattern ≤ (0 : Int) + d1660 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1835, d1686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c71 pattern childGuard
    simpa only [d1835, d1686, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1835, d1686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c695 pattern childGuard
    simpa only [d1835, d1686, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c697 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1662 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c698 (pattern : Twelve) (guard : d1835 pattern = 1) : d1687 pattern ≤ (0 : Int) + d1663 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1835, d1687, d1663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c74 pattern childGuard
    simpa only [d1835, d1687, d1663, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1835, d1687, d1663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c697 pattern childGuard
    simpa only [d1835, d1687, d1663, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c699 (pattern : Twelve) (guard : d1835 pattern = 1) : d1688 pattern ≤ (0 : Int) + d1664 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1835 pattern = 1 := by simpa only [d1688, d1664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c696 pattern childGuard
    simpa only [d1688, d1664, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1835 pattern = 1 := by simpa only [d1688, d1664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c698 pattern childGuard
    simpa only [d1688, d1664, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
