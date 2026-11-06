/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons044
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c6300 (pattern : Twelve) (guard : d1858 pattern = 1) : d1481 pattern ≤ (0 : Int) + d1419 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1481, d1419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6296 pattern childGuard
    simpa only [d1481, d1419, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1481, d1419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6299 pattern childGuard
    simpa only [d1481, d1419, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6301 (pattern : Twelve) (guard : d1858 pattern = 1) : d1482 pattern ≤ (0 : Int) + d1420 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1482, d1420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6287 pattern childGuard
    simpa only [d1482, d1420, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1482, d1420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2211 pattern childGuard
    simpa only [d1482, d1420, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6302 (pattern : Twelve) (guard : d1858 pattern = 1) : d1485 pattern ≤ (0 : Int) + d1422 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1485, d1422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6300 pattern childGuard
    simpa only [d1485, d1422, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1485, d1422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6301 pattern childGuard
    simpa only [d1485, d1422, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6303 (pattern : Twelve) (guard : d1858 pattern = 1) : d1487 pattern ≤ (0 : Int) + d1423 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1487, d1423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6293 pattern childGuard
    simpa only [d1487, d1423, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1487, d1423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6302 pattern childGuard
    simpa only [d1487, d1423, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6304 (pattern : Twelve) (guard : d1858 pattern = 1) : d1488 pattern ≤ (0 : Int) + d1424 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1488, d1424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6292 pattern childGuard
    simpa only [d1488, d1424, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1488, d1424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6302 pattern childGuard
    simpa only [d1488, d1424, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6305 (pattern : Twelve) (guard : d1858 pattern = 1) : d1490 pattern ≤ (0 : Int) + d1425 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1490, d1425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6303 pattern childGuard
    simpa only [d1490, d1425, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1490, d1425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6304 pattern childGuard
    simpa only [d1490, d1425, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6306 (pattern : Twelve) (guard : d1858 pattern = 1) : d1491 pattern ≤ (0 : Int) + d1426 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1491, d1426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6305 pattern childGuard
    simpa only [d1491, d1426, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1491, d1426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6304 pattern childGuard
    simpa only [d1491, d1426, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6307 (pattern : Twelve) (guard : d0 pattern = 1) : d1342 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6308 (pattern : Twelve) (guard : d1858 pattern = 1) : d1477 pattern ≤ (0 : Int) + d1415 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1858, d1477, d1415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6295 pattern childGuard
    simpa only [d1858, d1477, d1415, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1858, d1477, d1415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6307 pattern childGuard
    simpa only [d1858, d1477, d1415, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6309 (pattern : Twelve) (guard : d0 pattern = 1) : d1344 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6310 (pattern : Twelve) (guard : d1858 pattern = 1) : d1478 pattern ≤ (0 : Int) + d1416 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1858, d1478, d1416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6298 pattern childGuard
    simpa only [d1858, d1478, d1416, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1858, d1478, d1416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6309 pattern childGuard
    simpa only [d1858, d1478, d1416, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6311 (pattern : Twelve) (guard : d1858 pattern = 1) : d1483 pattern ≤ (0 : Int) + d1419 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1483, d1419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6308 pattern childGuard
    simpa only [d1483, d1419, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1483, d1419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6310 pattern childGuard
    simpa only [d1483, d1419, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6312 (pattern : Twelve) (guard : d1858 pattern = 1) : d1486 pattern ≤ (0 : Int) + d1422 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1486, d1422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6311 pattern childGuard
    simpa only [d1486, d1422, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1486, d1422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6301 pattern childGuard
    simpa only [d1486, d1422, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6313 (pattern : Twelve) (guard : d1858 pattern = 1) : d1489 pattern ≤ (0 : Int) + d1424 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1489, d1424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6292 pattern childGuard
    simpa only [d1489, d1424, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1489, d1424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6312 pattern childGuard
    simpa only [d1489, d1424, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6314 (pattern : Twelve) (guard : d1858 pattern = 1) : d1492 pattern ≤ (0 : Int) + d1427 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1492, d1427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6306 pattern childGuard
    simpa only [d1492, d1427, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1492, d1427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6313 pattern childGuard
    simpa only [d1492, d1427, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6315 (pattern : Twelve) (guard : d1852 pattern = 1) : d1294 pattern ≤ (0 : Int) + d1649 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d1294, d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c328 pattern childGuard
    simpa only [d1852, d1294, d1649, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d1294, d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1102 pattern childGuard
    simpa only [d1852, d1294, d1649, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6316 (pattern : Twelve) (guard : d1858 pattern = 1) : d1730 pattern ≤ (0 : Int) + d1705 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1858, d1730, d1705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6315 pattern childGuard
    simpa only [d1858, d1730, d1705, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1858, d1730, d1705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c583 pattern childGuard
    simpa only [d1858, d1730, d1705, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6317 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1647 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6318 (pattern : Twelve) (guard : d1852 pattern = 1) : d1296 pattern ≤ (0 : Int) + d1651 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d1296, d1651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2395 pattern childGuard
    simpa only [d1852, d1296, d1651, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d1296, d1651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6317 pattern childGuard
    simpa only [d1852, d1296, d1651, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6319 (pattern : Twelve) (guard : d1858 pattern = 1) : d1731 pattern ≤ (0 : Int) + d1706 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1858, d1731, d1706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6318 pattern childGuard
    simpa only [d1858, d1731, d1706, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1858, d1731, d1706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c558 pattern childGuard
    simpa only [d1858, d1731, d1706, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6320 (pattern : Twelve) (guard : d1858 pattern = 1) : d1736 pattern ≤ (0 : Int) + d1709 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1736, d1709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6316 pattern childGuard
    simpa only [d1736, d1709, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1736, d1709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6319 pattern childGuard
    simpa only [d1736, d1709, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6321 (pattern : Twelve) (guard : d1852 pattern = 1) : d1298 pattern ≤ (0 : Int) + d1652 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d1298, d1652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c243 pattern childGuard
    simpa only [d1852, d1298, d1652, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d1298, d1652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1114 pattern childGuard
    simpa only [d1852, d1298, d1652, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6322 (pattern : Twelve) (guard : d1858 pattern = 1) : d1732 pattern ≤ (0 : Int) + d1707 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1858, d1732, d1707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6321 pattern childGuard
    simpa only [d1858, d1732, d1707, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1858, d1732, d1707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c589 pattern childGuard
    simpa only [d1858, d1732, d1707, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6323 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1648 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6324 (pattern : Twelve) (guard : d1852 pattern = 1) : d1300 pattern ≤ (0 : Int) + d1654 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d1300, d1654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2402 pattern childGuard
    simpa only [d1852, d1300, d1654, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d1300, d1654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6323 pattern childGuard
    simpa only [d1852, d1300, d1654, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6325 (pattern : Twelve) (guard : d1858 pattern = 1) : d1733 pattern ≤ (0 : Int) + d1708 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1858, d1733, d1708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6324 pattern childGuard
    simpa only [d1858, d1733, d1708, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1858, d1733, d1708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c592 pattern childGuard
    simpa only [d1858, d1733, d1708, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6326 (pattern : Twelve) (guard : d1858 pattern = 1) : d1737 pattern ≤ (0 : Int) + d1710 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1737, d1710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6322 pattern childGuard
    simpa only [d1737, d1710, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1737, d1710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6325 pattern childGuard
    simpa only [d1737, d1710, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6327 (pattern : Twelve) (guard : d1858 pattern = 1) : d1738 pattern ≤ (0 : Int) + d1711 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1738, d1711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6319 pattern childGuard
    simpa only [d1738, d1711, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1738, d1711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2211 pattern childGuard
    simpa only [d1738, d1711, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6328 (pattern : Twelve) (guard : d1858 pattern = 1) : d1740 pattern ≤ (0 : Int) + d1712 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1740, d1712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6326 pattern childGuard
    simpa only [d1740, d1712, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1740, d1712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6327 pattern childGuard
    simpa only [d1740, d1712, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6329 (pattern : Twelve) (guard : d1858 pattern = 1) : d1742 pattern ≤ (0 : Int) + d1713 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1742, d1713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6320 pattern childGuard
    simpa only [d1742, d1713, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1742, d1713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6328 pattern childGuard
    simpa only [d1742, d1713, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6330 (pattern : Twelve) (guard : d1858 pattern = 1) : d1734 pattern ≤ (0 : Int) + d1707 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1858, d1734, d1707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6321 pattern childGuard
    simpa only [d1858, d1734, d1707, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1858, d1734, d1707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c558 pattern childGuard
    simpa only [d1858, d1734, d1707, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6331 (pattern : Twelve) (guard : d1858 pattern = 1) : d1735 pattern ≤ (0 : Int) + d1708 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1858, d1735, d1708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6324 pattern childGuard
    simpa only [d1858, d1735, d1708, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1858, d1735, d1708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1256 pattern childGuard
    simpa only [d1858, d1735, d1708, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6332 (pattern : Twelve) (guard : d1858 pattern = 1) : d1739 pattern ≤ (0 : Int) + d1710 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1739, d1710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6330 pattern childGuard
    simpa only [d1739, d1710, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1739, d1710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6331 pattern childGuard
    simpa only [d1739, d1710, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6333 (pattern : Twelve) (guard : d1858 pattern = 1) : d1741 pattern ≤ (0 : Int) + d1712 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1741, d1712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6332 pattern childGuard
    simpa only [d1741, d1712, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1741, d1712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6327 pattern childGuard
    simpa only [d1741, d1712, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6334 (pattern : Twelve) (guard : d1858 pattern = 1) : d1743 pattern ≤ (0 : Int) + d1713 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1743, d1713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6320 pattern childGuard
    simpa only [d1743, d1713, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1743, d1713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6333 pattern childGuard
    simpa only [d1743, d1713, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6335 (pattern : Twelve) (guard : d1858 pattern = 1) : d1744 pattern ≤ (0 : Int) + d1713 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6329 pattern childGuard
    simpa only [d1744, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6334 pattern childGuard
    simpa only [d1744, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6336 (pattern : Twelve) (guard : d0 pattern = 1) : d186 pattern ≤ (0 : Int) + d51 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6337 (pattern : Twelve) (guard : d1852 pattern = 1) : d426 pattern ≤ (0 : Int) + d73 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d426, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1852, d426, d73, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d426, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6336 pattern childGuard
    simpa only [d1852, d426, d73, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6338 (pattern : Twelve) (guard : d1852 pattern = 1) : d444 pattern ≤ (0 : Int) + d91 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d444, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6105 pattern childGuard
    simpa only [d444, d91, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d444, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6337 pattern childGuard
    simpa only [d444, d91, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6339 (pattern : Twelve) (guard : d1 pattern = 1) : d54 pattern ≤ (0 : Int) + d54 pattern := by
  omega
theorem c6340 (pattern : Twelve) (guard : d0 pattern = 1) : d189 pattern ≤ (0 : Int) + d55 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6341 (pattern : Twelve) (guard : d1852 pattern = 1) : d428 pattern ≤ (0 : Int) + d75 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d428, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6339 pattern childGuard
    simpa only [d1852, d428, d75, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d428, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6340 pattern childGuard
    simpa only [d1852, d428, d75, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6342 (pattern : Twelve) (guard : d1852 pattern = 1) : d445 pattern ≤ (0 : Int) + d92 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d445, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6109 pattern childGuard
    simpa only [d445, d92, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d445, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6341 pattern childGuard
    simpa only [d445, d92, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6343 (pattern : Twelve) (guard : d1852 pattern = 1) : d455 pattern ≤ (0 : Int) + d102 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d455, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6338 pattern childGuard
    simpa only [d455, d102, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d455, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6342 pattern childGuard
    simpa only [d455, d102, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6344 (pattern : Twelve) (guard : d1852 pattern = 1) : d430 pattern ≤ (0 : Int) + d76 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d430, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1852, d430, d76, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d430, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6340 pattern childGuard
    simpa only [d1852, d430, d76, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6345 (pattern : Twelve) (guard : d1852 pattern = 1) : d446 pattern ≤ (0 : Int) + d93 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d446, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6114 pattern childGuard
    simpa only [d446, d93, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d446, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6344 pattern childGuard
    simpa only [d446, d93, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6346 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d55 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6347 (pattern : Twelve) (guard : d1852 pattern = 1) : d432 pattern ≤ (0 : Int) + d78 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d432, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2190 pattern childGuard
    simpa only [d1852, d432, d78, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d432, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6346 pattern childGuard
    simpa only [d1852, d432, d78, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6348 (pattern : Twelve) (guard : d1852 pattern = 1) : d447 pattern ≤ (0 : Int) + d94 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d447, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6118 pattern childGuard
    simpa only [d447, d94, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d447, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6347 pattern childGuard
    simpa only [d447, d94, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6349 (pattern : Twelve) (guard : d1852 pattern = 1) : d456 pattern ≤ (0 : Int) + d103 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d456, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6345 pattern childGuard
    simpa only [d456, d103, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d456, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6348 pattern childGuard
    simpa only [d456, d103, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6350 (pattern : Twelve) (guard : d1852 pattern = 1) : d465 pattern ≤ (0 : Int) + d110 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d465, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6343 pattern childGuard
    simpa only [d465, d110, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d465, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6349 pattern childGuard
    simpa only [d465, d110, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6351 (pattern : Twelve) (guard : d0 pattern = 1) : d194 pattern ≤ (0 : Int) + d55 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6352 (pattern : Twelve) (guard : d1852 pattern = 1) : d434 pattern ≤ (0 : Int) + d80 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d434, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c92 pattern childGuard
    simpa only [d1852, d434, d80, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d434, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6351 pattern childGuard
    simpa only [d1852, d434, d80, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6353 (pattern : Twelve) (guard : d1852 pattern = 1) : d448 pattern ≤ (0 : Int) + d95 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d448, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6124 pattern childGuard
    simpa only [d448, d95, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d448, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6352 pattern childGuard
    simpa only [d448, d95, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6354 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d61 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6355 (pattern : Twelve) (guard : d1852 pattern = 1) : d436 pattern ≤ (0 : Int) + d82 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d436, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2201 pattern childGuard
    simpa only [d1852, d436, d82, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d436, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6354 pattern childGuard
    simpa only [d1852, d436, d82, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6356 (pattern : Twelve) (guard : d1852 pattern = 1) : d449 pattern ≤ (0 : Int) + d96 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d449, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6128 pattern childGuard
    simpa only [d449, d96, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d449, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6355 pattern childGuard
    simpa only [d449, d96, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6357 (pattern : Twelve) (guard : d1852 pattern = 1) : d457 pattern ≤ (0 : Int) + d104 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d457, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6353 pattern childGuard
    simpa only [d457, d104, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d457, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6356 pattern childGuard
    simpa only [d457, d104, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6358 (pattern : Twelve) (guard : d1852 pattern = 1) : d450 pattern ≤ (0 : Int) + d94 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d450, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6133 pattern childGuard
    simpa only [d450, d94, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d450, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6347 pattern childGuard
    simpa only [d450, d94, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6359 (pattern : Twelve) (guard : d1852 pattern = 1) : d6 pattern ≤ (0 : Int) + d6 pattern := by
  omega
theorem c6360 (pattern : Twelve) (guard : d1852 pattern = 1) : d458 pattern ≤ (0 : Int) + d105 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d458, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6358 pattern childGuard
    simpa only [d458, d105, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d458, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6359 pattern childGuard
    simpa only [d458, d105, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6361 (pattern : Twelve) (guard : d1852 pattern = 1) : d466 pattern ≤ (0 : Int) + d111 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d466, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6357 pattern childGuard
    simpa only [d466, d111, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d466, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6360 pattern childGuard
    simpa only [d466, d111, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6362 (pattern : Twelve) (guard : d1852 pattern = 1) : d471 pattern ≤ (0 : Int) + d114 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d471, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6350 pattern childGuard
    simpa only [d471, d114, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d471, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6361 pattern childGuard
    simpa only [d471, d114, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6363 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d51 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6364 (pattern : Twelve) (guard : d1852 pattern = 1) : d438 pattern ≤ (0 : Int) + d73 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d438, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1852, d438, d73, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d438, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6363 pattern childGuard
    simpa only [d1852, d438, d73, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6365 (pattern : Twelve) (guard : d1852 pattern = 1) : d438 pattern ≤ (0 : Int) + d91 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6140 pattern childGuard
    simpa only [d91, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6364 pattern childGuard
    simpa only [d91, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6366 (pattern : Twelve) (guard : d1852 pattern = 1) : d440 pattern ≤ (0 : Int) + d75 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d440, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6339 pattern childGuard
    simpa only [d1852, d440, d75, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d440, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6346 pattern childGuard
    simpa only [d1852, d440, d75, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6367 (pattern : Twelve) (guard : d1852 pattern = 1) : d451 pattern ≤ (0 : Int) + d92 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d451, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6168 pattern childGuard
    simpa only [d451, d92, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d451, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6366 pattern childGuard
    simpa only [d451, d92, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6368 (pattern : Twelve) (guard : d1852 pattern = 1) : d459 pattern ≤ (0 : Int) + d102 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d459, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6365 pattern childGuard
    simpa only [d459, d102, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d459, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6367 pattern childGuard
    simpa only [d459, d102, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6369 (pattern : Twelve) (guard : d1852 pattern = 1) : d438 pattern ≤ (0 : Int) + d76 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d438, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1852, d438, d76, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d438, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6346 pattern childGuard
    simpa only [d1852, d438, d76, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6370 (pattern : Twelve) (guard : d1852 pattern = 1) : d438 pattern ≤ (0 : Int) + d93 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6140 pattern childGuard
    simpa only [d93, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6369 pattern childGuard
    simpa only [d93, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6371 (pattern : Twelve) (guard : d1852 pattern = 1) : d432 pattern ≤ (0 : Int) + d94 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6172 pattern childGuard
    simpa only [d94, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6347 pattern childGuard
    simpa only [d94, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6372 (pattern : Twelve) (guard : d1852 pattern = 1) : d460 pattern ≤ (0 : Int) + d103 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d460, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6370 pattern childGuard
    simpa only [d460, d103, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d460, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6371 pattern childGuard
    simpa only [d460, d103, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6373 (pattern : Twelve) (guard : d1852 pattern = 1) : d467 pattern ≤ (0 : Int) + d110 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d467, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6368 pattern childGuard
    simpa only [d467, d110, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d467, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6372 pattern childGuard
    simpa only [d467, d110, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6374 (pattern : Twelve) (guard : d1852 pattern = 1) : d441 pattern ≤ (0 : Int) + d80 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d441, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c92 pattern childGuard
    simpa only [d1852, d441, d80, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d441, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6346 pattern childGuard
    simpa only [d1852, d441, d80, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6375 (pattern : Twelve) (guard : d1852 pattern = 1) : d441 pattern ≤ (0 : Int) + d95 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6177 pattern childGuard
    simpa only [d95, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6374 pattern childGuard
    simpa only [d95, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6376 (pattern : Twelve) (guard : d1852 pattern = 1) : d436 pattern ≤ (0 : Int) + d96 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6180 pattern childGuard
    simpa only [d96, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6355 pattern childGuard
    simpa only [d96, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6377 (pattern : Twelve) (guard : d1852 pattern = 1) : d461 pattern ≤ (0 : Int) + d104 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d461, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6375 pattern childGuard
    simpa only [d461, d104, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d461, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6376 pattern childGuard
    simpa only [d461, d104, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6378 (pattern : Twelve) (guard : d1852 pattern = 1) : d462 pattern ≤ (0 : Int) + d105 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d462, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6371 pattern childGuard
    simpa only [d462, d105, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d462, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6359 pattern childGuard
    simpa only [d462, d105, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6379 (pattern : Twelve) (guard : d1852 pattern = 1) : d468 pattern ≤ (0 : Int) + d111 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d468, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6377 pattern childGuard
    simpa only [d468, d111, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d468, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6378 pattern childGuard
    simpa only [d468, d111, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6380 (pattern : Twelve) (guard : d1852 pattern = 1) : d472 pattern ≤ (0 : Int) + d114 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d472, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6373 pattern childGuard
    simpa only [d472, d114, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d472, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6379 pattern childGuard
    simpa only [d472, d114, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6381 (pattern : Twelve) (guard : d1852 pattern = 1) : d474 pattern ≤ (0 : Int) + d114 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6362 pattern childGuard
    simpa only [d474, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6380 pattern childGuard
    simpa only [d474, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6382 (pattern : Twelve) (guard : d1852 pattern = 1) : d475 pattern ≤ (0 : Int) + d114 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6381 pattern childGuard
    simpa only [d475, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6380 pattern childGuard
    simpa only [d475, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6383 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d129 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6384 (pattern : Twelve) (guard : d1852 pattern = 1) : d438 pattern ≤ (0 : Int) + d136 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d438, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1852, d438, d136, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d438, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6383 pattern childGuard
    simpa only [d1852, d438, d136, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6385 (pattern : Twelve) (guard : d1852 pattern = 1) : d438 pattern ≤ (0 : Int) + d144 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6140 pattern childGuard
    simpa only [d144, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6384 pattern childGuard
    simpa only [d144, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6386 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d130 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6387 (pattern : Twelve) (guard : d1852 pattern = 1) : d439 pattern ≤ (0 : Int) + d137 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d439, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2180 pattern childGuard
    simpa only [d1852, d439, d137, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d439, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6386 pattern childGuard
    simpa only [d1852, d439, d137, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6388 (pattern : Twelve) (guard : d1852 pattern = 1) : d432 pattern ≤ (0 : Int) + d138 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d432, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2190 pattern childGuard
    simpa only [d1852, d432, d138, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d432, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6383 pattern childGuard
    simpa only [d1852, d432, d138, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6389 (pattern : Twelve) (guard : d1852 pattern = 1) : d452 pattern ≤ (0 : Int) + d145 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d452, d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6387 pattern childGuard
    simpa only [d452, d145, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d452, d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6388 pattern childGuard
    simpa only [d452, d145, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6390 (pattern : Twelve) (guard : d1852 pattern = 1) : d463 pattern ≤ (0 : Int) + d149 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d463, d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6385 pattern childGuard
    simpa only [d463, d149, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d463, d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6389 pattern childGuard
    simpa only [d463, d149, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6391 (pattern : Twelve) (guard : d1852 pattern = 1) : d432 pattern ≤ (0 : Int) + d139 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d432, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2190 pattern childGuard
    simpa only [d1852, d432, d139, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d432, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6386 pattern childGuard
    simpa only [d1852, d432, d139, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6392 (pattern : Twelve) (guard : d1852 pattern = 1) : d432 pattern ≤ (0 : Int) + d146 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6391 pattern childGuard
    simpa only [d146, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6388 pattern childGuard
    simpa only [d146, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6393 (pattern : Twelve) (guard : d1852 pattern = 1) : d460 pattern ≤ (0 : Int) + d150 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d460, d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6385 pattern childGuard
    simpa only [d460, d150, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d460, d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6392 pattern childGuard
    simpa only [d460, d150, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6394 (pattern : Twelve) (guard : d1852 pattern = 1) : d469 pattern ≤ (0 : Int) + d153 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d469, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6390 pattern childGuard
    simpa only [d469, d153, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d469, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6393 pattern childGuard
    simpa only [d469, d153, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6395 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d131 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6396 (pattern : Twelve) (guard : d1852 pattern = 1) : d441 pattern ≤ (0 : Int) + d140 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d441, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c92 pattern childGuard
    simpa only [d1852, d441, d140, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d441, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6395 pattern childGuard
    simpa only [d1852, d441, d140, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6397 (pattern : Twelve) (guard : d1 pattern = 1) : d132 pattern ≤ (0 : Int) + d132 pattern := by
  omega
theorem c6398 (pattern : Twelve) (guard : d1852 pattern = 1) : d442 pattern ≤ (0 : Int) + d141 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d442, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6397 pattern childGuard
    simpa only [d1852, d442, d141, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d442, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6383 pattern childGuard
    simpa only [d1852, d442, d141, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6399 (pattern : Twelve) (guard : d1852 pattern = 1) : d453 pattern ≤ (0 : Int) + d147 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d453, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6396 pattern childGuard
    simpa only [d453, d147, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d453, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6398 pattern childGuard
    simpa only [d453, d147, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6400 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d133 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6401 (pattern : Twelve) (guard : d1852 pattern = 1) : d436 pattern ≤ (0 : Int) + d142 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d436, d142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2201 pattern childGuard
    simpa only [d1852, d436, d142, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d436, d142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6400 pattern childGuard
    simpa only [d1852, d436, d142, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6402 (pattern : Twelve) (guard : d1 pattern = 1) : d134 pattern ≤ (0 : Int) + d134 pattern := by
  omega
theorem c6403 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d135 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6404 (pattern : Twelve) (guard : d1852 pattern = 1) : d443 pattern ≤ (0 : Int) + d143 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d443, d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6402 pattern childGuard
    simpa only [d1852, d443, d143, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d443, d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6403 pattern childGuard
    simpa only [d1852, d443, d143, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6405 (pattern : Twelve) (guard : d1852 pattern = 1) : d454 pattern ≤ (0 : Int) + d148 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d454, d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6401 pattern childGuard
    simpa only [d454, d148, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d454, d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6404 pattern childGuard
    simpa only [d454, d148, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6406 (pattern : Twelve) (guard : d1852 pattern = 1) : d464 pattern ≤ (0 : Int) + d151 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d464, d151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6399 pattern childGuard
    simpa only [d464, d151, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d464, d151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6405 pattern childGuard
    simpa only [d464, d151, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6407 (pattern : Twelve) (guard : d1852 pattern = 1) : d462 pattern ≤ (0 : Int) + d152 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d462, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6392 pattern childGuard
    simpa only [d462, d152, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d462, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6359 pattern childGuard
    simpa only [d462, d152, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6408 (pattern : Twelve) (guard : d1852 pattern = 1) : d470 pattern ≤ (0 : Int) + d154 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d470, d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6406 pattern childGuard
    simpa only [d470, d154, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d470, d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6407 pattern childGuard
    simpa only [d470, d154, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6409 (pattern : Twelve) (guard : d1852 pattern = 1) : d473 pattern ≤ (0 : Int) + d155 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d473, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6394 pattern childGuard
    simpa only [d473, d155, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d473, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6408 pattern childGuard
    simpa only [d473, d155, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6410 (pattern : Twelve) (guard : d1852 pattern = 1) : d476 pattern ≤ (0 : Int) + d156 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d476, d156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6382 pattern childGuard
    simpa only [d476, d156, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d476, d156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6409 pattern childGuard
    simpa only [d476, d156, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6411 (pattern : Twelve) (guard : d0 pattern = 1) : d908 pattern ≤ (0 : Int) + d825 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6412 (pattern : Twelve) (guard : d1852 pattern = 1) : d1070 pattern ≤ (0 : Int) + d839 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d1070, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c240 pattern childGuard
    simpa only [d1852, d1070, d839, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d1070, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6411 pattern childGuard
    simpa only [d1852, d1070, d839, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6413 (pattern : Twelve) (guard : d1852 pattern = 1) : d1078 pattern ≤ (0 : Int) + d853 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1078, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6209 pattern childGuard
    simpa only [d1078, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1078, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6412 pattern childGuard
    simpa only [d1078, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6414 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d825 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6415 (pattern : Twelve) (guard : d1852 pattern = 1) : d1072 pattern ≤ (0 : Int) + d841 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d1072, d841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2361 pattern childGuard
    simpa only [d1852, d1072, d841, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d1072, d841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6414 pattern childGuard
    simpa only [d1852, d1072, d841, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6416 (pattern : Twelve) (guard : d1852 pattern = 1) : d1079 pattern ≤ (0 : Int) + d854 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1079, d854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6213 pattern childGuard
    simpa only [d1079, d854, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1079, d854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6415 pattern childGuard
    simpa only [d1079, d854, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6417 (pattern : Twelve) (guard : d1852 pattern = 1) : d1088 pattern ≤ (0 : Int) + d861 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1088, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6413 pattern childGuard
    simpa only [d1088, d861, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1088, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6416 pattern childGuard
    simpa only [d1088, d861, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6418 (pattern : Twelve) (guard : d1852 pattern = 1) : d1073 pattern ≤ (0 : Int) + d839 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d1073, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c240 pattern childGuard
    simpa only [d1852, d1073, d839, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d1073, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6414 pattern childGuard
    simpa only [d1852, d1073, d839, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6419 (pattern : Twelve) (guard : d1852 pattern = 1) : d1080 pattern ≤ (0 : Int) + d853 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1080, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6218 pattern childGuard
    simpa only [d1080, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1080, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6418 pattern childGuard
    simpa only [d1080, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6420 (pattern : Twelve) (guard : d1852 pattern = 1) : d1081 pattern ≤ (0 : Int) + d854 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1081, d854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6222 pattern childGuard
    simpa only [d1081, d854, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1081, d854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6415 pattern childGuard
    simpa only [d1081, d854, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6421 (pattern : Twelve) (guard : d1852 pattern = 1) : d1089 pattern ≤ (0 : Int) + d861 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1089, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6419 pattern childGuard
    simpa only [d1089, d861, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1089, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6420 pattern childGuard
    simpa only [d1089, d861, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6422 (pattern : Twelve) (guard : d1852 pattern = 1) : d1095 pattern ≤ (0 : Int) + d861 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6417 pattern childGuard
    simpa only [d1095, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6421 pattern childGuard
    simpa only [d1095, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6423 (pattern : Twelve) (guard : d1852 pattern = 1) : d1074 pattern ≤ (0 : Int) + d843 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d1074, d843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c100 pattern childGuard
    simpa only [d1852, d1074, d843, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d1074, d843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6414 pattern childGuard
    simpa only [d1852, d1074, d843, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6424 (pattern : Twelve) (guard : d1852 pattern = 1) : d1082 pattern ≤ (0 : Int) + d855 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1082, d855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6228 pattern childGuard
    simpa only [d1082, d855, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1082, d855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6423 pattern childGuard
    simpa only [d1082, d855, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6425 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d831 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6426 (pattern : Twelve) (guard : d1852 pattern = 1) : d1075 pattern ≤ (0 : Int) + d845 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d1075, d845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2374 pattern childGuard
    simpa only [d1852, d1075, d845, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d1075, d845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6425 pattern childGuard
    simpa only [d1852, d1075, d845, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6427 (pattern : Twelve) (guard : d1852 pattern = 1) : d1083 pattern ≤ (0 : Int) + d856 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1083, d856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6232 pattern childGuard
    simpa only [d1083, d856, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1083, d856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6426 pattern childGuard
    simpa only [d1083, d856, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6428 (pattern : Twelve) (guard : d1852 pattern = 1) : d1090 pattern ≤ (0 : Int) + d862 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1090, d862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6424 pattern childGuard
    simpa only [d1090, d862, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1090, d862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6427 pattern childGuard
    simpa only [d1090, d862, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6429 (pattern : Twelve) (guard : d1852 pattern = 1) : d1091 pattern ≤ (0 : Int) + d863 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1091, d863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6420 pattern childGuard
    simpa only [d1091, d863, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1091, d863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6359 pattern childGuard
    simpa only [d1091, d863, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6430 (pattern : Twelve) (guard : d1852 pattern = 1) : d1096 pattern ≤ (0 : Int) + d867 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1096, d867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6428 pattern childGuard
    simpa only [d1096, d867, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1096, d867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6429 pattern childGuard
    simpa only [d1096, d867, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6431 (pattern : Twelve) (guard : d1852 pattern = 1) : d1099 pattern ≤ (0 : Int) + d869 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1099, d869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6422 pattern childGuard
    simpa only [d1099, d869, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1099, d869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6430 pattern childGuard
    simpa only [d1099, d869, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6432 (pattern : Twelve) (guard : d1852 pattern = 1) : d1084 pattern ≤ (0 : Int) + d853 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1084, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6240 pattern childGuard
    simpa only [d1084, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1084, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6418 pattern childGuard
    simpa only [d1084, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6433 (pattern : Twelve) (guard : d1852 pattern = 1) : d1092 pattern ≤ (0 : Int) + d861 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1092, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6432 pattern childGuard
    simpa only [d1092, d861, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1092, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6420 pattern childGuard
    simpa only [d1092, d861, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6434 (pattern : Twelve) (guard : d1852 pattern = 1) : d1085 pattern ≤ (0 : Int) + d855 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1085, d855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6261 pattern childGuard
    simpa only [d1085, d855, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1085, d855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6423 pattern childGuard
    simpa only [d1085, d855, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6435 (pattern : Twelve) (guard : d1852 pattern = 1) : d1093 pattern ≤ (0 : Int) + d862 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1093, d862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6434 pattern childGuard
    simpa only [d1093, d862, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1093, d862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6427 pattern childGuard
    simpa only [d1093, d862, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6436 (pattern : Twelve) (guard : d1852 pattern = 1) : d1097 pattern ≤ (0 : Int) + d867 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1097, d867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6435 pattern childGuard
    simpa only [d1097, d867, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1097, d867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6429 pattern childGuard
    simpa only [d1097, d867, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6437 (pattern : Twelve) (guard : d1852 pattern = 1) : d1100 pattern ≤ (0 : Int) + d869 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1100, d869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6433 pattern childGuard
    simpa only [d1100, d869, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1100, d869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6436 pattern childGuard
    simpa only [d1100, d869, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6438 (pattern : Twelve) (guard : d1852 pattern = 1) : d1102 pattern ≤ (0 : Int) + d869 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6431 pattern childGuard
    simpa only [d1102, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6437 pattern childGuard
    simpa only [d1102, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6439 (pattern : Twelve) (guard : d1852 pattern = 1) : d1103 pattern ≤ (0 : Int) + d869 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6438 pattern childGuard
    simpa only [d1103, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6437 pattern childGuard
    simpa only [d1103, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
