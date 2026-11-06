/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons016
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c2380 (pattern : Twelve) (guard : d1858 pattern = 1) : d1422 pattern ≤ (0 : Int) + d1485 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1422, d1485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2378 pattern childGuard
    simpa only [d1422, d1485, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1422, d1485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2379 pattern childGuard
    simpa only [d1422, d1485, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2381 (pattern : Twelve) (guard : d1858 pattern = 1) : d1423 pattern ≤ (0 : Int) + d1487 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1423, d1487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2370 pattern childGuard
    simpa only [d1423, d1487, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1423, d1487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2380 pattern childGuard
    simpa only [d1423, d1487, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2382 (pattern : Twelve) (guard : d1858 pattern = 1) : d1424 pattern ≤ (0 : Int) + d1488 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1424, d1488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2369 pattern childGuard
    simpa only [d1424, d1488, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1424, d1488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2380 pattern childGuard
    simpa only [d1424, d1488, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2383 (pattern : Twelve) (guard : d1858 pattern = 1) : d1425 pattern ≤ (0 : Int) + d1490 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1425, d1490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2381 pattern childGuard
    simpa only [d1425, d1490, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1425, d1490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2382 pattern childGuard
    simpa only [d1425, d1490, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2384 (pattern : Twelve) (guard : d1858 pattern = 1) : d1426 pattern ≤ (0 : Int) + d1491 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1426, d1491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2383 pattern childGuard
    simpa only [d1426, d1491, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1426, d1491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2382 pattern childGuard
    simpa only [d1426, d1491, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2385 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1342 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2386 (pattern : Twelve) (guard : d1858 pattern = 1) : d1415 pattern ≤ (0 : Int) + d1477 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1858, d1415, d1477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2372 pattern childGuard
    simpa only [d1858, d1415, d1477, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1858, d1415, d1477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2385 pattern childGuard
    simpa only [d1858, d1415, d1477, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2387 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1344 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2388 (pattern : Twelve) (guard : d1858 pattern = 1) : d1416 pattern ≤ (0 : Int) + d1478 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1858, d1416, d1478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2376 pattern childGuard
    simpa only [d1858, d1416, d1478, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1858, d1416, d1478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2387 pattern childGuard
    simpa only [d1858, d1416, d1478, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2389 (pattern : Twelve) (guard : d1858 pattern = 1) : d1419 pattern ≤ (0 : Int) + d1483 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1419, d1483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2386 pattern childGuard
    simpa only [d1419, d1483, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1419, d1483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2388 pattern childGuard
    simpa only [d1419, d1483, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2390 (pattern : Twelve) (guard : d1858 pattern = 1) : d1422 pattern ≤ (0 : Int) + d1486 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1422, d1486, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2389 pattern childGuard
    simpa only [d1422, d1486, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1422, d1486, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2379 pattern childGuard
    simpa only [d1422, d1486, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2391 (pattern : Twelve) (guard : d1858 pattern = 1) : d1424 pattern ≤ (0 : Int) + d1489 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1424, d1489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2369 pattern childGuard
    simpa only [d1424, d1489, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1424, d1489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2390 pattern childGuard
    simpa only [d1424, d1489, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2392 (pattern : Twelve) (guard : d1858 pattern = 1) : d1427 pattern ≤ (0 : Int) + d1492 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1427, d1492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2384 pattern childGuard
    simpa only [d1427, d1492, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1427, d1492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2391 pattern childGuard
    simpa only [d1427, d1492, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2393 (pattern : Twelve) (guard : d1852 pattern = 1) : d1649 pattern ≤ (0 : Int) + d1294 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d1649, d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c328 pattern childGuard
    simpa only [d1852, d1649, d1294, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d1649, d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c389 pattern childGuard
    simpa only [d1852, d1649, d1294, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2394 (pattern : Twelve) (guard : d1858 pattern = 1) : d1705 pattern ≤ (0 : Int) + d1730 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1858, d1705, d1730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2393 pattern childGuard
    simpa only [d1858, d1705, d1730, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1858, d1705, d1730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2164 pattern childGuard
    simpa only [d1858, d1705, d1730, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2395 (pattern : Twelve) (guard : d1 pattern = 1) : d1286 pattern ≤ (0 : Int) + d1286 pattern := by
  omega
theorem c2396 (pattern : Twelve) (guard : d0 pattern = 1) : d1647 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2397 (pattern : Twelve) (guard : d1852 pattern = 1) : d1651 pattern ≤ (0 : Int) + d1296 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d1651, d1296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2395 pattern childGuard
    simpa only [d1852, d1651, d1296, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d1651, d1296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2396 pattern childGuard
    simpa only [d1852, d1651, d1296, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2398 (pattern : Twelve) (guard : d1858 pattern = 1) : d1706 pattern ≤ (0 : Int) + d1731 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1858, d1706, d1731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2397 pattern childGuard
    simpa only [d1858, d1706, d1731, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1858, d1706, d1731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2140 pattern childGuard
    simpa only [d1858, d1706, d1731, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2399 (pattern : Twelve) (guard : d1858 pattern = 1) : d1709 pattern ≤ (0 : Int) + d1736 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1709, d1736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2394 pattern childGuard
    simpa only [d1709, d1736, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1709, d1736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2398 pattern childGuard
    simpa only [d1709, d1736, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2400 (pattern : Twelve) (guard : d1852 pattern = 1) : d1652 pattern ≤ (0 : Int) + d1298 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d1652, d1298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c243 pattern childGuard
    simpa only [d1852, d1652, d1298, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d1652, d1298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c403 pattern childGuard
    simpa only [d1852, d1652, d1298, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2401 (pattern : Twelve) (guard : d1858 pattern = 1) : d1707 pattern ≤ (0 : Int) + d1732 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1858, d1707, d1732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2400 pattern childGuard
    simpa only [d1858, d1707, d1732, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1858, d1707, d1732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2168 pattern childGuard
    simpa only [d1858, d1707, d1732, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2402 (pattern : Twelve) (guard : d1 pattern = 1) : d1289 pattern ≤ (0 : Int) + d1289 pattern := by
  omega
theorem c2403 (pattern : Twelve) (guard : d0 pattern = 1) : d1648 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2404 (pattern : Twelve) (guard : d1852 pattern = 1) : d1654 pattern ≤ (0 : Int) + d1300 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d1654, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2402 pattern childGuard
    simpa only [d1852, d1654, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d1654, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2403 pattern childGuard
    simpa only [d1852, d1654, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2405 (pattern : Twelve) (guard : d1858 pattern = 1) : d1708 pattern ≤ (0 : Int) + d1733 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1858, d1708, d1733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2404 pattern childGuard
    simpa only [d1858, d1708, d1733, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1858, d1708, d1733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2170 pattern childGuard
    simpa only [d1858, d1708, d1733, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2406 (pattern : Twelve) (guard : d1858 pattern = 1) : d1710 pattern ≤ (0 : Int) + d1737 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1710, d1737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2401 pattern childGuard
    simpa only [d1710, d1737, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1710, d1737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2405 pattern childGuard
    simpa only [d1710, d1737, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2407 (pattern : Twelve) (guard : d1858 pattern = 1) : d1711 pattern ≤ (0 : Int) + d1738 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1711, d1738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2398 pattern childGuard
    simpa only [d1711, d1738, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1711, d1738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2211 pattern childGuard
    simpa only [d1711, d1738, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2408 (pattern : Twelve) (guard : d1858 pattern = 1) : d1712 pattern ≤ (0 : Int) + d1740 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1712, d1740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2406 pattern childGuard
    simpa only [d1712, d1740, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1712, d1740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2407 pattern childGuard
    simpa only [d1712, d1740, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2409 (pattern : Twelve) (guard : d1858 pattern = 1) : d1713 pattern ≤ (0 : Int) + d1742 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1713, d1742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2399 pattern childGuard
    simpa only [d1713, d1742, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1713, d1742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2408 pattern childGuard
    simpa only [d1713, d1742, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2410 (pattern : Twelve) (guard : d1858 pattern = 1) : d1707 pattern ≤ (0 : Int) + d1734 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1858, d1707, d1734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2400 pattern childGuard
    simpa only [d1858, d1707, d1734, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1858, d1707, d1734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2140 pattern childGuard
    simpa only [d1858, d1707, d1734, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2411 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1626 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2412 (pattern : Twelve) (guard : d1858 pattern = 1) : d1708 pattern ≤ (0 : Int) + d1735 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1858, d1708, d1735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2404 pattern childGuard
    simpa only [d1858, d1708, d1735, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1858, d1708, d1735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2411 pattern childGuard
    simpa only [d1858, d1708, d1735, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2413 (pattern : Twelve) (guard : d1858 pattern = 1) : d1710 pattern ≤ (0 : Int) + d1739 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1710, d1739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2410 pattern childGuard
    simpa only [d1710, d1739, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1710, d1739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2412 pattern childGuard
    simpa only [d1710, d1739, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2414 (pattern : Twelve) (guard : d1858 pattern = 1) : d1712 pattern ≤ (0 : Int) + d1741 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1712, d1741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2413 pattern childGuard
    simpa only [d1712, d1741, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1712, d1741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2407 pattern childGuard
    simpa only [d1712, d1741, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2415 (pattern : Twelve) (guard : d1858 pattern = 1) : d1713 pattern ≤ (0 : Int) + d1743 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1713, d1743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2399 pattern childGuard
    simpa only [d1713, d1743, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1713, d1743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2414 pattern childGuard
    simpa only [d1713, d1743, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2416 (pattern : Twelve) (guard : d1858 pattern = 1) : d1713 pattern ≤ (0 : Int) + d1744 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2409 pattern childGuard
    simpa only [d1744, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2415 pattern childGuard
    simpa only [d1744, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2417 (pattern : Twelve) (guard : d0 pattern = 1) : d198 pattern ≤ (0 : Int) + d257 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2418 (pattern : Twelve) (guard : d1847 pattern = 1) : d304 pattern ≤ (0 : Int) + d272 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1847, d304, d272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c84 pattern childGuard
    simpa only [d1847, d304, d272, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1847, d304, d272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2417 pattern childGuard
    simpa only [d1847, d304, d272, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2419 (pattern : Twelve) (guard : d0 pattern = 1) : d200 pattern ≤ (0 : Int) + d259 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2420 (pattern : Twelve) (guard : d1847 pattern = 1) : d305 pattern ≤ (0 : Int) + d273 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1847, d305, d273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c97 pattern childGuard
    simpa only [d1847, d305, d273, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1847, d305, d273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2419 pattern childGuard
    simpa only [d1847, d305, d273, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2421 (pattern : Twelve) (guard : d1847 pattern = 1) : d320 pattern ≤ (0 : Int) + d284 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d320, d284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2418 pattern childGuard
    simpa only [d320, d284, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d320, d284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2420 pattern childGuard
    simpa only [d320, d284, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2422 (pattern : Twelve) (guard : d0 pattern = 1) : d200 pattern ≤ (0 : Int) + d261 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2423 (pattern : Twelve) (guard : d1847 pattern = 1) : d306 pattern ≤ (0 : Int) + d274 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1847, d306, d274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c110 pattern childGuard
    simpa only [d1847, d306, d274, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1847, d306, d274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2422 pattern childGuard
    simpa only [d1847, d306, d274, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2424 (pattern : Twelve) (guard : d0 pattern = 1) : d202 pattern ≤ (0 : Int) + d263 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2425 (pattern : Twelve) (guard : d1847 pattern = 1) : d307 pattern ≤ (0 : Int) + d275 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1847, d307, d275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c119 pattern childGuard
    simpa only [d1847, d307, d275, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1847, d307, d275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2424 pattern childGuard
    simpa only [d1847, d307, d275, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2426 (pattern : Twelve) (guard : d1847 pattern = 1) : d321 pattern ≤ (0 : Int) + d285 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d321, d285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2423 pattern childGuard
    simpa only [d321, d285, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d321, d285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2425 pattern childGuard
    simpa only [d321, d285, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2427 (pattern : Twelve) (guard : d1847 pattern = 1) : d332 pattern ≤ (0 : Int) + d293 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d332, d293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2421 pattern childGuard
    simpa only [d332, d293, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d332, d293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2426 pattern childGuard
    simpa only [d332, d293, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2428 (pattern : Twelve) (guard : d0 pattern = 1) : d204 pattern ≤ (0 : Int) + d265 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2429 (pattern : Twelve) (guard : d1847 pattern = 1) : d308 pattern ≤ (0 : Int) + d276 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1847, d308, d276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c130 pattern childGuard
    simpa only [d1847, d308, d276, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1847, d308, d276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2428 pattern childGuard
    simpa only [d1847, d308, d276, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2430 (pattern : Twelve) (guard : d0 pattern = 1) : d206 pattern ≤ (0 : Int) + d267 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2431 (pattern : Twelve) (guard : d1847 pattern = 1) : d309 pattern ≤ (0 : Int) + d277 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1847, d309, d277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c140 pattern childGuard
    simpa only [d1847, d309, d277, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1847, d309, d277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2430 pattern childGuard
    simpa only [d1847, d309, d277, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2432 (pattern : Twelve) (guard : d1847 pattern = 1) : d322 pattern ≤ (0 : Int) + d286 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d322, d286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2429 pattern childGuard
    simpa only [d322, d286, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d322, d286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2431 pattern childGuard
    simpa only [d322, d286, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2433 (pattern : Twelve) (guard : d0 pattern = 1) : d206 pattern ≤ (0 : Int) + d263 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2434 (pattern : Twelve) (guard : d1847 pattern = 1) : d310 pattern ≤ (0 : Int) + d278 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1847, d310, d278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c151 pattern childGuard
    simpa only [d1847, d310, d278, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1847, d310, d278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2433 pattern childGuard
    simpa only [d1847, d310, d278, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2435 (pattern : Twelve) (guard : d1847 pattern = 1) : d323 pattern ≤ (0 : Int) + d287 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d323, d287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2434 pattern childGuard
    simpa only [d323, d287, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d323, d287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1149 pattern childGuard
    simpa only [d323, d287, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2436 (pattern : Twelve) (guard : d1847 pattern = 1) : d333 pattern ≤ (0 : Int) + d294 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d333, d294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2432 pattern childGuard
    simpa only [d333, d294, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d333, d294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2435 pattern childGuard
    simpa only [d333, d294, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2437 (pattern : Twelve) (guard : d1847 pattern = 1) : d338 pattern ≤ (0 : Int) + d297 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d338, d297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2427 pattern childGuard
    simpa only [d338, d297, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d338, d297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2436 pattern childGuard
    simpa only [d338, d297, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2438 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d263 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2439 (pattern : Twelve) (guard : d1847 pattern = 1) : d311 pattern ≤ (0 : Int) + d279 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1847, d311, d279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c161 pattern childGuard
    simpa only [d1847, d311, d279, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1847, d311, d279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2438 pattern childGuard
    simpa only [d1847, d311, d279, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2440 (pattern : Twelve) (guard : d1847 pattern = 1) : d312 pattern ≤ (0 : Int) + d280 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1847, d312, d280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c170 pattern childGuard
    simpa only [d1847, d312, d280, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1847, d312, d280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2438 pattern childGuard
    simpa only [d1847, d312, d280, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2441 (pattern : Twelve) (guard : d1847 pattern = 1) : d324 pattern ≤ (0 : Int) + d288 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d324, d288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2439 pattern childGuard
    simpa only [d324, d288, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d324, d288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2440 pattern childGuard
    simpa only [d324, d288, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2442 (pattern : Twelve) (guard : d1847 pattern = 1) : d313 pattern ≤ (0 : Int) + d280 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1847, d313, d280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c179 pattern childGuard
    simpa only [d1847, d313, d280, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1847, d313, d280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2438 pattern childGuard
    simpa only [d1847, d313, d280, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2443 (pattern : Twelve) (guard : d1847 pattern = 1) : d325 pattern ≤ (0 : Int) + d288 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d325, d288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2439 pattern childGuard
    simpa only [d325, d288, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d325, d288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2442 pattern childGuard
    simpa only [d325, d288, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2444 (pattern : Twelve) (guard : d1847 pattern = 1) : d334 pattern ≤ (0 : Int) + d288 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2441 pattern childGuard
    simpa only [d334, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2443 pattern childGuard
    simpa only [d334, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2445 (pattern : Twelve) (guard : d1847 pattern = 1) : d314 pattern ≤ (0 : Int) + d280 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1847, d314, d280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c187 pattern childGuard
    simpa only [d1847, d314, d280, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1847, d314, d280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2438 pattern childGuard
    simpa only [d1847, d314, d280, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2446 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d267 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2447 (pattern : Twelve) (guard : d1847 pattern = 1) : d315 pattern ≤ (0 : Int) + d281 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1847, d315, d281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c194 pattern childGuard
    simpa only [d1847, d315, d281, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1847, d315, d281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2446 pattern childGuard
    simpa only [d1847, d315, d281, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2448 (pattern : Twelve) (guard : d1847 pattern = 1) : d326 pattern ≤ (0 : Int) + d289 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d326, d289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2445 pattern childGuard
    simpa only [d326, d289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d326, d289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2447 pattern childGuard
    simpa only [d326, d289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2449 (pattern : Twelve) (guard : d1847 pattern = 1) : d327 pattern ≤ (0 : Int) + d290 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d327, d290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2442 pattern childGuard
    simpa only [d327, d290, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d327, d290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1149 pattern childGuard
    simpa only [d327, d290, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2450 (pattern : Twelve) (guard : d1847 pattern = 1) : d335 pattern ≤ (0 : Int) + d295 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d335, d295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2448 pattern childGuard
    simpa only [d335, d295, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d335, d295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2449 pattern childGuard
    simpa only [d335, d295, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2451 (pattern : Twelve) (guard : d1847 pattern = 1) : d339 pattern ≤ (0 : Int) + d298 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d339, d298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2444 pattern childGuard
    simpa only [d339, d298, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d339, d298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2450 pattern childGuard
    simpa only [d339, d298, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2452 (pattern : Twelve) (guard : d1847 pattern = 1) : d341 pattern ≤ (0 : Int) + d300 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d341, d300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2437 pattern childGuard
    simpa only [d341, d300, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d341, d300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2451 pattern childGuard
    simpa only [d341, d300, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2453 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d270 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2454 (pattern : Twelve) (guard : d1847 pattern = 1) : d311 pattern ≤ (0 : Int) + d282 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1847, d311, d282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c161 pattern childGuard
    simpa only [d1847, d311, d282, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1847, d311, d282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2453 pattern childGuard
    simpa only [d1847, d311, d282, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2455 (pattern : Twelve) (guard : d1847 pattern = 1) : d316 pattern ≤ (0 : Int) + d280 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1847, d316, d280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c211 pattern childGuard
    simpa only [d1847, d316, d280, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1847, d316, d280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2438 pattern childGuard
    simpa only [d1847, d316, d280, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2456 (pattern : Twelve) (guard : d1847 pattern = 1) : d328 pattern ≤ (0 : Int) + d291 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d328, d291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2454 pattern childGuard
    simpa only [d328, d291, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d328, d291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2455 pattern childGuard
    simpa only [d328, d291, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2457 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d271 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2458 (pattern : Twelve) (guard : d1847 pattern = 1) : d311 pattern ≤ (0 : Int) + d283 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1847, d311, d283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c161 pattern childGuard
    simpa only [d1847, d311, d283, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1847, d311, d283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2457 pattern childGuard
    simpa only [d1847, d311, d283, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2459 (pattern : Twelve) (guard : d1847 pattern = 1) : d317 pattern ≤ (0 : Int) + d280 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1847, d317, d280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c219 pattern childGuard
    simpa only [d1847, d317, d280, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1847, d317, d280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2438 pattern childGuard
    simpa only [d1847, d317, d280, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2460 (pattern : Twelve) (guard : d1847 pattern = 1) : d329 pattern ≤ (0 : Int) + d292 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d329, d292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2458 pattern childGuard
    simpa only [d329, d292, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d329, d292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2459 pattern childGuard
    simpa only [d329, d292, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2461 (pattern : Twelve) (guard : d1847 pattern = 1) : d336 pattern ≤ (0 : Int) + d296 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d336, d296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2456 pattern childGuard
    simpa only [d336, d296, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d336, d296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2460 pattern childGuard
    simpa only [d336, d296, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2462 (pattern : Twelve) (guard : d1847 pattern = 1) : d318 pattern ≤ (0 : Int) + d280 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1847, d318, d280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c225 pattern childGuard
    simpa only [d1847, d318, d280, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1847, d318, d280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2438 pattern childGuard
    simpa only [d1847, d318, d280, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2463 (pattern : Twelve) (guard : d1847 pattern = 1) : d319 pattern ≤ (0 : Int) + d281 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1847, d319, d281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c227 pattern childGuard
    simpa only [d1847, d319, d281, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1847, d319, d281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2446 pattern childGuard
    simpa only [d1847, d319, d281, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2464 (pattern : Twelve) (guard : d1847 pattern = 1) : d330 pattern ≤ (0 : Int) + d289 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d330, d289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2462 pattern childGuard
    simpa only [d330, d289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d330, d289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2463 pattern childGuard
    simpa only [d330, d289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2465 (pattern : Twelve) (guard : d1847 pattern = 1) : d331 pattern ≤ (0 : Int) + d290 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d331, d290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2459 pattern childGuard
    simpa only [d331, d290, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d331, d290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1149 pattern childGuard
    simpa only [d331, d290, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2466 (pattern : Twelve) (guard : d1847 pattern = 1) : d337 pattern ≤ (0 : Int) + d295 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d337, d295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2464 pattern childGuard
    simpa only [d337, d295, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d337, d295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2465 pattern childGuard
    simpa only [d337, d295, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2467 (pattern : Twelve) (guard : d1847 pattern = 1) : d340 pattern ≤ (0 : Int) + d299 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d340, d299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2461 pattern childGuard
    simpa only [d340, d299, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d340, d299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2466 pattern childGuard
    simpa only [d340, d299, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2468 (pattern : Twelve) (guard : d1847 pattern = 1) : d342 pattern ≤ (0 : Int) + d301 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d342, d301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2467 pattern childGuard
    simpa only [d342, d301, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d342, d301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2451 pattern childGuard
    simpa only [d342, d301, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2469 (pattern : Twelve) (guard : d1847 pattern = 1) : d343 pattern ≤ (0 : Int) + d302 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d343, d302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2452 pattern childGuard
    simpa only [d343, d302, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d343, d302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2468 pattern childGuard
    simpa only [d343, d302, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2470 (pattern : Twelve) (guard : d1847 pattern = 1) : d344 pattern ≤ (0 : Int) + d303 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d344, d303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2469 pattern childGuard
    simpa only [d344, d303, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d344, d303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2468 pattern childGuard
    simpa only [d344, d303, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2471 (pattern : Twelve) (guard : d0 pattern = 1) : d909 pattern ≤ (0 : Int) + d948 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2472 (pattern : Twelve) (guard : d1847 pattern = 1) : d980 pattern ≤ (0 : Int) + d955 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1847, d980, d955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c239 pattern childGuard
    simpa only [d1847, d980, d955, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1847, d980, d955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2471 pattern childGuard
    simpa only [d1847, d980, d955, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2473 (pattern : Twelve) (guard : d0 pattern = 1) : d910 pattern ≤ (0 : Int) + d949 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2474 (pattern : Twelve) (guard : d1847 pattern = 1) : d981 pattern ≤ (0 : Int) + d956 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1847, d981, d956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c251 pattern childGuard
    simpa only [d1847, d981, d956, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1847, d981, d956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2473 pattern childGuard
    simpa only [d1847, d981, d956, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2475 (pattern : Twelve) (guard : d1847 pattern = 1) : d991 pattern ≤ (0 : Int) + d963 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d991, d963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2472 pattern childGuard
    simpa only [d991, d963, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d991, d963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2474 pattern childGuard
    simpa only [d991, d963, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2476 (pattern : Twelve) (guard : d0 pattern = 1) : d910 pattern ≤ (0 : Int) + d951 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2477 (pattern : Twelve) (guard : d1847 pattern = 1) : d982 pattern ≤ (0 : Int) + d957 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1847, d982, d957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c258 pattern childGuard
    simpa only [d1847, d982, d957, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1847, d982, d957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2476 pattern childGuard
    simpa only [d1847, d982, d957, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2478 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d949 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2479 (pattern : Twelve) (guard : d1847 pattern = 1) : d983 pattern ≤ (0 : Int) + d958 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1847, d983, d958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c263 pattern childGuard
    simpa only [d1847, d983, d958, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1847, d983, d958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2478 pattern childGuard
    simpa only [d1847, d983, d958, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2480 (pattern : Twelve) (guard : d1847 pattern = 1) : d992 pattern ≤ (0 : Int) + d964 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d992, d964, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2477 pattern childGuard
    simpa only [d992, d964, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d992, d964, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2479 pattern childGuard
    simpa only [d992, d964, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2481 (pattern : Twelve) (guard : d1847 pattern = 1) : d1000 pattern ≤ (0 : Int) + d970 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d1000, d970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2475 pattern childGuard
    simpa only [d1000, d970, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d1000, d970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2480 pattern childGuard
    simpa only [d1000, d970, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2482 (pattern : Twelve) (guard : d0 pattern = 1) : d911 pattern ≤ (0 : Int) + d949 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2483 (pattern : Twelve) (guard : d1847 pattern = 1) : d984 pattern ≤ (0 : Int) + d959 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1847, d984, d959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c269 pattern childGuard
    simpa only [d1847, d984, d959, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1847, d984, d959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2482 pattern childGuard
    simpa only [d1847, d984, d959, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2484 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d952 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2485 (pattern : Twelve) (guard : d1847 pattern = 1) : d985 pattern ≤ (0 : Int) + d960 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1847, d985, d960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c276 pattern childGuard
    simpa only [d1847, d985, d960, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1847, d985, d960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2484 pattern childGuard
    simpa only [d1847, d985, d960, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2486 (pattern : Twelve) (guard : d1847 pattern = 1) : d993 pattern ≤ (0 : Int) + d965 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d993, d965, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2483 pattern childGuard
    simpa only [d993, d965, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d993, d965, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2485 pattern childGuard
    simpa only [d993, d965, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2487 (pattern : Twelve) (guard : d1847 pattern = 1) : d994 pattern ≤ (0 : Int) + d966 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d994, d966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2479 pattern childGuard
    simpa only [d994, d966, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d994, d966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1149 pattern childGuard
    simpa only [d994, d966, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2488 (pattern : Twelve) (guard : d1847 pattern = 1) : d1001 pattern ≤ (0 : Int) + d971 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d1001, d971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2486 pattern childGuard
    simpa only [d1001, d971, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d1001, d971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2487 pattern childGuard
    simpa only [d1001, d971, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2489 (pattern : Twelve) (guard : d1847 pattern = 1) : d1004 pattern ≤ (0 : Int) + d973 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d1004, d973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2481 pattern childGuard
    simpa only [d1004, d973, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d1004, d973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2488 pattern childGuard
    simpa only [d1004, d973, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2490 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d954 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2491 (pattern : Twelve) (guard : d1847 pattern = 1) : d986 pattern ≤ (0 : Int) + d961 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1847, d986, d961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c287 pattern childGuard
    simpa only [d1847, d986, d961, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1847, d986, d961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2490 pattern childGuard
    simpa only [d1847, d986, d961, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2492 (pattern : Twelve) (guard : d1847 pattern = 1) : d987 pattern ≤ (0 : Int) + d958 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1847, d987, d958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c294 pattern childGuard
    simpa only [d1847, d987, d958, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1847, d987, d958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2478 pattern childGuard
    simpa only [d1847, d987, d958, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2493 (pattern : Twelve) (guard : d1847 pattern = 1) : d995 pattern ≤ (0 : Int) + d967 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d995, d967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2491 pattern childGuard
    simpa only [d995, d967, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d995, d967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2492 pattern childGuard
    simpa only [d995, d967, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2494 (pattern : Twelve) (guard : d1847 pattern = 1) : d988 pattern ≤ (0 : Int) + d958 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1847, d988, d958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c300 pattern childGuard
    simpa only [d1847, d988, d958, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1847, d988, d958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2478 pattern childGuard
    simpa only [d1847, d988, d958, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2495 (pattern : Twelve) (guard : d1847 pattern = 1) : d989 pattern ≤ (0 : Int) + d960 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1847, d989, d960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c305 pattern childGuard
    simpa only [d1847, d989, d960, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1847, d989, d960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2484 pattern childGuard
    simpa only [d1847, d989, d960, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2496 (pattern : Twelve) (guard : d1847 pattern = 1) : d996 pattern ≤ (0 : Int) + d968 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d996, d968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2494 pattern childGuard
    simpa only [d996, d968, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d996, d968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2495 pattern childGuard
    simpa only [d996, d968, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2497 (pattern : Twelve) (guard : d1847 pattern = 1) : d997 pattern ≤ (0 : Int) + d966 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d997, d966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2492 pattern childGuard
    simpa only [d997, d966, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d997, d966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1149 pattern childGuard
    simpa only [d997, d966, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2498 (pattern : Twelve) (guard : d1847 pattern = 1) : d1002 pattern ≤ (0 : Int) + d972 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d1002, d972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2496 pattern childGuard
    simpa only [d1002, d972, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d1002, d972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2497 pattern childGuard
    simpa only [d1002, d972, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2499 (pattern : Twelve) (guard : d1847 pattern = 1) : d1005 pattern ≤ (0 : Int) + d974 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d1005, d974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2493 pattern childGuard
    simpa only [d1005, d974, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d1005, d974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2498 pattern childGuard
    simpa only [d1005, d974, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2500 (pattern : Twelve) (guard : d1847 pattern = 1) : d1007 pattern ≤ (0 : Int) + d976 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d1007, d976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2489 pattern childGuard
    simpa only [d1007, d976, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d1007, d976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2499 pattern childGuard
    simpa only [d1007, d976, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2501 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d951 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2502 (pattern : Twelve) (guard : d1847 pattern = 1) : d986 pattern ≤ (0 : Int) + d962 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1847, d986, d962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c287 pattern childGuard
    simpa only [d1847, d986, d962, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1847, d986, d962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2501 pattern childGuard
    simpa only [d1847, d986, d962, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2503 (pattern : Twelve) (guard : d1847 pattern = 1) : d998 pattern ≤ (0 : Int) + d969 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d998, d969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2502 pattern childGuard
    simpa only [d998, d969, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d998, d969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2479 pattern childGuard
    simpa only [d998, d969, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2504 (pattern : Twelve) (guard : d1847 pattern = 1) : d990 pattern ≤ (0 : Int) + d958 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1847, d990, d958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c316 pattern childGuard
    simpa only [d1847, d990, d958, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1847, d990, d958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2478 pattern childGuard
    simpa only [d1847, d990, d958, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2505 (pattern : Twelve) (guard : d1847 pattern = 1) : d999 pattern ≤ (0 : Int) + d968 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d999, d968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2504 pattern childGuard
    simpa only [d999, d968, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d999, d968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2485 pattern childGuard
    simpa only [d999, d968, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2506 (pattern : Twelve) (guard : d1847 pattern = 1) : d1003 pattern ≤ (0 : Int) + d972 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d1003, d972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2505 pattern childGuard
    simpa only [d1003, d972, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d1003, d972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2487 pattern childGuard
    simpa only [d1003, d972, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2507 (pattern : Twelve) (guard : d1847 pattern = 1) : d1006 pattern ≤ (0 : Int) + d975 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d1006, d975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2503 pattern childGuard
    simpa only [d1006, d975, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d1006, d975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2506 pattern childGuard
    simpa only [d1006, d975, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2508 (pattern : Twelve) (guard : d1847 pattern = 1) : d1008 pattern ≤ (0 : Int) + d977 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d1008, d977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2507 pattern childGuard
    simpa only [d1008, d977, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d1008, d977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2499 pattern childGuard
    simpa only [d1008, d977, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2509 (pattern : Twelve) (guard : d1847 pattern = 1) : d1009 pattern ≤ (0 : Int) + d978 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d1009, d978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2500 pattern childGuard
    simpa only [d1009, d978, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d1009, d978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2508 pattern childGuard
    simpa only [d1009, d978, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2510 (pattern : Twelve) (guard : d1847 pattern = 1) : d1010 pattern ≤ (0 : Int) + d979 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d1010, d979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2509 pattern childGuard
    simpa only [d1010, d979, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d1010, d979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2508 pattern childGuard
    simpa only [d1010, d979, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2511 (pattern : Twelve) (guard : d0 pattern = 1) : d1355 pattern ≤ (0 : Int) + d1386 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2512 (pattern : Twelve) (guard : d1847 pattern = 1) : d1412 pattern ≤ (0 : Int) + d1393 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1847, d1412, d1393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c327 pattern childGuard
    simpa only [d1847, d1412, d1393, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1847, d1412, d1393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2511 pattern childGuard
    simpa only [d1847, d1412, d1393, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2513 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1388 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2514 (pattern : Twelve) (guard : d1847 pattern = 1) : d1413 pattern ≤ (0 : Int) + d1394 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1847, d1413, d1394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c336 pattern childGuard
    simpa only [d1847, d1413, d1394, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1847, d1413, d1394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2513 pattern childGuard
    simpa only [d1847, d1413, d1394, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2515 (pattern : Twelve) (guard : d1847 pattern = 1) : d1417 pattern ≤ (0 : Int) + d1398 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d1417, d1398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2512 pattern childGuard
    simpa only [d1417, d1398, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d1417, d1398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2514 pattern childGuard
    simpa only [d1417, d1398, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2516 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1386 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2517 (pattern : Twelve) (guard : d1847 pattern = 1) : d1414 pattern ≤ (0 : Int) + d1395 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1847, d1414, d1395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c341 pattern childGuard
    simpa only [d1847, d1414, d1395, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1847, d1414, d1395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2516 pattern childGuard
    simpa only [d1847, d1414, d1395, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2518 (pattern : Twelve) (guard : d1847 pattern = 1) : d1418 pattern ≤ (0 : Int) + d1399 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d1418, d1399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2517 pattern childGuard
    simpa only [d1418, d1399, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d1418, d1399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2514 pattern childGuard
    simpa only [d1418, d1399, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2519 (pattern : Twelve) (guard : d1847 pattern = 1) : d1421 pattern ≤ (0 : Int) + d1403 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d1421, d1403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2515 pattern childGuard
    simpa only [d1421, d1403, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d1421, d1403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2518 pattern childGuard
    simpa only [d1421, d1403, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
