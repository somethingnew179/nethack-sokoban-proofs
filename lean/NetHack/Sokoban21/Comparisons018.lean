/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons017
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c2520 (pattern : Twelve) (guard : d1847 pattern = 1) : d1415 pattern ≤ (0 : Int) + d1394 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1847, d1415, d1394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c347 pattern childGuard
    simpa only [d1847, d1415, d1394, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1847, d1415, d1394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2513 pattern childGuard
    simpa only [d1847, d1415, d1394, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2521 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1391 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2522 (pattern : Twelve) (guard : d1847 pattern = 1) : d1416 pattern ≤ (0 : Int) + d1396 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1847, d1416, d1396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c355 pattern childGuard
    simpa only [d1847, d1416, d1396, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1847, d1416, d1396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2521 pattern childGuard
    simpa only [d1847, d1416, d1396, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2523 (pattern : Twelve) (guard : d1847 pattern = 1) : d1419 pattern ≤ (0 : Int) + d1400 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d1419, d1400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2520 pattern childGuard
    simpa only [d1419, d1400, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d1419, d1400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2522 pattern childGuard
    simpa only [d1419, d1400, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2524 (pattern : Twelve) (guard : d1847 pattern = 1) : d1420 pattern ≤ (0 : Int) + d1401 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d1420, d1401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2514 pattern childGuard
    simpa only [d1420, d1401, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d1420, d1401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1149 pattern childGuard
    simpa only [d1420, d1401, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2525 (pattern : Twelve) (guard : d1847 pattern = 1) : d1422 pattern ≤ (0 : Int) + d1404 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d1422, d1404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2523 pattern childGuard
    simpa only [d1422, d1404, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d1422, d1404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2524 pattern childGuard
    simpa only [d1422, d1404, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2526 (pattern : Twelve) (guard : d1847 pattern = 1) : d1423 pattern ≤ (0 : Int) + d1405 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d1423, d1405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2519 pattern childGuard
    simpa only [d1423, d1405, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d1423, d1405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2525 pattern childGuard
    simpa only [d1423, d1405, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2527 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1392 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2528 (pattern : Twelve) (guard : d1847 pattern = 1) : d1414 pattern ≤ (0 : Int) + d1397 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1847, d1414, d1397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c341 pattern childGuard
    simpa only [d1847, d1414, d1397, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1847, d1414, d1397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2527 pattern childGuard
    simpa only [d1847, d1414, d1397, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2529 (pattern : Twelve) (guard : d1847 pattern = 1) : d1418 pattern ≤ (0 : Int) + d1402 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d1418, d1402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2528 pattern childGuard
    simpa only [d1418, d1402, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d1418, d1402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2514 pattern childGuard
    simpa only [d1418, d1402, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2530 (pattern : Twelve) (guard : d1847 pattern = 1) : d1424 pattern ≤ (0 : Int) + d1406 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d1424, d1406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2529 pattern childGuard
    simpa only [d1424, d1406, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d1424, d1406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2525 pattern childGuard
    simpa only [d1424, d1406, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2531 (pattern : Twelve) (guard : d1847 pattern = 1) : d1425 pattern ≤ (0 : Int) + d1408 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d1425, d1408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2526 pattern childGuard
    simpa only [d1425, d1408, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d1425, d1408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2530 pattern childGuard
    simpa only [d1425, d1408, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2532 (pattern : Twelve) (guard : d1847 pattern = 1) : d1424 pattern ≤ (0 : Int) + d1407 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d1424, d1407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2518 pattern childGuard
    simpa only [d1424, d1407, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d1424, d1407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2525 pattern childGuard
    simpa only [d1424, d1407, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2533 (pattern : Twelve) (guard : d1847 pattern = 1) : d1424 pattern ≤ (0 : Int) + d1409 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d1409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2532 pattern childGuard
    simpa only [d1409, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d1409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2530 pattern childGuard
    simpa only [d1409, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2534 (pattern : Twelve) (guard : d1847 pattern = 1) : d1426 pattern ≤ (0 : Int) + d1410 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d1426, d1410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2531 pattern childGuard
    simpa only [d1426, d1410, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d1426, d1410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2533 pattern childGuard
    simpa only [d1426, d1410, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2535 (pattern : Twelve) (guard : d1847 pattern = 1) : d1427 pattern ≤ (0 : Int) + d1411 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d1427, d1411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2534 pattern childGuard
    simpa only [d1427, d1411, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d1427, d1411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2533 pattern childGuard
    simpa only [d1427, d1411, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2536 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1694 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2537 (pattern : Twelve) (guard : d1847 pattern = 1) : d1705 pattern ≤ (0 : Int) + d1697 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1847, d1705, d1697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c391 pattern childGuard
    simpa only [d1847, d1705, d1697, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1847, d1705, d1697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2536 pattern childGuard
    simpa only [d1847, d1705, d1697, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2538 (pattern : Twelve) (guard : d1847 pattern = 1) : d1706 pattern ≤ (0 : Int) + d1698 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1847, d1706, d1698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c400 pattern childGuard
    simpa only [d1847, d1706, d1698, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1847, d1706, d1698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2521 pattern childGuard
    simpa only [d1847, d1706, d1698, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2539 (pattern : Twelve) (guard : d1847 pattern = 1) : d1709 pattern ≤ (0 : Int) + d1700 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d1709, d1700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2537 pattern childGuard
    simpa only [d1709, d1700, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d1709, d1700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2538 pattern childGuard
    simpa only [d1709, d1700, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2540 (pattern : Twelve) (guard : d1847 pattern = 1) : d1707 pattern ≤ (0 : Int) + d1698 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1847, d1707, d1698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c405 pattern childGuard
    simpa only [d1847, d1707, d1698, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1847, d1707, d1698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2521 pattern childGuard
    simpa only [d1847, d1707, d1698, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2541 (pattern : Twelve) (guard : d1847 pattern = 1) : d1708 pattern ≤ (0 : Int) + d1699 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1847, d1708, d1699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c413 pattern childGuard
    simpa only [d1847, d1708, d1699, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1847, d1708, d1699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2411 pattern childGuard
    simpa only [d1847, d1708, d1699, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2542 (pattern : Twelve) (guard : d1847 pattern = 1) : d1710 pattern ≤ (0 : Int) + d1701 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d1710, d1701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2540 pattern childGuard
    simpa only [d1710, d1701, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d1710, d1701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2541 pattern childGuard
    simpa only [d1710, d1701, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2543 (pattern : Twelve) (guard : d1847 pattern = 1) : d1711 pattern ≤ (0 : Int) + d1702 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d1711, d1702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2538 pattern childGuard
    simpa only [d1711, d1702, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d1711, d1702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1149 pattern childGuard
    simpa only [d1711, d1702, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2544 (pattern : Twelve) (guard : d1847 pattern = 1) : d1712 pattern ≤ (0 : Int) + d1703 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d1712, d1703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2542 pattern childGuard
    simpa only [d1712, d1703, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d1712, d1703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2543 pattern childGuard
    simpa only [d1712, d1703, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2545 (pattern : Twelve) (guard : d1847 pattern = 1) : d1713 pattern ≤ (0 : Int) + d1704 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d1713, d1704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2539 pattern childGuard
    simpa only [d1713, d1704, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d1713, d1704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2544 pattern childGuard
    simpa only [d1713, d1704, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2546 (pattern : Twelve) (guard : d1848 pattern = 1) : d0 pattern ≤ (0 : Int) + d184 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1263 pattern childGuard
    simpa only [d184, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1272 pattern childGuard
    simpa only [d184, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2547 (pattern : Twelve) (guard : d0 pattern = 1) : d27 pattern ≤ (0 : Int) + d366 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2548 (pattern : Twelve) (guard : d1849 pattern = 1) : d50 pattern ≤ (0 : Int) + d372 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d50, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1267 pattern childGuard
    simpa only [d1849, d50, d372, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d50, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2547 pattern childGuard
    simpa only [d1849, d50, d372, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2549 (pattern : Twelve) (guard : d1863 pattern = 1) : d72 pattern ≤ (0 : Int) + d389 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1863, d72, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2546 pattern childGuard
    simpa only [d1863, d72, d389, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1863, d72, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2548 pattern childGuard
    simpa only [d1863, d72, d389, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2550 (pattern : Twelve) (guard : d0 pattern = 1) : d198 pattern ≤ (0 : Int) + d390 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2551 (pattern : Twelve) (guard : d1864 pattern = 1) : d304 pattern ≤ (0 : Int) + d402 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1863 pattern = 1 := by simpa only [d1864, d304, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2549 pattern childGuard
    simpa only [d1864, d304, d402, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1864, d304, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2550 pattern childGuard
    simpa only [d1864, d304, d402, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2552 (pattern : Twelve) (guard : d0 pattern = 1) : d20 pattern ≤ (0 : Int) + d167 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2553 (pattern : Twelve) (guard : d1848 pattern = 1) : d31 pattern ≤ (0 : Int) + d369 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d31, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1848, d31, d369, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d31, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2552 pattern childGuard
    simpa only [d1848, d31, d369, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2554 (pattern : Twelve) (guard : d1848 pattern = 1) : d52 pattern ≤ (0 : Int) + d375 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d52, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1281 pattern childGuard
    simpa only [d52, d375, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d52, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2553 pattern childGuard
    simpa only [d52, d375, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2555 (pattern : Twelve) (guard : d0 pattern = 1) : d32 pattern ≤ (0 : Int) + d36 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2556 (pattern : Twelve) (guard : d1849 pattern = 1) : d53 pattern ≤ (0 : Int) + d376 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d53, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1285 pattern childGuard
    simpa only [d1849, d53, d376, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d53, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2555 pattern childGuard
    simpa only [d1849, d53, d376, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2557 (pattern : Twelve) (guard : d1863 pattern = 1) : d74 pattern ≤ (0 : Int) + d391 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1863, d74, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2554 pattern childGuard
    simpa only [d1863, d74, d391, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1863, d74, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2556 pattern childGuard
    simpa only [d1863, d74, d391, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2558 (pattern : Twelve) (guard : d0 pattern = 1) : d200 pattern ≤ (0 : Int) + d392 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2559 (pattern : Twelve) (guard : d1864 pattern = 1) : d305 pattern ≤ (0 : Int) + d403 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1863 pattern = 1 := by simpa only [d1864, d305, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2557 pattern childGuard
    simpa only [d1864, d305, d403, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1864, d305, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2558 pattern childGuard
    simpa only [d1864, d305, d403, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2560 (pattern : Twelve) (guard : d1864 pattern = 1) : d320 pattern ≤ (0 : Int) + d409 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d320, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2551 pattern childGuard
    simpa only [d320, d409, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d320, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2559 pattern childGuard
    simpa only [d320, d409, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2561 (pattern : Twelve) (guard : d1848 pattern = 1) : d0 pattern ≤ (0 : Int) + d375 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1297 pattern childGuard
    simpa only [d375, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1304 pattern childGuard
    simpa only [d375, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2562 (pattern : Twelve) (guard : d0 pattern = 1) : d27 pattern ≤ (0 : Int) + d36 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2563 (pattern : Twelve) (guard : d1849 pattern = 1) : d50 pattern ≤ (0 : Int) + d376 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d50, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1300 pattern childGuard
    simpa only [d1849, d50, d376, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d50, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2562 pattern childGuard
    simpa only [d1849, d50, d376, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2564 (pattern : Twelve) (guard : d1863 pattern = 1) : d72 pattern ≤ (0 : Int) + d391 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1863, d72, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2561 pattern childGuard
    simpa only [d1863, d72, d391, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1863, d72, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2563 pattern childGuard
    simpa only [d1863, d72, d391, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2565 (pattern : Twelve) (guard : d1864 pattern = 1) : d306 pattern ≤ (0 : Int) + d403 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1863 pattern = 1 := by simpa only [d1864, d306, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2564 pattern childGuard
    simpa only [d1864, d306, d403, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1864, d306, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2558 pattern childGuard
    simpa only [d1864, d306, d403, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2566 (pattern : Twelve) (guard : d1848 pattern = 1) : d35 pattern ≤ (0 : Int) + d35 pattern := by
  omega
theorem c2567 (pattern : Twelve) (guard : d1848 pattern = 1) : d56 pattern ≤ (0 : Int) + d379 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d56, d379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1309 pattern childGuard
    simpa only [d56, d379, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d56, d379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2566 pattern childGuard
    simpa only [d56, d379, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2568 (pattern : Twelve) (guard : d0 pattern = 1) : d36 pattern ≤ (0 : Int) + d36 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2569 (pattern : Twelve) (guard : d1849 pattern = 1) : d57 pattern ≤ (0 : Int) + d380 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d57, d380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1312 pattern childGuard
    simpa only [d1849, d57, d380, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d57, d380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2568 pattern childGuard
    simpa only [d1849, d57, d380, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2570 (pattern : Twelve) (guard : d1863 pattern = 1) : d77 pattern ≤ (0 : Int) + d393 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1863, d77, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2567 pattern childGuard
    simpa only [d1863, d77, d393, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1863, d77, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2569 pattern childGuard
    simpa only [d1863, d77, d393, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2571 (pattern : Twelve) (guard : d0 pattern = 1) : d202 pattern ≤ (0 : Int) + d394 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2572 (pattern : Twelve) (guard : d1864 pattern = 1) : d307 pattern ≤ (0 : Int) + d404 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1863 pattern = 1 := by simpa only [d1864, d307, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2570 pattern childGuard
    simpa only [d1864, d307, d404, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1864, d307, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2571 pattern childGuard
    simpa only [d1864, d307, d404, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2573 (pattern : Twelve) (guard : d1864 pattern = 1) : d321 pattern ≤ (0 : Int) + d410 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d321, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2565 pattern childGuard
    simpa only [d321, d410, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d321, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2572 pattern childGuard
    simpa only [d321, d410, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2574 (pattern : Twelve) (guard : d1864 pattern = 1) : d332 pattern ≤ (0 : Int) + d415 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d332, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2560 pattern childGuard
    simpa only [d332, d415, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d332, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2573 pattern childGuard
    simpa only [d332, d415, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2575 (pattern : Twelve) (guard : d1848 pattern = 1) : d30 pattern ≤ (0 : Int) + d381 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1321 pattern childGuard
    simpa only [d381, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1325 pattern childGuard
    simpa only [d381, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2576 (pattern : Twelve) (guard : d0 pattern = 1) : d37 pattern ≤ (0 : Int) + d36 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2577 (pattern : Twelve) (guard : d1849 pattern = 1) : d58 pattern ≤ (0 : Int) + d382 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d58, d382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1325 pattern childGuard
    simpa only [d1849, d58, d382, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d58, d382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2576 pattern childGuard
    simpa only [d1849, d58, d382, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2578 (pattern : Twelve) (guard : d1863 pattern = 1) : d79 pattern ≤ (0 : Int) + d395 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1863, d79, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2575 pattern childGuard
    simpa only [d1863, d79, d395, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1863, d79, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2577 pattern childGuard
    simpa only [d1863, d79, d395, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2579 (pattern : Twelve) (guard : d0 pattern = 1) : d204 pattern ≤ (0 : Int) + d396 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2580 (pattern : Twelve) (guard : d1864 pattern = 1) : d308 pattern ≤ (0 : Int) + d405 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1863 pattern = 1 := by simpa only [d1864, d308, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2578 pattern childGuard
    simpa only [d1864, d308, d405, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1864, d308, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2579 pattern childGuard
    simpa only [d1864, d308, d405, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2581 (pattern : Twelve) (guard : d1848 pattern = 1) : d39 pattern ≤ (0 : Int) + d39 pattern := by
  omega
theorem c2582 (pattern : Twelve) (guard : d1848 pattern = 1) : d59 pattern ≤ (0 : Int) + d39 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1335 pattern childGuard
    simpa only [d59, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2581 pattern childGuard
    simpa only [d59, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2583 (pattern : Twelve) (guard : d0 pattern = 1) : d40 pattern ≤ (0 : Int) + d40 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2584 (pattern : Twelve) (guard : d1849 pattern = 1) : d60 pattern ≤ (0 : Int) + d384 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d60, d384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1335 pattern childGuard
    simpa only [d1849, d60, d384, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d60, d384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2583 pattern childGuard
    simpa only [d1849, d60, d384, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2585 (pattern : Twelve) (guard : d1863 pattern = 1) : d81 pattern ≤ (0 : Int) + d397 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1863, d81, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2582 pattern childGuard
    simpa only [d1863, d81, d397, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1863, d81, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2584 pattern childGuard
    simpa only [d1863, d81, d397, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2586 (pattern : Twelve) (guard : d0 pattern = 1) : d206 pattern ≤ (0 : Int) + d398 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2587 (pattern : Twelve) (guard : d1864 pattern = 1) : d309 pattern ≤ (0 : Int) + d406 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1863 pattern = 1 := by simpa only [d1864, d309, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2585 pattern childGuard
    simpa only [d1864, d309, d406, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1864, d309, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2586 pattern childGuard
    simpa only [d1864, d309, d406, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2588 (pattern : Twelve) (guard : d1864 pattern = 1) : d322 pattern ≤ (0 : Int) + d411 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d322, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2580 pattern childGuard
    simpa only [d322, d411, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d322, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2587 pattern childGuard
    simpa only [d322, d411, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2589 (pattern : Twelve) (guard : d1848 pattern = 1) : d56 pattern ≤ (0 : Int) + d35 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1312 pattern childGuard
    simpa only [d56, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2566 pattern childGuard
    simpa only [d56, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2590 (pattern : Twelve) (guard : d1863 pattern = 1) : d77 pattern ≤ (0 : Int) + d399 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1863, d77, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2589 pattern childGuard
    simpa only [d1863, d77, d399, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1863, d77, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2569 pattern childGuard
    simpa only [d1863, d77, d399, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2591 (pattern : Twelve) (guard : d0 pattern = 1) : d206 pattern ≤ (0 : Int) + d394 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2592 (pattern : Twelve) (guard : d1864 pattern = 1) : d310 pattern ≤ (0 : Int) + d407 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1863 pattern = 1 := by simpa only [d1864, d310, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2590 pattern childGuard
    simpa only [d1864, d310, d407, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1864, d310, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2591 pattern childGuard
    simpa only [d1864, d310, d407, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2593 (pattern : Twelve) (guard : d1864 pattern = 1) : d6 pattern ≤ (0 : Int) + d6 pattern := by
  omega
theorem c2594 (pattern : Twelve) (guard : d1864 pattern = 1) : d323 pattern ≤ (0 : Int) + d412 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d323, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2592 pattern childGuard
    simpa only [d323, d412, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d323, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2593 pattern childGuard
    simpa only [d323, d412, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2595 (pattern : Twelve) (guard : d1864 pattern = 1) : d333 pattern ≤ (0 : Int) + d416 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d333, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2588 pattern childGuard
    simpa only [d333, d416, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d333, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2594 pattern childGuard
    simpa only [d333, d416, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2596 (pattern : Twelve) (guard : d1864 pattern = 1) : d338 pattern ≤ (0 : Int) + d419 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d338, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2574 pattern childGuard
    simpa only [d338, d419, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d338, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2595 pattern childGuard
    simpa only [d338, d419, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2597 (pattern : Twelve) (guard : d1849 pattern = 1) : d50 pattern ≤ (0 : Int) + d380 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d50, d380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1357 pattern childGuard
    simpa only [d1849, d50, d380, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d50, d380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2562 pattern childGuard
    simpa only [d1849, d50, d380, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2598 (pattern : Twelve) (guard : d1863 pattern = 1) : d72 pattern ≤ (0 : Int) + d399 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1863, d72, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1354 pattern childGuard
    simpa only [d1863, d72, d399, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1863, d72, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2597 pattern childGuard
    simpa only [d1863, d72, d399, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2599 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d394 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2600 (pattern : Twelve) (guard : d1864 pattern = 1) : d311 pattern ≤ (0 : Int) + d407 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1863 pattern = 1 := by simpa only [d1864, d311, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2598 pattern childGuard
    simpa only [d1864, d311, d407, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1864, d311, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2599 pattern childGuard
    simpa only [d1864, d311, d407, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2601 (pattern : Twelve) (guard : d1848 pattern = 1) : d31 pattern ≤ (0 : Int) + d35 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d31, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1848, d31, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d31, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1530 pattern childGuard
    simpa only [d1848, d31, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2602 (pattern : Twelve) (guard : d1848 pattern = 1) : d52 pattern ≤ (0 : Int) + d35 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1312 pattern childGuard
    simpa only [d52, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2601 pattern childGuard
    simpa only [d52, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2603 (pattern : Twelve) (guard : d0 pattern = 1) : d43 pattern ≤ (0 : Int) + d36 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2604 (pattern : Twelve) (guard : d1849 pattern = 1) : d62 pattern ≤ (0 : Int) + d380 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d62, d380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1312 pattern childGuard
    simpa only [d1849, d62, d380, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d62, d380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2603 pattern childGuard
    simpa only [d1849, d62, d380, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2605 (pattern : Twelve) (guard : d1863 pattern = 1) : d83 pattern ≤ (0 : Int) + d399 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1863, d83, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2602 pattern childGuard
    simpa only [d1863, d83, d399, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1863, d83, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2604 pattern childGuard
    simpa only [d1863, d83, d399, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2606 (pattern : Twelve) (guard : d1864 pattern = 1) : d312 pattern ≤ (0 : Int) + d407 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1863 pattern = 1 := by simpa only [d1864, d312, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2605 pattern childGuard
    simpa only [d1864, d312, d407, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1864, d312, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2599 pattern childGuard
    simpa only [d1864, d312, d407, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2607 (pattern : Twelve) (guard : d1864 pattern = 1) : d324 pattern ≤ (0 : Int) + d407 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2600 pattern childGuard
    simpa only [d324, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2606 pattern childGuard
    simpa only [d324, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2608 (pattern : Twelve) (guard : d0 pattern = 1) : d45 pattern ≤ (0 : Int) + d36 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2609 (pattern : Twelve) (guard : d1849 pattern = 1) : d65 pattern ≤ (0 : Int) + d380 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d65, d380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1312 pattern childGuard
    simpa only [d1849, d65, d380, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d65, d380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2608 pattern childGuard
    simpa only [d1849, d65, d380, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2610 (pattern : Twelve) (guard : d1863 pattern = 1) : d85 pattern ≤ (0 : Int) + d399 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1863, d85, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2589 pattern childGuard
    simpa only [d1863, d85, d399, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1863, d85, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2609 pattern childGuard
    simpa only [d1863, d85, d399, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2611 (pattern : Twelve) (guard : d1864 pattern = 1) : d313 pattern ≤ (0 : Int) + d407 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1863 pattern = 1 := by simpa only [d1864, d313, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2610 pattern childGuard
    simpa only [d1864, d313, d407, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1864, d313, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2599 pattern childGuard
    simpa only [d1864, d313, d407, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2612 (pattern : Twelve) (guard : d1864 pattern = 1) : d325 pattern ≤ (0 : Int) + d407 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2600 pattern childGuard
    simpa only [d325, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2611 pattern childGuard
    simpa only [d325, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2613 (pattern : Twelve) (guard : d1864 pattern = 1) : d334 pattern ≤ (0 : Int) + d407 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2607 pattern childGuard
    simpa only [d334, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2612 pattern childGuard
    simpa only [d334, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2614 (pattern : Twelve) (guard : d0 pattern = 1) : d46 pattern ≤ (0 : Int) + d36 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2615 (pattern : Twelve) (guard : d1849 pattern = 1) : d67 pattern ≤ (0 : Int) + d380 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d67, d380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1312 pattern childGuard
    simpa only [d1849, d67, d380, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d67, d380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2614 pattern childGuard
    simpa only [d1849, d67, d380, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2616 (pattern : Twelve) (guard : d1863 pattern = 1) : d87 pattern ≤ (0 : Int) + d399 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1863, d87, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1312 pattern childGuard
    simpa only [d1863, d87, d399, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1863, d87, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2615 pattern childGuard
    simpa only [d1863, d87, d399, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2617 (pattern : Twelve) (guard : d1864 pattern = 1) : d314 pattern ≤ (0 : Int) + d407 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1863 pattern = 1 := by simpa only [d1864, d314, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2616 pattern childGuard
    simpa only [d1864, d314, d407, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1864, d314, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2599 pattern childGuard
    simpa only [d1864, d314, d407, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2618 (pattern : Twelve) (guard : d0 pattern = 1) : d47 pattern ≤ (0 : Int) + d40 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2619 (pattern : Twelve) (guard : d1849 pattern = 1) : d69 pattern ≤ (0 : Int) + d384 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d69, d384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1335 pattern childGuard
    simpa only [d1849, d69, d384, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d69, d384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2618 pattern childGuard
    simpa only [d1849, d69, d384, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2620 (pattern : Twelve) (guard : d1863 pattern = 1) : d89 pattern ≤ (0 : Int) + d397 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1863, d89, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2582 pattern childGuard
    simpa only [d1863, d89, d397, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1863, d89, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2619 pattern childGuard
    simpa only [d1863, d89, d397, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2621 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d398 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2622 (pattern : Twelve) (guard : d1864 pattern = 1) : d315 pattern ≤ (0 : Int) + d406 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1863 pattern = 1 := by simpa only [d1864, d315, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2620 pattern childGuard
    simpa only [d1864, d315, d406, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1864, d315, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2621 pattern childGuard
    simpa only [d1864, d315, d406, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2623 (pattern : Twelve) (guard : d1864 pattern = 1) : d326 pattern ≤ (0 : Int) + d413 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d326, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2617 pattern childGuard
    simpa only [d326, d413, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d326, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2622 pattern childGuard
    simpa only [d326, d413, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2624 (pattern : Twelve) (guard : d1864 pattern = 1) : d327 pattern ≤ (0 : Int) + d412 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d327, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2611 pattern childGuard
    simpa only [d327, d412, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d327, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2593 pattern childGuard
    simpa only [d327, d412, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2625 (pattern : Twelve) (guard : d1864 pattern = 1) : d335 pattern ≤ (0 : Int) + d417 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d335, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2623 pattern childGuard
    simpa only [d335, d417, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d335, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2624 pattern childGuard
    simpa only [d335, d417, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2626 (pattern : Twelve) (guard : d1864 pattern = 1) : d339 pattern ≤ (0 : Int) + d420 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d339, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2613 pattern childGuard
    simpa only [d339, d420, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d339, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2625 pattern childGuard
    simpa only [d339, d420, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2627 (pattern : Twelve) (guard : d1864 pattern = 1) : d341 pattern ≤ (0 : Int) + d422 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d341, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2596 pattern childGuard
    simpa only [d341, d422, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d341, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2626 pattern childGuard
    simpa only [d341, d422, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2628 (pattern : Twelve) (guard : d1849 pattern = 1) : d53 pattern ≤ (0 : Int) + d380 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d53, d380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1312 pattern childGuard
    simpa only [d1849, d53, d380, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d53, d380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2555 pattern childGuard
    simpa only [d1849, d53, d380, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2629 (pattern : Twelve) (guard : d1863 pattern = 1) : d74 pattern ≤ (0 : Int) + d399 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1863, d74, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2602 pattern childGuard
    simpa only [d1863, d74, d399, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1863, d74, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2628 pattern childGuard
    simpa only [d1863, d74, d399, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2630 (pattern : Twelve) (guard : d1864 pattern = 1) : d316 pattern ≤ (0 : Int) + d407 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1863 pattern = 1 := by simpa only [d1864, d316, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2629 pattern childGuard
    simpa only [d1864, d316, d407, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1864, d316, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2599 pattern childGuard
    simpa only [d1864, d316, d407, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2631 (pattern : Twelve) (guard : d1864 pattern = 1) : d328 pattern ≤ (0 : Int) + d407 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2600 pattern childGuard
    simpa only [d328, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2630 pattern childGuard
    simpa only [d328, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2632 (pattern : Twelve) (guard : d1864 pattern = 1) : d317 pattern ≤ (0 : Int) + d407 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1863 pattern = 1 := by simpa only [d1864, d317, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2590 pattern childGuard
    simpa only [d1864, d317, d407, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1864, d317, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2599 pattern childGuard
    simpa only [d1864, d317, d407, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2633 (pattern : Twelve) (guard : d1864 pattern = 1) : d329 pattern ≤ (0 : Int) + d407 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2600 pattern childGuard
    simpa only [d329, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2632 pattern childGuard
    simpa only [d329, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2634 (pattern : Twelve) (guard : d1864 pattern = 1) : d336 pattern ≤ (0 : Int) + d407 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2631 pattern childGuard
    simpa only [d336, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2633 pattern childGuard
    simpa only [d336, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2635 (pattern : Twelve) (guard : d1849 pattern = 1) : d58 pattern ≤ (0 : Int) + d380 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d58, d380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1312 pattern childGuard
    simpa only [d1849, d58, d380, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d58, d380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2576 pattern childGuard
    simpa only [d1849, d58, d380, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2636 (pattern : Twelve) (guard : d1863 pattern = 1) : d79 pattern ≤ (0 : Int) + d399 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1863, d79, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1312 pattern childGuard
    simpa only [d1863, d79, d399, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1863, d79, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2635 pattern childGuard
    simpa only [d1863, d79, d399, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2637 (pattern : Twelve) (guard : d1864 pattern = 1) : d318 pattern ≤ (0 : Int) + d407 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1863 pattern = 1 := by simpa only [d1864, d318, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2636 pattern childGuard
    simpa only [d1864, d318, d407, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1864, d318, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2599 pattern childGuard
    simpa only [d1864, d318, d407, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2638 (pattern : Twelve) (guard : d1864 pattern = 1) : d319 pattern ≤ (0 : Int) + d406 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1863 pattern = 1 := by simpa only [d1864, d319, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2585 pattern childGuard
    simpa only [d1864, d319, d406, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1864, d319, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2621 pattern childGuard
    simpa only [d1864, d319, d406, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2639 (pattern : Twelve) (guard : d1864 pattern = 1) : d330 pattern ≤ (0 : Int) + d413 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d330, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2637 pattern childGuard
    simpa only [d330, d413, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d330, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2638 pattern childGuard
    simpa only [d330, d413, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2640 (pattern : Twelve) (guard : d1864 pattern = 1) : d331 pattern ≤ (0 : Int) + d412 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d331, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2632 pattern childGuard
    simpa only [d331, d412, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d331, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2593 pattern childGuard
    simpa only [d331, d412, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2641 (pattern : Twelve) (guard : d1864 pattern = 1) : d337 pattern ≤ (0 : Int) + d417 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d337, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2639 pattern childGuard
    simpa only [d337, d417, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d337, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2640 pattern childGuard
    simpa only [d337, d417, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2642 (pattern : Twelve) (guard : d1864 pattern = 1) : d340 pattern ≤ (0 : Int) + d420 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d340, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2634 pattern childGuard
    simpa only [d340, d420, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d340, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2641 pattern childGuard
    simpa only [d340, d420, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2643 (pattern : Twelve) (guard : d1864 pattern = 1) : d342 pattern ≤ (0 : Int) + d420 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2642 pattern childGuard
    simpa only [d342, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2626 pattern childGuard
    simpa only [d342, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2644 (pattern : Twelve) (guard : d1864 pattern = 1) : d343 pattern ≤ (0 : Int) + d423 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d343, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2627 pattern childGuard
    simpa only [d343, d423, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d343, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2643 pattern childGuard
    simpa only [d343, d423, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2645 (pattern : Twelve) (guard : d0 pattern = 1) : d40 pattern ≤ (0 : Int) + d125 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2646 (pattern : Twelve) (guard : d1849 pattern = 1) : d60 pattern ≤ (0 : Int) + d386 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d60, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1335 pattern childGuard
    simpa only [d1849, d60, d386, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d60, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2645 pattern childGuard
    simpa only [d1849, d60, d386, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2647 (pattern : Twelve) (guard : d1863 pattern = 1) : d81 pattern ≤ (0 : Int) + d400 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1863, d81, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2582 pattern childGuard
    simpa only [d1863, d81, d400, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1863, d81, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2646 pattern childGuard
    simpa only [d1863, d81, d400, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2648 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d401 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2649 (pattern : Twelve) (guard : d1864 pattern = 1) : d319 pattern ≤ (0 : Int) + d408 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1863 pattern = 1 := by simpa only [d1864, d319, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2647 pattern childGuard
    simpa only [d1864, d319, d408, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1864, d319, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2648 pattern childGuard
    simpa only [d1864, d319, d408, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2650 (pattern : Twelve) (guard : d1864 pattern = 1) : d330 pattern ≤ (0 : Int) + d414 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d330, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2637 pattern childGuard
    simpa only [d330, d414, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d330, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2649 pattern childGuard
    simpa only [d330, d414, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2651 (pattern : Twelve) (guard : d1864 pattern = 1) : d337 pattern ≤ (0 : Int) + d418 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d337, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2650 pattern childGuard
    simpa only [d337, d418, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d337, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2640 pattern childGuard
    simpa only [d337, d418, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2652 (pattern : Twelve) (guard : d1864 pattern = 1) : d340 pattern ≤ (0 : Int) + d421 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d340, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2634 pattern childGuard
    simpa only [d340, d421, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d340, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2651 pattern childGuard
    simpa only [d340, d421, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2653 (pattern : Twelve) (guard : d0 pattern = 1) : d47 pattern ≤ (0 : Int) + d125 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2654 (pattern : Twelve) (guard : d1849 pattern = 1) : d69 pattern ≤ (0 : Int) + d386 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d69, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1335 pattern childGuard
    simpa only [d1849, d69, d386, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d69, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2653 pattern childGuard
    simpa only [d1849, d69, d386, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2655 (pattern : Twelve) (guard : d1863 pattern = 1) : d89 pattern ≤ (0 : Int) + d400 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1863, d89, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2582 pattern childGuard
    simpa only [d1863, d89, d400, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1863, d89, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2654 pattern childGuard
    simpa only [d1863, d89, d400, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2656 (pattern : Twelve) (guard : d1864 pattern = 1) : d315 pattern ≤ (0 : Int) + d408 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1863 pattern = 1 := by simpa only [d1864, d315, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2655 pattern childGuard
    simpa only [d1864, d315, d408, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1864, d315, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2648 pattern childGuard
    simpa only [d1864, d315, d408, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2657 (pattern : Twelve) (guard : d1864 pattern = 1) : d326 pattern ≤ (0 : Int) + d414 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d326, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2617 pattern childGuard
    simpa only [d326, d414, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d326, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2656 pattern childGuard
    simpa only [d326, d414, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2658 (pattern : Twelve) (guard : d1864 pattern = 1) : d335 pattern ≤ (0 : Int) + d418 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d335, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2657 pattern childGuard
    simpa only [d335, d418, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d335, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2624 pattern childGuard
    simpa only [d335, d418, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2659 (pattern : Twelve) (guard : d1864 pattern = 1) : d339 pattern ≤ (0 : Int) + d421 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d339, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2613 pattern childGuard
    simpa only [d339, d421, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d339, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2658 pattern childGuard
    simpa only [d339, d421, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
