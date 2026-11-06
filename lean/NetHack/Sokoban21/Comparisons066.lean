/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons065
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c9240 (pattern : Twelve) (guard : d1852 pattern = 1) : d1321 pattern ≤ (0 : Int) + d1490 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9238 pattern childGuard
    simpa only [d1490, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9239 pattern childGuard
    simpa only [d1490, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9241 (pattern : Twelve) (guard : d1852 pattern = 1) : d1321 pattern ≤ (0 : Int) + d1491 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9240 pattern childGuard
    simpa only [d1491, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9239 pattern childGuard
    simpa only [d1491, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9242 (pattern : Twelve) (guard : d0 pattern = 1) : d1333 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9243 (pattern : Twelve) (guard : d1852 pattern = 1) : d1339 pattern ≤ (0 : Int) + d1073 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d1339, d1073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c240 pattern childGuard
    simpa only [d1852, d1339, d1073, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d1339, d1073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9242 pattern childGuard
    simpa only [d1852, d1339, d1073, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9244 (pattern : Twelve) (guard : d1852 pattern = 1) : d1345 pattern ≤ (0 : Int) + d1474 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1345, d1474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9243 pattern childGuard
    simpa only [d1345, d1474, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1345, d1474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6466 pattern childGuard
    simpa only [d1345, d1474, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9245 (pattern : Twelve) (guard : d0 pattern = 1) : d1334 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9246 (pattern : Twelve) (guard : d1852 pattern = 1) : d1340 pattern ≤ (0 : Int) + d1072 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d1340, d1072, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2361 pattern childGuard
    simpa only [d1852, d1340, d1072, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d1340, d1072, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9245 pattern childGuard
    simpa only [d1852, d1340, d1072, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9247 (pattern : Twelve) (guard : d1852 pattern = 1) : d1346 pattern ≤ (0 : Int) + d1473 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1346, d1473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9246 pattern childGuard
    simpa only [d1346, d1473, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1346, d1473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6468 pattern childGuard
    simpa only [d1346, d1473, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9248 (pattern : Twelve) (guard : d1852 pattern = 1) : d1349 pattern ≤ (0 : Int) + d1480 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1349, d1480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9244 pattern childGuard
    simpa only [d1349, d1480, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1349, d1480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9247 pattern childGuard
    simpa only [d1349, d1480, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9249 (pattern : Twelve) (guard : d0 pattern = 1) : d1335 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9250 (pattern : Twelve) (guard : d1852 pattern = 1) : d1341 pattern ≤ (0 : Int) + d1074 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d1341, d1074, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c100 pattern childGuard
    simpa only [d1852, d1341, d1074, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d1341, d1074, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9249 pattern childGuard
    simpa only [d1852, d1341, d1074, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9251 (pattern : Twelve) (guard : d1852 pattern = 1) : d1347 pattern ≤ (0 : Int) + d1477 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1347, d1477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9250 pattern childGuard
    simpa only [d1347, d1477, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1347, d1477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6494 pattern childGuard
    simpa only [d1347, d1477, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9252 (pattern : Twelve) (guard : d1852 pattern = 1) : d1343 pattern ≤ (0 : Int) + d1075 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d1343, d1075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2374 pattern childGuard
    simpa only [d1852, d1343, d1075, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d1343, d1075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5443 pattern childGuard
    simpa only [d1852, d1343, d1075, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9253 (pattern : Twelve) (guard : d1852 pattern = 1) : d1348 pattern ≤ (0 : Int) + d1478 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1348, d1478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9252 pattern childGuard
    simpa only [d1348, d1478, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1348, d1478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6498 pattern childGuard
    simpa only [d1348, d1478, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9254 (pattern : Twelve) (guard : d1852 pattern = 1) : d1350 pattern ≤ (0 : Int) + d1483 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1350, d1483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9251 pattern childGuard
    simpa only [d1350, d1483, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1350, d1483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9253 pattern childGuard
    simpa only [d1350, d1483, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9255 (pattern : Twelve) (guard : d1852 pattern = 1) : d1351 pattern ≤ (0 : Int) + d1482 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1351, d1482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9247 pattern childGuard
    simpa only [d1351, d1482, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1351, d1482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6359 pattern childGuard
    simpa only [d1351, d1482, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9256 (pattern : Twelve) (guard : d1852 pattern = 1) : d1352 pattern ≤ (0 : Int) + d1486 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1352, d1486, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9254 pattern childGuard
    simpa only [d1352, d1486, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1352, d1486, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9255 pattern childGuard
    simpa only [d1352, d1486, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9257 (pattern : Twelve) (guard : d1852 pattern = 1) : d1353 pattern ≤ (0 : Int) + d1489 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1353, d1489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9248 pattern childGuard
    simpa only [d1353, d1489, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1353, d1489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9256 pattern childGuard
    simpa only [d1353, d1489, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9258 (pattern : Twelve) (guard : d1852 pattern = 1) : d1354 pattern ≤ (0 : Int) + d1492 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1354, d1492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9241 pattern childGuard
    simpa only [d1354, d1492, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1354, d1492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9257 pattern childGuard
    simpa only [d1354, d1492, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9259 (pattern : Twelve) (guard : d1852 pattern = 1) : d1656 pattern ≤ (0 : Int) + d1730 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1656, d1730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2393 pattern childGuard
    simpa only [d1656, d1730, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1656, d1730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6505 pattern childGuard
    simpa only [d1656, d1730, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9260 (pattern : Twelve) (guard : d1852 pattern = 1) : d1657 pattern ≤ (0 : Int) + d1731 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1657, d1731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2397 pattern childGuard
    simpa only [d1657, d1731, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1657, d1731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6476 pattern childGuard
    simpa only [d1657, d1731, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9261 (pattern : Twelve) (guard : d1852 pattern = 1) : d1660 pattern ≤ (0 : Int) + d1736 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1660, d1736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9259 pattern childGuard
    simpa only [d1660, d1736, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1660, d1736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9260 pattern childGuard
    simpa only [d1660, d1736, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9262 (pattern : Twelve) (guard : d1852 pattern = 1) : d1658 pattern ≤ (0 : Int) + d1732 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1658, d1732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2400 pattern childGuard
    simpa only [d1658, d1732, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1658, d1732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6509 pattern childGuard
    simpa only [d1658, d1732, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9263 (pattern : Twelve) (guard : d1852 pattern = 1) : d1659 pattern ≤ (0 : Int) + d1733 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1659, d1733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2404 pattern childGuard
    simpa only [d1659, d1733, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1659, d1733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6511 pattern childGuard
    simpa only [d1659, d1733, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9264 (pattern : Twelve) (guard : d1852 pattern = 1) : d1661 pattern ≤ (0 : Int) + d1737 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1661, d1737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9262 pattern childGuard
    simpa only [d1661, d1737, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1661, d1737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9263 pattern childGuard
    simpa only [d1661, d1737, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9265 (pattern : Twelve) (guard : d1852 pattern = 1) : d1662 pattern ≤ (0 : Int) + d1738 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1662, d1738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9260 pattern childGuard
    simpa only [d1662, d1738, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1662, d1738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6359 pattern childGuard
    simpa only [d1662, d1738, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9266 (pattern : Twelve) (guard : d1852 pattern = 1) : d1663 pattern ≤ (0 : Int) + d1740 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1663, d1740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9264 pattern childGuard
    simpa only [d1663, d1740, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1663, d1740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9265 pattern childGuard
    simpa only [d1663, d1740, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9267 (pattern : Twelve) (guard : d1852 pattern = 1) : d1664 pattern ≤ (0 : Int) + d1742 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1664, d1742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9261 pattern childGuard
    simpa only [d1664, d1742, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1664, d1742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9266 pattern childGuard
    simpa only [d1664, d1742, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9268 (pattern : Twelve) (guard : d1852 pattern = 1) : d1668 pattern ≤ (0 : Int) + d1294 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d1668, d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c328 pattern childGuard
    simpa only [d1852, d1668, d1294, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d1668, d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c403 pattern childGuard
    simpa only [d1852, d1668, d1294, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9269 (pattern : Twelve) (guard : d1852 pattern = 1) : d1671 pattern ≤ (0 : Int) + d1730 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1671, d1730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9268 pattern childGuard
    simpa only [d1671, d1730, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1671, d1730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6505 pattern childGuard
    simpa only [d1671, d1730, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9270 (pattern : Twelve) (guard : d1852 pattern = 1) : d1674 pattern ≤ (0 : Int) + d1736 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1674, d1736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9269 pattern childGuard
    simpa only [d1674, d1736, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1674, d1736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9260 pattern childGuard
    simpa only [d1674, d1736, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9271 (pattern : Twelve) (guard : d0 pattern = 1) : d1666 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9272 (pattern : Twelve) (guard : d1852 pattern = 1) : d1669 pattern ≤ (0 : Int) + d1298 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d1669, d1298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c243 pattern childGuard
    simpa only [d1852, d1669, d1298, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d1669, d1298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9271 pattern childGuard
    simpa only [d1852, d1669, d1298, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9273 (pattern : Twelve) (guard : d1852 pattern = 1) : d1672 pattern ≤ (0 : Int) + d1734 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1672, d1734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9272 pattern childGuard
    simpa only [d1672, d1734, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1672, d1734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6476 pattern childGuard
    simpa only [d1672, d1734, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9274 (pattern : Twelve) (guard : d1852 pattern = 1) : d1670 pattern ≤ (0 : Int) + d1300 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d1670, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2402 pattern childGuard
    simpa only [d1852, d1670, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d1670, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5471 pattern childGuard
    simpa only [d1852, d1670, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9275 (pattern : Twelve) (guard : d1852 pattern = 1) : d1673 pattern ≤ (0 : Int) + d1735 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1673, d1735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9274 pattern childGuard
    simpa only [d1673, d1735, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1673, d1735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6525 pattern childGuard
    simpa only [d1673, d1735, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9276 (pattern : Twelve) (guard : d1852 pattern = 1) : d1675 pattern ≤ (0 : Int) + d1739 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1675, d1739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9273 pattern childGuard
    simpa only [d1675, d1739, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1675, d1739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9275 pattern childGuard
    simpa only [d1675, d1739, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9277 (pattern : Twelve) (guard : d1852 pattern = 1) : d1676 pattern ≤ (0 : Int) + d1741 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1676, d1741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9276 pattern childGuard
    simpa only [d1676, d1741, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1676, d1741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9265 pattern childGuard
    simpa only [d1676, d1741, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9278 (pattern : Twelve) (guard : d1852 pattern = 1) : d1677 pattern ≤ (0 : Int) + d1743 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1677, d1743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9270 pattern childGuard
    simpa only [d1677, d1743, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1677, d1743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9277 pattern childGuard
    simpa only [d1677, d1743, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9279 (pattern : Twelve) (guard : d1852 pattern = 1) : d1678 pattern ≤ (0 : Int) + d1744 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1678, d1744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9267 pattern childGuard
    simpa only [d1678, d1744, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1678, d1744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9278 pattern childGuard
    simpa only [d1678, d1744, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9280 (pattern : Twelve) (guard : d1869 pattern = 1) : d102 pattern ≤ (0 : Int) + d352 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d102, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4586 pattern childGuard
    simpa only [d1869, d102, d352, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d102, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c733 pattern childGuard
    simpa only [d1869, d102, d352, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9281 (pattern : Twelve) (guard : d1869 pattern = 1) : d103 pattern ≤ (0 : Int) + d353 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d103, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4588 pattern childGuard
    simpa only [d1869, d103, d353, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d103, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4078 pattern childGuard
    simpa only [d1869, d103, d353, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9282 (pattern : Twelve) (guard : d1869 pattern = 1) : d110 pattern ≤ (0 : Int) + d358 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d110, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9280 pattern childGuard
    simpa only [d110, d358, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d110, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9281 pattern childGuard
    simpa only [d110, d358, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9283 (pattern : Twelve) (guard : d0 pattern = 1) : d3 pattern ≤ (0 : Int) + d1 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9284 (pattern : Twelve) (guard : d1848 pattern = 1) : d37 pattern ≤ (0 : Int) + d27 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d37, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c240 pattern childGuard
    simpa only [d1848, d37, d27, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d37, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9283 pattern childGuard
    simpa only [d1848, d37, d27, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9285 (pattern : Twelve) (guard : d1848 pattern = 1) : d58 pattern ≤ (0 : Int) + d50 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d58, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1848 pattern childGuard
    simpa only [d58, d50, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d58, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9284 pattern childGuard
    simpa only [d58, d50, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9286 (pattern : Twelve) (guard : d1848 pattern = 1) : d79 pattern ≤ (0 : Int) + d72 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d79, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1610 pattern childGuard
    simpa only [d79, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d79, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9285 pattern childGuard
    simpa only [d79, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9287 (pattern : Twelve) (guard : d1848 pattern = 1) : d95 pattern ≤ (0 : Int) + d91 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d95, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9286 pattern childGuard
    simpa only [d95, d91, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d95, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4611 pattern childGuard
    simpa only [d95, d91, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9288 (pattern : Twelve) (guard : d0 pattern = 1) : d96 pattern ≤ (0 : Int) + d211 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9289 (pattern : Twelve) (guard : d1869 pattern = 1) : d104 pattern ≤ (0 : Int) + d354 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d104, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9287 pattern childGuard
    simpa only [d1869, d104, d354, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d104, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9288 pattern childGuard
    simpa only [d1869, d104, d354, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9290 (pattern : Twelve) (guard : d1848 pattern = 1) : d56 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1610 pattern childGuard
    simpa only [d56, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5045 pattern childGuard
    simpa only [d56, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9291 (pattern : Twelve) (guard : d1848 pattern = 1) : d57 pattern ≤ (0 : Int) + d50 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d57, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1848 pattern childGuard
    simpa only [d57, d50, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d57, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5106 pattern childGuard
    simpa only [d57, d50, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9292 (pattern : Twelve) (guard : d1848 pattern = 1) : d77 pattern ≤ (0 : Int) + d72 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d77, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9290 pattern childGuard
    simpa only [d77, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d77, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9291 pattern childGuard
    simpa only [d77, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9293 (pattern : Twelve) (guard : d1848 pattern = 1) : d78 pattern ≤ (0 : Int) + d76 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d78, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9290 pattern childGuard
    simpa only [d78, d76, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d78, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4603 pattern childGuard
    simpa only [d78, d76, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9294 (pattern : Twelve) (guard : d1848 pattern = 1) : d94 pattern ≤ (0 : Int) + d93 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d94, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9292 pattern childGuard
    simpa only [d94, d93, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d94, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9293 pattern childGuard
    simpa only [d94, d93, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9295 (pattern : Twelve) (guard : d1869 pattern = 1) : d105 pattern ≤ (0 : Int) + d355 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d105, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9294 pattern childGuard
    simpa only [d1869, d105, d355, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d105, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d1869, d105, d355, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9296 (pattern : Twelve) (guard : d1869 pattern = 1) : d111 pattern ≤ (0 : Int) + d359 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d111, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9289 pattern childGuard
    simpa only [d111, d359, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d111, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9295 pattern childGuard
    simpa only [d111, d359, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9297 (pattern : Twelve) (guard : d1869 pattern = 1) : d114 pattern ≤ (0 : Int) + d361 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d114, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9282 pattern childGuard
    simpa only [d114, d361, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d114, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9296 pattern childGuard
    simpa only [d114, d361, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9298 (pattern : Twelve) (guard : d1848 pattern = 1) : d91 pattern ≤ (0 : Int) + d97 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d91, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4609 pattern childGuard
    simpa only [d91, d97, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d91, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4596 pattern childGuard
    simpa only [d91, d97, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9299 (pattern : Twelve) (guard : d1869 pattern = 1) : d102 pattern ≤ (0 : Int) + d356 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d102, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9298 pattern childGuard
    simpa only [d1869, d102, d356, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d102, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c747 pattern childGuard
    simpa only [d1869, d102, d356, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9300 (pattern : Twelve) (guard : d1848 pattern = 1) : d76 pattern ≤ (0 : Int) + d80 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d76, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4403 pattern childGuard
    simpa only [d76, d80, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d76, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4603 pattern childGuard
    simpa only [d76, d80, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9301 (pattern : Twelve) (guard : d1848 pattern = 1) : d93 pattern ≤ (0 : Int) + d97 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d93, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4609 pattern childGuard
    simpa only [d93, d97, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d93, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9300 pattern childGuard
    simpa only [d93, d97, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9302 (pattern : Twelve) (guard : d1869 pattern = 1) : d103 pattern ≤ (0 : Int) + d356 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d103, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9301 pattern childGuard
    simpa only [d1869, d103, d356, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d103, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4088 pattern childGuard
    simpa only [d1869, d103, d356, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9303 (pattern : Twelve) (guard : d1869 pattern = 1) : d110 pattern ≤ (0 : Int) + d356 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9299 pattern childGuard
    simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9302 pattern childGuard
    simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9304 (pattern : Twelve) (guard : d1848 pattern = 1) : d95 pattern ≤ (0 : Int) + d97 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d95, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9286 pattern childGuard
    simpa only [d95, d97, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d95, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4618 pattern childGuard
    simpa only [d95, d97, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9305 (pattern : Twelve) (guard : d0 pattern = 1) : d96 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9306 (pattern : Twelve) (guard : d1869 pattern = 1) : d104 pattern ≤ (0 : Int) + d356 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d104, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9304 pattern childGuard
    simpa only [d1869, d104, d356, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d104, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9305 pattern childGuard
    simpa only [d1869, d104, d356, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9307 (pattern : Twelve) (guard : d1848 pattern = 1) : d56 pattern ≤ (0 : Int) + d30 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1567 pattern childGuard
    simpa only [d56, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5006 pattern childGuard
    simpa only [d56, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9308 (pattern : Twelve) (guard : d1848 pattern = 1) : d78 pattern ≤ (0 : Int) + d80 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d78, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9307 pattern childGuard
    simpa only [d78, d80, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d78, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4603 pattern childGuard
    simpa only [d78, d80, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9309 (pattern : Twelve) (guard : d1848 pattern = 1) : d94 pattern ≤ (0 : Int) + d97 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d94, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9292 pattern childGuard
    simpa only [d94, d97, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d94, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9308 pattern childGuard
    simpa only [d94, d97, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9310 (pattern : Twelve) (guard : d1869 pattern = 1) : d105 pattern ≤ (0 : Int) + d356 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d105, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9309 pattern childGuard
    simpa only [d1869, d105, d356, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d105, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d1869, d105, d356, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9311 (pattern : Twelve) (guard : d1869 pattern = 1) : d111 pattern ≤ (0 : Int) + d356 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9306 pattern childGuard
    simpa only [d111, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9310 pattern childGuard
    simpa only [d111, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9312 (pattern : Twelve) (guard : d1869 pattern = 1) : d114 pattern ≤ (0 : Int) + d356 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9303 pattern childGuard
    simpa only [d114, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9311 pattern childGuard
    simpa only [d114, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9313 (pattern : Twelve) (guard : d1869 pattern = 1) : d114 pattern ≤ (0 : Int) + d362 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9297 pattern childGuard
    simpa only [d362, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9312 pattern childGuard
    simpa only [d362, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9314 (pattern : Twelve) (guard : d1869 pattern = 1) : d102 pattern ≤ (0 : Int) + d357 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d102, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4586 pattern childGuard
    simpa only [d1869, d102, d357, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d102, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c747 pattern childGuard
    simpa only [d1869, d102, d357, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9315 (pattern : Twelve) (guard : d1869 pattern = 1) : d103 pattern ≤ (0 : Int) + d355 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d103, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4588 pattern childGuard
    simpa only [d1869, d103, d355, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d103, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4088 pattern childGuard
    simpa only [d1869, d103, d355, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9316 (pattern : Twelve) (guard : d1869 pattern = 1) : d110 pattern ≤ (0 : Int) + d360 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d110, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9314 pattern childGuard
    simpa only [d110, d360, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d110, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9315 pattern childGuard
    simpa only [d110, d360, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9317 (pattern : Twelve) (guard : d1869 pattern = 1) : d104 pattern ≤ (0 : Int) + d357 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d104, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9287 pattern childGuard
    simpa only [d1869, d104, d357, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d104, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9305 pattern childGuard
    simpa only [d1869, d104, d357, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9318 (pattern : Twelve) (guard : d1869 pattern = 1) : d111 pattern ≤ (0 : Int) + d360 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d111, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9317 pattern childGuard
    simpa only [d111, d360, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d111, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9295 pattern childGuard
    simpa only [d111, d360, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9319 (pattern : Twelve) (guard : d1869 pattern = 1) : d114 pattern ≤ (0 : Int) + d360 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9316 pattern childGuard
    simpa only [d114, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9318 pattern childGuard
    simpa only [d114, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9320 (pattern : Twelve) (guard : d1869 pattern = 1) : d114 pattern ≤ (0 : Int) + d363 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9319 pattern childGuard
    simpa only [d363, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9312 pattern childGuard
    simpa only [d363, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9321 (pattern : Twelve) (guard : d1869 pattern = 1) : d114 pattern ≤ (0 : Int) + d364 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9313 pattern childGuard
    simpa only [d364, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9320 pattern childGuard
    simpa only [d364, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9322 (pattern : Twelve) (guard : d0 pattern = 1) : d25 pattern ≤ (0 : Int) + d18 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9323 (pattern : Twelve) (guard : d1848 pattern = 1) : d120 pattern ≤ (0 : Int) + d28 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d120, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c240 pattern childGuard
    simpa only [d1848, d120, d28, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d120, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9322 pattern childGuard
    simpa only [d1848, d120, d28, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9324 (pattern : Twelve) (guard : d1848 pattern = 1) : d129 pattern ≤ (0 : Int) + d51 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d129, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9323 pattern childGuard
    simpa only [d129, d51, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d129, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2795 pattern childGuard
    simpa only [d129, d51, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9325 (pattern : Twelve) (guard : d1848 pattern = 1) : d136 pattern ≤ (0 : Int) + d73 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d136, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1560 pattern childGuard
    simpa only [d136, d73, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d136, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9324 pattern childGuard
    simpa only [d136, d73, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9326 (pattern : Twelve) (guard : d1848 pattern = 1) : d144 pattern ≤ (0 : Int) + d91 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d144, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4609 pattern childGuard
    simpa only [d144, d91, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d144, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9325 pattern childGuard
    simpa only [d144, d91, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9327 (pattern : Twelve) (guard : d0 pattern = 1) : d145 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9328 (pattern : Twelve) (guard : d1869 pattern = 1) : d149 pattern ≤ (0 : Int) + d357 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d149, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9326 pattern childGuard
    simpa only [d1869, d149, d357, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d149, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9327 pattern childGuard
    simpa only [d1869, d149, d357, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9329 (pattern : Twelve) (guard : d1848 pattern = 1) : d120 pattern ≤ (0 : Int) + d34 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d120, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c240 pattern childGuard
    simpa only [d1848, d120, d34, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d120, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1990 pattern childGuard
    simpa only [d1848, d120, d34, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9330 (pattern : Twelve) (guard : d1848 pattern = 1) : d129 pattern ≤ (0 : Int) + d55 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d129, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9329 pattern childGuard
    simpa only [d129, d55, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d129, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2795 pattern childGuard
    simpa only [d129, d55, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9331 (pattern : Twelve) (guard : d1848 pattern = 1) : d136 pattern ≤ (0 : Int) + d76 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d136, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1560 pattern childGuard
    simpa only [d136, d76, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d136, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9330 pattern childGuard
    simpa only [d136, d76, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9332 (pattern : Twelve) (guard : d1848 pattern = 1) : d144 pattern ≤ (0 : Int) + d93 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d144, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4609 pattern childGuard
    simpa only [d144, d93, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d144, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9331 pattern childGuard
    simpa only [d144, d93, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9333 (pattern : Twelve) (guard : d0 pattern = 1) : d146 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9334 (pattern : Twelve) (guard : d1869 pattern = 1) : d150 pattern ≤ (0 : Int) + d355 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d150, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9332 pattern childGuard
    simpa only [d1869, d150, d355, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d150, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9333 pattern childGuard
    simpa only [d1869, d150, d355, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9335 (pattern : Twelve) (guard : d1869 pattern = 1) : d153 pattern ≤ (0 : Int) + d360 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d153, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9328 pattern childGuard
    simpa only [d153, d360, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d153, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9334 pattern childGuard
    simpa only [d153, d360, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9336 (pattern : Twelve) (guard : d1848 pattern = 1) : d121 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d121, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1848, d121, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d121, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1917 pattern childGuard
    simpa only [d1848, d121, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9337 (pattern : Twelve) (guard : d0 pattern = 1) : d4 pattern ≤ (0 : Int) + d1 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9338 (pattern : Twelve) (guard : d1848 pattern = 1) : d122 pattern ≤ (0 : Int) + d27 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d122, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c240 pattern childGuard
    simpa only [d1848, d122, d27, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d122, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9337 pattern childGuard
    simpa only [d1848, d122, d27, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9339 (pattern : Twelve) (guard : d1848 pattern = 1) : d131 pattern ≤ (0 : Int) + d50 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d131, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9336 pattern childGuard
    simpa only [d131, d50, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d131, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9338 pattern childGuard
    simpa only [d131, d50, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9340 (pattern : Twelve) (guard : d1848 pattern = 1) : d140 pattern ≤ (0 : Int) + d72 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d140, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1610 pattern childGuard
    simpa only [d140, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d140, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9339 pattern childGuard
    simpa only [d140, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9341 (pattern : Twelve) (guard : d1848 pattern = 1) : d123 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1848, d123, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7061 pattern childGuard
    simpa only [d1848, d123, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9342 (pattern : Twelve) (guard : d1848 pattern = 1) : d132 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1610 pattern childGuard
    simpa only [d132, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9341 pattern childGuard
    simpa only [d132, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9343 (pattern : Twelve) (guard : d1848 pattern = 1) : d141 pattern ≤ (0 : Int) + d73 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d141, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9342 pattern childGuard
    simpa only [d141, d73, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d141, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9324 pattern childGuard
    simpa only [d141, d73, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9344 (pattern : Twelve) (guard : d1848 pattern = 1) : d147 pattern ≤ (0 : Int) + d91 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d147, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9340 pattern childGuard
    simpa only [d147, d91, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d147, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9343 pattern childGuard
    simpa only [d147, d91, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9345 (pattern : Twelve) (guard : d0 pattern = 1) : d148 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9346 (pattern : Twelve) (guard : d1869 pattern = 1) : d151 pattern ≤ (0 : Int) + d357 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d151, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9344 pattern childGuard
    simpa only [d1869, d151, d357, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d151, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9345 pattern childGuard
    simpa only [d1869, d151, d357, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9347 (pattern : Twelve) (guard : d1848 pattern = 1) : d130 pattern ≤ (0 : Int) + d50 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d130, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9336 pattern childGuard
    simpa only [d130, d50, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d130, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5106 pattern childGuard
    simpa only [d130, d50, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9348 (pattern : Twelve) (guard : d1848 pattern = 1) : d139 pattern ≤ (0 : Int) + d72 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d139, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9290 pattern childGuard
    simpa only [d139, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d139, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9347 pattern childGuard
    simpa only [d139, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9349 (pattern : Twelve) (guard : d1848 pattern = 1) : d138 pattern ≤ (0 : Int) + d76 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d138, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9290 pattern childGuard
    simpa only [d138, d76, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d138, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9330 pattern childGuard
    simpa only [d138, d76, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9350 (pattern : Twelve) (guard : d1848 pattern = 1) : d146 pattern ≤ (0 : Int) + d93 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d146, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9348 pattern childGuard
    simpa only [d146, d93, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d146, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9349 pattern childGuard
    simpa only [d146, d93, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9351 (pattern : Twelve) (guard : d1869 pattern = 1) : d152 pattern ≤ (0 : Int) + d355 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d152, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9350 pattern childGuard
    simpa only [d1869, d152, d355, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d152, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d1869, d152, d355, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9352 (pattern : Twelve) (guard : d1869 pattern = 1) : d154 pattern ≤ (0 : Int) + d360 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d154, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9346 pattern childGuard
    simpa only [d154, d360, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d154, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9351 pattern childGuard
    simpa only [d154, d360, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9353 (pattern : Twelve) (guard : d1869 pattern = 1) : d155 pattern ≤ (0 : Int) + d360 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9335 pattern childGuard
    simpa only [d155, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9352 pattern childGuard
    simpa only [d155, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9354 (pattern : Twelve) (guard : d1848 pattern = 1) : d136 pattern ≤ (0 : Int) + d80 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d136, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4403 pattern childGuard
    simpa only [d136, d80, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d136, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9330 pattern childGuard
    simpa only [d136, d80, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9355 (pattern : Twelve) (guard : d1848 pattern = 1) : d144 pattern ≤ (0 : Int) + d97 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d144, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4609 pattern childGuard
    simpa only [d144, d97, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d144, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9354 pattern childGuard
    simpa only [d144, d97, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9356 (pattern : Twelve) (guard : d1869 pattern = 1) : d149 pattern ≤ (0 : Int) + d356 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d149, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9355 pattern childGuard
    simpa only [d1869, d149, d356, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d149, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9327 pattern childGuard
    simpa only [d1869, d149, d356, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9357 (pattern : Twelve) (guard : d1869 pattern = 1) : d150 pattern ≤ (0 : Int) + d356 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d150, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9355 pattern childGuard
    simpa only [d1869, d150, d356, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d150, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9333 pattern childGuard
    simpa only [d1869, d150, d356, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9358 (pattern : Twelve) (guard : d1869 pattern = 1) : d153 pattern ≤ (0 : Int) + d356 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9356 pattern childGuard
    simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9357 pattern childGuard
    simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9359 (pattern : Twelve) (guard : d1848 pattern = 1) : d123 pattern ≤ (0 : Int) + d30 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d123, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1848, d123, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d123, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7759 pattern childGuard
    simpa only [d1848, d123, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9360 (pattern : Twelve) (guard : d1848 pattern = 1) : d132 pattern ≤ (0 : Int) + d30 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1567 pattern childGuard
    simpa only [d132, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9359 pattern childGuard
    simpa only [d132, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9361 (pattern : Twelve) (guard : d1848 pattern = 1) : d141 pattern ≤ (0 : Int) + d80 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d141, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9360 pattern childGuard
    simpa only [d141, d80, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d141, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9330 pattern childGuard
    simpa only [d141, d80, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9362 (pattern : Twelve) (guard : d1848 pattern = 1) : d147 pattern ≤ (0 : Int) + d97 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d147, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9340 pattern childGuard
    simpa only [d147, d97, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d147, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9361 pattern childGuard
    simpa only [d147, d97, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9363 (pattern : Twelve) (guard : d1869 pattern = 1) : d151 pattern ≤ (0 : Int) + d356 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d151, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9362 pattern childGuard
    simpa only [d1869, d151, d356, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d151, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9345 pattern childGuard
    simpa only [d1869, d151, d356, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9364 (pattern : Twelve) (guard : d1848 pattern = 1) : d138 pattern ≤ (0 : Int) + d80 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d138, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9307 pattern childGuard
    simpa only [d138, d80, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d138, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9330 pattern childGuard
    simpa only [d138, d80, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9365 (pattern : Twelve) (guard : d1848 pattern = 1) : d146 pattern ≤ (0 : Int) + d97 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d146, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9348 pattern childGuard
    simpa only [d146, d97, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d146, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9364 pattern childGuard
    simpa only [d146, d97, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9366 (pattern : Twelve) (guard : d1869 pattern = 1) : d152 pattern ≤ (0 : Int) + d356 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d152, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9365 pattern childGuard
    simpa only [d1869, d152, d356, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d152, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d1869, d152, d356, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9367 (pattern : Twelve) (guard : d1869 pattern = 1) : d154 pattern ≤ (0 : Int) + d356 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9363 pattern childGuard
    simpa only [d154, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9366 pattern childGuard
    simpa only [d154, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9368 (pattern : Twelve) (guard : d1869 pattern = 1) : d155 pattern ≤ (0 : Int) + d356 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9358 pattern childGuard
    simpa only [d155, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9367 pattern childGuard
    simpa only [d155, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9369 (pattern : Twelve) (guard : d1869 pattern = 1) : d155 pattern ≤ (0 : Int) + d363 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9353 pattern childGuard
    simpa only [d363, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9368 pattern childGuard
    simpa only [d363, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9370 (pattern : Twelve) (guard : d1869 pattern = 1) : d156 pattern ≤ (0 : Int) + d365 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d156, d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9321 pattern childGuard
    simpa only [d156, d365, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d156, d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9369 pattern childGuard
    simpa only [d156, d365, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9371 (pattern : Twelve) (guard : d1869 pattern = 1) : d861 pattern ≤ (0 : Int) + d1018 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d861, d1018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4686 pattern childGuard
    simpa only [d1869, d861, d1018, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d861, d1018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c757 pattern childGuard
    simpa only [d1869, d861, d1018, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9372 (pattern : Twelve) (guard : d1869 pattern = 1) : d861 pattern ≤ (0 : Int) + d1019 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d861, d1019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4686 pattern childGuard
    simpa only [d1869, d861, d1019, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d861, d1019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4096 pattern childGuard
    simpa only [d1869, d861, d1019, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9373 (pattern : Twelve) (guard : d1869 pattern = 1) : d861 pattern ≤ (0 : Int) + d1023 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9371 pattern childGuard
    simpa only [d1023, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9372 pattern childGuard
    simpa only [d1023, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9374 (pattern : Twelve) (guard : d1848 pattern = 1) : d819 pattern ≤ (0 : Int) + d816 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d819, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4215 pattern childGuard
    simpa only [d1848, d819, d816, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d819, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9283 pattern childGuard
    simpa only [d1848, d819, d816, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9375 (pattern : Twelve) (guard : d1848 pattern = 1) : d828 pattern ≤ (0 : Int) + d824 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d828, d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1918 pattern childGuard
    simpa only [d828, d824, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d828, d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9374 pattern childGuard
    simpa only [d828, d824, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9376 (pattern : Twelve) (guard : d1848 pattern = 1) : d842 pattern ≤ (0 : Int) + d838 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d842, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1610 pattern childGuard
    simpa only [d842, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d842, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9375 pattern childGuard
    simpa only [d842, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9377 (pattern : Twelve) (guard : d1848 pattern = 1) : d843 pattern ≤ (0 : Int) + d839 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d843, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1922 pattern childGuard
    simpa only [d843, d839, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d843, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4693 pattern childGuard
    simpa only [d843, d839, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9378 (pattern : Twelve) (guard : d1848 pattern = 1) : d855 pattern ≤ (0 : Int) + d853 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d855, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9376 pattern childGuard
    simpa only [d855, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d855, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9377 pattern childGuard
    simpa only [d855, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9379 (pattern : Twelve) (guard : d0 pattern = 1) : d856 pattern ≤ (0 : Int) + d916 pattern := by
  change (0 : Int) = 1 at guard
  omega
end NetHack.Sokoban21.Diagram
