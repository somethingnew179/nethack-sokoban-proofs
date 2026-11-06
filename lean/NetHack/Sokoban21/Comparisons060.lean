/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons059
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c8400 (pattern : Twelve) (guard : d1867 pattern = 1) : d1608 pattern ≤ (0 : Int) + d1549 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1608, d1549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8398 pattern childGuard
    simpa only [d1608, d1549, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1608, d1549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8399 pattern childGuard
    simpa only [d1608, d1549, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8401 (pattern : Twelve) (guard : d1867 pattern = 1) : d1610 pattern ≤ (0 : Int) + d1551 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1610, d1551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8385 pattern childGuard
    simpa only [d1610, d1551, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1610, d1551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8400 pattern childGuard
    simpa only [d1610, d1551, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8402 (pattern : Twelve) (guard : d1867 pattern = 1) : d1611 pattern ≤ (0 : Int) + d1552 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1611, d1552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8384 pattern childGuard
    simpa only [d1611, d1552, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1611, d1552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8400 pattern childGuard
    simpa only [d1611, d1552, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8403 (pattern : Twelve) (guard : d1867 pattern = 1) : d1613 pattern ≤ (0 : Int) + d1554 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1613, d1554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8401 pattern childGuard
    simpa only [d1613, d1554, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1613, d1554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8402 pattern childGuard
    simpa only [d1613, d1554, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8404 (pattern : Twelve) (guard : d1867 pattern = 1) : d1614 pattern ≤ (0 : Int) + d1555 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1614, d1555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8403 pattern childGuard
    simpa only [d1614, d1555, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1614, d1555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8402 pattern childGuard
    simpa only [d1614, d1555, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8405 (pattern : Twelve) (guard : d1867 pattern = 1) : d635 pattern ≤ (0 : Int) + d1494 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d635, d1494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7752 pattern childGuard
    simpa only [d1867, d635, d1494, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d635, d1494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8138 pattern childGuard
    simpa only [d1867, d635, d1494, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8406 (pattern : Twelve) (guard : d1867 pattern = 1) : d1559 pattern ≤ (0 : Int) + d1499 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1559, d1499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8291 pattern childGuard
    simpa only [d1559, d1499, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1559, d1499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8405 pattern childGuard
    simpa only [d1559, d1499, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8407 (pattern : Twelve) (guard : d1867 pattern = 1) : d1560 pattern ≤ (0 : Int) + d1500 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1560, d1500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8130 pattern childGuard
    simpa only [d1560, d1500, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1560, d1500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8405 pattern childGuard
    simpa only [d1560, d1500, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8408 (pattern : Twelve) (guard : d1867 pattern = 1) : d1570 pattern ≤ (0 : Int) + d1511 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1570, d1511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8406 pattern childGuard
    simpa only [d1570, d1511, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1570, d1511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8407 pattern childGuard
    simpa only [d1570, d1511, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8409 (pattern : Twelve) (guard : d1867 pattern = 1) : d1585 pattern ≤ (0 : Int) + d1526 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1585, d1526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8135 pattern childGuard
    simpa only [d1585, d1526, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1585, d1526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8408 pattern childGuard
    simpa only [d1585, d1526, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8410 (pattern : Twelve) (guard : d1867 pattern = 1) : d1596 pattern ≤ (0 : Int) + d1537 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1596, d1537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8409 pattern childGuard
    simpa only [d1596, d1537, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1596, d1537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8372 pattern childGuard
    simpa only [d1596, d1537, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8411 (pattern : Twelve) (guard : d1867 pattern = 1) : d1571 pattern ≤ (0 : Int) + d1512 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1571, d1512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8315 pattern childGuard
    simpa only [d1571, d1512, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1571, d1512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8375 pattern childGuard
    simpa only [d1571, d1512, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8412 (pattern : Twelve) (guard : d1867 pattern = 1) : d1586 pattern ≤ (0 : Int) + d1527 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1586, d1527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8186 pattern childGuard
    simpa only [d1586, d1527, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1586, d1527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8411 pattern childGuard
    simpa only [d1586, d1527, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8413 (pattern : Twelve) (guard : d1867 pattern = 1) : d1597 pattern ≤ (0 : Int) + d1538 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1597, d1538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8412 pattern childGuard
    simpa only [d1597, d1538, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1597, d1538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8379 pattern childGuard
    simpa only [d1597, d1538, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8414 (pattern : Twelve) (guard : d1867 pattern = 1) : d1604 pattern ≤ (0 : Int) + d1545 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1604, d1545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8410 pattern childGuard
    simpa only [d1604, d1545, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1604, d1545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8413 pattern childGuard
    simpa only [d1604, d1545, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8415 (pattern : Twelve) (guard : d1867 pattern = 1) : d1561 pattern ≤ (0 : Int) + d1501 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1561, d1501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8130 pattern childGuard
    simpa only [d1561, d1501, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1561, d1501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8391 pattern childGuard
    simpa only [d1561, d1501, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8416 (pattern : Twelve) (guard : d1867 pattern = 1) : d1572 pattern ≤ (0 : Int) + d1513 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1572, d1513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8315 pattern childGuard
    simpa only [d1572, d1513, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1572, d1513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8415 pattern childGuard
    simpa only [d1572, d1513, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8417 (pattern : Twelve) (guard : d1867 pattern = 1) : d1587 pattern ≤ (0 : Int) + d1528 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1587, d1528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8164 pattern childGuard
    simpa only [d1587, d1528, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1587, d1528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8416 pattern childGuard
    simpa only [d1587, d1528, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8418 (pattern : Twelve) (guard : d1867 pattern = 1) : d1562 pattern ≤ (0 : Int) + d1502 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1562, d1502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8141 pattern childGuard
    simpa only [d1562, d1502, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1562, d1502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8153 pattern childGuard
    simpa only [d1562, d1502, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8419 (pattern : Twelve) (guard : d1867 pattern = 1) : d1573 pattern ≤ (0 : Int) + d1514 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1573, d1514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8296 pattern childGuard
    simpa only [d1573, d1514, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1573, d1514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8418 pattern childGuard
    simpa only [d1573, d1514, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8420 (pattern : Twelve) (guard : d1867 pattern = 1) : d1588 pattern ≤ (0 : Int) + d1529 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1588, d1529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8419 pattern childGuard
    simpa only [d1588, d1529, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1588, d1529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d1588, d1529, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8421 (pattern : Twelve) (guard : d1867 pattern = 1) : d1598 pattern ≤ (0 : Int) + d1539 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1598, d1539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8417 pattern childGuard
    simpa only [d1598, d1539, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1598, d1539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8420 pattern childGuard
    simpa only [d1598, d1539, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8422 (pattern : Twelve) (guard : d1867 pattern = 1) : d822 pattern ≤ (0 : Int) + d1503 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d822, d1503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8391 pattern childGuard
    simpa only [d822, d1503, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d822, d1503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d822, d1503, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8423 (pattern : Twelve) (guard : d1867 pattern = 1) : d1574 pattern ≤ (0 : Int) + d1515 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1574, d1515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8321 pattern childGuard
    simpa only [d1574, d1515, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1574, d1515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8422 pattern childGuard
    simpa only [d1574, d1515, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8424 (pattern : Twelve) (guard : d1867 pattern = 1) : d1589 pattern ≤ (0 : Int) + d1530 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1589, d1530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8214 pattern childGuard
    simpa only [d1589, d1530, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1589, d1530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8423 pattern childGuard
    simpa only [d1589, d1530, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8425 (pattern : Twelve) (guard : d1867 pattern = 1) : d1563 pattern ≤ (0 : Int) + d1504 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1563, d1504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8216 pattern childGuard
    simpa only [d1563, d1504, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1563, d1504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3302 pattern childGuard
    simpa only [d1563, d1504, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8426 (pattern : Twelve) (guard : d1867 pattern = 1) : d1575 pattern ≤ (0 : Int) + d1516 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1575, d1516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8425 pattern childGuard
    simpa only [d1575, d1516, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1575, d1516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8282 pattern childGuard
    simpa only [d1575, d1516, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8427 (pattern : Twelve) (guard : d1867 pattern = 1) : d1590 pattern ≤ (0 : Int) + d1531 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1590, d1531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8426 pattern childGuard
    simpa only [d1590, d1531, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1590, d1531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d1590, d1531, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8428 (pattern : Twelve) (guard : d1867 pattern = 1) : d1599 pattern ≤ (0 : Int) + d1540 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1599, d1540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8424 pattern childGuard
    simpa only [d1599, d1540, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1599, d1540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8427 pattern childGuard
    simpa only [d1599, d1540, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8429 (pattern : Twelve) (guard : d1867 pattern = 1) : d1605 pattern ≤ (0 : Int) + d1546 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1605, d1546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8421 pattern childGuard
    simpa only [d1605, d1546, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1605, d1546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8428 pattern childGuard
    simpa only [d1605, d1546, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8430 (pattern : Twelve) (guard : d1867 pattern = 1) : d1606 pattern ≤ (0 : Int) + d1547 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1606, d1547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8413 pattern childGuard
    simpa only [d1606, d1547, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1606, d1547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d1606, d1547, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8431 (pattern : Twelve) (guard : d1867 pattern = 1) : d1609 pattern ≤ (0 : Int) + d1550 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1609, d1550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8429 pattern childGuard
    simpa only [d1609, d1550, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1609, d1550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8430 pattern childGuard
    simpa only [d1609, d1550, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8432 (pattern : Twelve) (guard : d1867 pattern = 1) : d1612 pattern ≤ (0 : Int) + d1553 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1612, d1553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8414 pattern childGuard
    simpa only [d1612, d1553, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1612, d1553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8431 pattern childGuard
    simpa only [d1612, d1553, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8433 (pattern : Twelve) (guard : d1867 pattern = 1) : d1615 pattern ≤ (0 : Int) + d1556 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1615, d1556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8404 pattern childGuard
    simpa only [d1615, d1556, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1615, d1556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8432 pattern childGuard
    simpa only [d1615, d1556, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8434 (pattern : Twelve) (guard : d1867 pattern = 1) : d1788 pattern ≤ (0 : Int) + d1753 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1788, d1753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8141 pattern childGuard
    simpa only [d1788, d1753, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1788, d1753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8405 pattern childGuard
    simpa only [d1788, d1753, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8435 (pattern : Twelve) (guard : d1867 pattern = 1) : d1789 pattern ≤ (0 : Int) + d1754 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1789, d1754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8216 pattern childGuard
    simpa only [d1789, d1754, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1789, d1754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d1789, d1754, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8436 (pattern : Twelve) (guard : d1867 pattern = 1) : d1797 pattern ≤ (0 : Int) + d1763 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1797, d1763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8434 pattern childGuard
    simpa only [d1797, d1763, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1797, d1763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8435 pattern childGuard
    simpa only [d1797, d1763, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8437 (pattern : Twelve) (guard : d1867 pattern = 1) : d1780 pattern ≤ (0 : Int) + d1745 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1780, d1745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8405 pattern childGuard
    simpa only [d1780, d1745, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1780, d1745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8153 pattern childGuard
    simpa only [d1780, d1745, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8438 (pattern : Twelve) (guard : d1867 pattern = 1) : d1781 pattern ≤ (0 : Int) + d1746 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1781, d1746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8405 pattern childGuard
    simpa only [d1781, d1746, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1781, d1746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d1781, d1746, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8439 (pattern : Twelve) (guard : d1867 pattern = 1) : d1784 pattern ≤ (0 : Int) + d1749 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1784, d1749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8437 pattern childGuard
    simpa only [d1784, d1749, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1784, d1749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8438 pattern childGuard
    simpa only [d1784, d1749, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8440 (pattern : Twelve) (guard : d1867 pattern = 1) : d1790 pattern ≤ (0 : Int) + d1755 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1790, d1755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8378 pattern childGuard
    simpa only [d1790, d1755, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1790, d1755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8439 pattern childGuard
    simpa only [d1790, d1755, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8441 (pattern : Twelve) (guard : d1867 pattern = 1) : d1798 pattern ≤ (0 : Int) + d1764 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1798, d1764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8440 pattern childGuard
    simpa only [d1798, d1764, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1798, d1764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8396 pattern childGuard
    simpa only [d1798, d1764, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8442 (pattern : Twelve) (guard : d1867 pattern = 1) : d1804 pattern ≤ (0 : Int) + d1770 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1804, d1770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8436 pattern childGuard
    simpa only [d1804, d1770, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1804, d1770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8441 pattern childGuard
    simpa only [d1804, d1770, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8443 (pattern : Twelve) (guard : d1867 pattern = 1) : d1791 pattern ≤ (0 : Int) + d1756 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1791, d1756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8296 pattern childGuard
    simpa only [d1791, d1756, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1791, d1756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8437 pattern childGuard
    simpa only [d1791, d1756, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8444 (pattern : Twelve) (guard : d1867 pattern = 1) : d1792 pattern ≤ (0 : Int) + d1757 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1792, d1757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8324 pattern childGuard
    simpa only [d1792, d1757, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1792, d1757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d1792, d1757, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8445 (pattern : Twelve) (guard : d1867 pattern = 1) : d1799 pattern ≤ (0 : Int) + d1765 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1799, d1765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8443 pattern childGuard
    simpa only [d1799, d1765, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1799, d1765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8444 pattern childGuard
    simpa only [d1799, d1765, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8446 (pattern : Twelve) (guard : d1867 pattern = 1) : d1782 pattern ≤ (0 : Int) + d1747 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1782, d1747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8153 pattern childGuard
    simpa only [d1782, d1747, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1782, d1747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3302 pattern childGuard
    simpa only [d1782, d1747, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8447 (pattern : Twelve) (guard : d1867 pattern = 1) : d1785 pattern ≤ (0 : Int) + d1750 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1785, d1750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8446 pattern childGuard
    simpa only [d1785, d1750, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1785, d1750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8282 pattern childGuard
    simpa only [d1785, d1750, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8448 (pattern : Twelve) (guard : d1867 pattern = 1) : d1793 pattern ≤ (0 : Int) + d1758 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1793, d1758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8395 pattern childGuard
    simpa only [d1793, d1758, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1793, d1758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8447 pattern childGuard
    simpa only [d1793, d1758, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8449 (pattern : Twelve) (guard : d1867 pattern = 1) : d1655 pattern ≤ (0 : Int) + d1759 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1655, d1759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8325 pattern childGuard
    simpa only [d1655, d1759, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1655, d1759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d1655, d1759, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8450 (pattern : Twelve) (guard : d1867 pattern = 1) : d1800 pattern ≤ (0 : Int) + d1766 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1800, d1766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8448 pattern childGuard
    simpa only [d1800, d1766, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1800, d1766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8449 pattern childGuard
    simpa only [d1800, d1766, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8451 (pattern : Twelve) (guard : d1867 pattern = 1) : d1805 pattern ≤ (0 : Int) + d1771 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1805, d1771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8445 pattern childGuard
    simpa only [d1805, d1771, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1805, d1771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8450 pattern childGuard
    simpa only [d1805, d1771, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8452 (pattern : Twelve) (guard : d1867 pattern = 1) : d1806 pattern ≤ (0 : Int) + d1772 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1806, d1772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8441 pattern childGuard
    simpa only [d1806, d1772, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1806, d1772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d1806, d1772, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8453 (pattern : Twelve) (guard : d1867 pattern = 1) : d1809 pattern ≤ (0 : Int) + d1775 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1809, d1775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8451 pattern childGuard
    simpa only [d1809, d1775, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1809, d1775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8452 pattern childGuard
    simpa only [d1809, d1775, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8454 (pattern : Twelve) (guard : d1867 pattern = 1) : d1811 pattern ≤ (0 : Int) + d1777 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1811, d1777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8442 pattern childGuard
    simpa only [d1811, d1777, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1811, d1777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8453 pattern childGuard
    simpa only [d1811, d1777, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8455 (pattern : Twelve) (guard : d1867 pattern = 1) : d1794 pattern ≤ (0 : Int) + d1760 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1794, d1760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8141 pattern childGuard
    simpa only [d1794, d1760, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1794, d1760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8437 pattern childGuard
    simpa only [d1794, d1760, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8456 (pattern : Twelve) (guard : d1867 pattern = 1) : d1801 pattern ≤ (0 : Int) + d1767 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1801, d1767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8455 pattern childGuard
    simpa only [d1801, d1767, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1801, d1767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8435 pattern childGuard
    simpa only [d1801, d1767, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8457 (pattern : Twelve) (guard : d1867 pattern = 1) : d1807 pattern ≤ (0 : Int) + d1773 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1807, d1773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8456 pattern childGuard
    simpa only [d1807, d1773, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1807, d1773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8441 pattern childGuard
    simpa only [d1807, d1773, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8458 (pattern : Twelve) (guard : d1867 pattern = 1) : d1783 pattern ≤ (0 : Int) + d1748 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1783, d1748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8405 pattern childGuard
    simpa only [d1783, d1748, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1783, d1748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3302 pattern childGuard
    simpa only [d1783, d1748, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8459 (pattern : Twelve) (guard : d1867 pattern = 1) : d1786 pattern ≤ (0 : Int) + d1751 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1786, d1751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8437 pattern childGuard
    simpa only [d1786, d1751, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1786, d1751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8458 pattern childGuard
    simpa only [d1786, d1751, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8460 (pattern : Twelve) (guard : d1867 pattern = 1) : d1795 pattern ≤ (0 : Int) + d1761 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1795, d1761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8296 pattern childGuard
    simpa only [d1795, d1761, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1795, d1761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8459 pattern childGuard
    simpa only [d1795, d1761, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8461 (pattern : Twelve) (guard : d1867 pattern = 1) : d1802 pattern ≤ (0 : Int) + d1768 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1802, d1768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8460 pattern childGuard
    simpa only [d1802, d1768, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1802, d1768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8396 pattern childGuard
    simpa only [d1802, d1768, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8462 (pattern : Twelve) (guard : d1867 pattern = 1) : d1787 pattern ≤ (0 : Int) + d1752 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1787, d1752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8282 pattern childGuard
    simpa only [d1787, d1752, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1787, d1752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3663 pattern childGuard
    simpa only [d1787, d1752, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8463 (pattern : Twelve) (guard : d1867 pattern = 1) : d1796 pattern ≤ (0 : Int) + d1762 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1796, d1762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8395 pattern childGuard
    simpa only [d1796, d1762, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1796, d1762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8462 pattern childGuard
    simpa only [d1796, d1762, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8464 (pattern : Twelve) (guard : d1867 pattern = 1) : d1252 pattern ≤ (0 : Int) + d191 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1252, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8325 pattern childGuard
    simpa only [d1252, d191, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1252, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d1252, d191, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8465 (pattern : Twelve) (guard : d1867 pattern = 1) : d1626 pattern ≤ (0 : Int) + d202 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1626, d202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8464 pattern childGuard
    simpa only [d1626, d202, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1626, d202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d1626, d202, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8466 (pattern : Twelve) (guard : d1867 pattern = 1) : d1803 pattern ≤ (0 : Int) + d1769 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1803, d1769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8463 pattern childGuard
    simpa only [d1803, d1769, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1803, d1769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8465 pattern childGuard
    simpa only [d1803, d1769, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8467 (pattern : Twelve) (guard : d1867 pattern = 1) : d1808 pattern ≤ (0 : Int) + d1774 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1808, d1774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8461 pattern childGuard
    simpa only [d1808, d1774, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1808, d1774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8466 pattern childGuard
    simpa only [d1808, d1774, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8468 (pattern : Twelve) (guard : d1867 pattern = 1) : d1810 pattern ≤ (0 : Int) + d1776 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1810, d1776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8467 pattern childGuard
    simpa only [d1810, d1776, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1810, d1776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8452 pattern childGuard
    simpa only [d1810, d1776, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8469 (pattern : Twelve) (guard : d1867 pattern = 1) : d1812 pattern ≤ (0 : Int) + d1778 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1812, d1778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8457 pattern childGuard
    simpa only [d1812, d1778, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1812, d1778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8468 pattern childGuard
    simpa only [d1812, d1778, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8470 (pattern : Twelve) (guard : d1867 pattern = 1) : d1813 pattern ≤ (0 : Int) + d1779 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1813, d1779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8454 pattern childGuard
    simpa only [d1813, d1779, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1813, d1779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8469 pattern childGuard
    simpa only [d1813, d1779, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8471 (pattern : Twelve) (guard : d0 pattern = 1) : d7 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c8472 (pattern : Twelve) (guard : d1867 pattern = 1) : d7 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7730 pattern childGuard
    simpa only [d1867, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8471 pattern childGuard
    simpa only [d1867, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8473 (pattern : Twelve) (guard : d1867 pattern = 1) : d646 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3245 pattern childGuard
    simpa only [d646, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8472 pattern childGuard
    simpa only [d646, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8474 (pattern : Twelve) (guard : d1867 pattern = 1) : d634 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7730 pattern childGuard
    simpa only [d1867, d634, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6994 pattern childGuard
    simpa only [d1867, d634, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8475 (pattern : Twelve) (guard : d1867 pattern = 1) : d647 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3245 pattern childGuard
    simpa only [d647, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8474 pattern childGuard
    simpa only [d647, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8476 (pattern : Twelve) (guard : d1867 pattern = 1) : d680 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8473 pattern childGuard
    simpa only [d680, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8475 pattern childGuard
    simpa only [d680, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8477 (pattern : Twelve) (guard : d1867 pattern = 1) : d161 pattern ≤ (0 : Int) + d1 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3253 pattern childGuard
    simpa only [d1867, d161, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6985 pattern childGuard
    simpa only [d1867, d161, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8478 (pattern : Twelve) (guard : d1867 pattern = 1) : d171 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d171, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3245 pattern childGuard
    simpa only [d171, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d171, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8477 pattern childGuard
    simpa only [d171, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8479 (pattern : Twelve) (guard : d1867 pattern = 1) : d162 pattern ≤ (0 : Int) + d17 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d162, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3256 pattern childGuard
    simpa only [d1867, d162, d17, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d162, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6988 pattern childGuard
    simpa only [d1867, d162, d17, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8480 (pattern : Twelve) (guard : d1867 pattern = 1) : d157 pattern ≤ (0 : Int) + d1 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7736 pattern childGuard
    simpa only [d1867, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6985 pattern childGuard
    simpa only [d1867, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8481 (pattern : Twelve) (guard : d1867 pattern = 1) : d648 pattern ≤ (0 : Int) + d27 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d648, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8479 pattern childGuard
    simpa only [d648, d27, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d648, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8480 pattern childGuard
    simpa only [d648, d27, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8482 (pattern : Twelve) (guard : d1867 pattern = 1) : d681 pattern ≤ (0 : Int) + d50 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d681, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8478 pattern childGuard
    simpa only [d681, d50, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d681, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8481 pattern childGuard
    simpa only [d681, d50, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8483 (pattern : Twelve) (guard : d1867 pattern = 1) : d709 pattern ≤ (0 : Int) + d72 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d709, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8476 pattern childGuard
    simpa only [d709, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d709, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8482 pattern childGuard
    simpa only [d709, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8484 (pattern : Twelve) (guard : d1867 pattern = 1) : d162 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3256 pattern childGuard
    simpa only [d1867, d162, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6994 pattern childGuard
    simpa only [d1867, d162, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8485 (pattern : Twelve) (guard : d1867 pattern = 1) : d158 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7732 pattern childGuard
    simpa only [d1867, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6994 pattern childGuard
    simpa only [d1867, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8486 (pattern : Twelve) (guard : d1867 pattern = 1) : d649 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8484 pattern childGuard
    simpa only [d649, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8485 pattern childGuard
    simpa only [d649, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8487 (pattern : Twelve) (guard : d1867 pattern = 1) : d682 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8475 pattern childGuard
    simpa only [d682, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8486 pattern childGuard
    simpa only [d682, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8488 (pattern : Twelve) (guard : d0 pattern = 1) : d160 pattern ≤ (0 : Int) + d9 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c8489 (pattern : Twelve) (guard : d1867 pattern = 1) : d635 pattern ≤ (0 : Int) + d18 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d635, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7747 pattern childGuard
    simpa only [d1867, d635, d18, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d635, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8488 pattern childGuard
    simpa only [d1867, d635, d18, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8490 (pattern : Twelve) (guard : d1867 pattern = 1) : d650 pattern ≤ (0 : Int) + d28 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d650, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8479 pattern childGuard
    simpa only [d650, d28, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d650, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8489 pattern childGuard
    simpa only [d650, d28, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8491 (pattern : Twelve) (guard : d0 pattern = 1) : d157 pattern ≤ (0 : Int) + d11 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c8492 (pattern : Twelve) (guard : d1867 pattern = 1) : d636 pattern ≤ (0 : Int) + d19 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d636, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7751 pattern childGuard
    simpa only [d1867, d636, d19, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d636, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8491 pattern childGuard
    simpa only [d1867, d636, d19, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8493 (pattern : Twelve) (guard : d1867 pattern = 1) : d651 pattern ≤ (0 : Int) + d29 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d651, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8492 pattern childGuard
    simpa only [d651, d29, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d651, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d651, d29, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8494 (pattern : Twelve) (guard : d1867 pattern = 1) : d683 pattern ≤ (0 : Int) + d51 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d683, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8490 pattern childGuard
    simpa only [d683, d51, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d683, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8493 pattern childGuard
    simpa only [d683, d51, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8495 (pattern : Twelve) (guard : d1867 pattern = 1) : d710 pattern ≤ (0 : Int) + d73 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d710, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8487 pattern childGuard
    simpa only [d710, d73, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d710, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8494 pattern childGuard
    simpa only [d710, d73, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8496 (pattern : Twelve) (guard : d1867 pattern = 1) : d736 pattern ≤ (0 : Int) + d91 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d736, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8483 pattern childGuard
    simpa only [d736, d91, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d736, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8495 pattern childGuard
    simpa only [d736, d91, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8497 (pattern : Twelve) (guard : d0 pattern = 1) : d10 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c8498 (pattern : Twelve) (guard : d1867 pattern = 1) : d10 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7758 pattern childGuard
    simpa only [d1867, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8497 pattern childGuard
    simpa only [d1867, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8499 (pattern : Twelve) (guard : d0 pattern = 1) : d160 pattern ≤ (0 : Int) + d2 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c8500 (pattern : Twelve) (guard : d1867 pattern = 1) : d637 pattern ≤ (0 : Int) + d2 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7760 pattern childGuard
    simpa only [d1867, d637, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8499 pattern childGuard
    simpa only [d1867, d637, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8501 (pattern : Twelve) (guard : d1867 pattern = 1) : d652 pattern ≤ (0 : Int) + d30 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d652, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8498 pattern childGuard
    simpa only [d652, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d652, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8500 pattern childGuard
    simpa only [d652, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8502 (pattern : Twelve) (guard : d1867 pattern = 1) : d638 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7758 pattern childGuard
    simpa only [d1867, d638, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6994 pattern childGuard
    simpa only [d1867, d638, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8503 (pattern : Twelve) (guard : d1867 pattern = 1) : d639 pattern ≤ (0 : Int) + d20 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d639, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7765 pattern childGuard
    simpa only [d1867, d639, d20, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d639, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3290 pattern childGuard
    simpa only [d1867, d639, d20, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8504 (pattern : Twelve) (guard : d1867 pattern = 1) : d653 pattern ≤ (0 : Int) + d31 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d653, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8502 pattern childGuard
    simpa only [d653, d31, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d653, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8503 pattern childGuard
    simpa only [d653, d31, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8505 (pattern : Twelve) (guard : d1867 pattern = 1) : d684 pattern ≤ (0 : Int) + d52 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d684, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8501 pattern childGuard
    simpa only [d684, d52, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d684, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8504 pattern childGuard
    simpa only [d684, d52, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8506 (pattern : Twelve) (guard : d1867 pattern = 1) : d160 pattern ≤ (0 : Int) + d2 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7761 pattern childGuard
    simpa only [d1867, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8499 pattern childGuard
    simpa only [d1867, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8507 (pattern : Twelve) (guard : d1867 pattern = 1) : d654 pattern ≤ (0 : Int) + d30 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d654, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8502 pattern childGuard
    simpa only [d654, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d654, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8506 pattern childGuard
    simpa only [d654, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8508 (pattern : Twelve) (guard : d1867 pattern = 1) : d158 pattern ≤ (0 : Int) + d17 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7732 pattern childGuard
    simpa only [d1867, d17, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6988 pattern childGuard
    simpa only [d1867, d17, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8509 (pattern : Twelve) (guard : d1867 pattern = 1) : d655 pattern ≤ (0 : Int) + d32 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d655, d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8508 pattern childGuard
    simpa only [d655, d32, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d655, d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3298 pattern childGuard
    simpa only [d655, d32, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8510 (pattern : Twelve) (guard : d1867 pattern = 1) : d685 pattern ≤ (0 : Int) + d53 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d685, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8507 pattern childGuard
    simpa only [d685, d53, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d685, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8509 pattern childGuard
    simpa only [d685, d53, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8511 (pattern : Twelve) (guard : d1867 pattern = 1) : d711 pattern ≤ (0 : Int) + d74 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d711, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8505 pattern childGuard
    simpa only [d711, d74, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d711, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8510 pattern childGuard
    simpa only [d711, d74, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8512 (pattern : Twelve) (guard : d1867 pattern = 1) : d656 pattern ≤ (0 : Int) + d33 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d656, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8485 pattern childGuard
    simpa only [d656, d33, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d656, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3302 pattern childGuard
    simpa only [d656, d33, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8513 (pattern : Twelve) (guard : d1867 pattern = 1) : d686 pattern ≤ (0 : Int) + d54 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d686, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8507 pattern childGuard
    simpa only [d686, d54, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d686, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8512 pattern childGuard
    simpa only [d686, d54, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8514 (pattern : Twelve) (guard : d1867 pattern = 1) : d160 pattern ≤ (0 : Int) + d23 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7761 pattern childGuard
    simpa only [d1867, d23, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8488 pattern childGuard
    simpa only [d1867, d23, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8515 (pattern : Twelve) (guard : d1867 pattern = 1) : d657 pattern ≤ (0 : Int) + d34 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d657, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8508 pattern childGuard
    simpa only [d657, d34, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d657, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8514 pattern childGuard
    simpa only [d657, d34, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8516 (pattern : Twelve) (guard : d1867 pattern = 1) : d687 pattern ≤ (0 : Int) + d55 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d687, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8515 pattern childGuard
    simpa only [d687, d55, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d687, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8493 pattern childGuard
    simpa only [d687, d55, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8517 (pattern : Twelve) (guard : d1867 pattern = 1) : d712 pattern ≤ (0 : Int) + d75 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d712, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8513 pattern childGuard
    simpa only [d712, d75, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d712, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8516 pattern childGuard
    simpa only [d712, d75, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8518 (pattern : Twelve) (guard : d1867 pattern = 1) : d737 pattern ≤ (0 : Int) + d92 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d737, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8511 pattern childGuard
    simpa only [d737, d92, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d737, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8517 pattern childGuard
    simpa only [d737, d92, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8519 (pattern : Twelve) (guard : d1867 pattern = 1) : d754 pattern ≤ (0 : Int) + d102 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d754, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8496 pattern childGuard
    simpa only [d754, d102, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d754, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8518 pattern childGuard
    simpa only [d754, d102, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8520 (pattern : Twelve) (guard : d1867 pattern = 1) : d640 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7782 pattern childGuard
    simpa only [d1867, d640, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6994 pattern childGuard
    simpa only [d1867, d640, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8521 (pattern : Twelve) (guard : d1867 pattern = 1) : d658 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8498 pattern childGuard
    simpa only [d658, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8520 pattern childGuard
    simpa only [d658, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8522 (pattern : Twelve) (guard : d1867 pattern = 1) : d659 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8502 pattern childGuard
    simpa only [d659, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8485 pattern childGuard
    simpa only [d659, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8523 (pattern : Twelve) (guard : d1867 pattern = 1) : d688 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8521 pattern childGuard
    simpa only [d688, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8522 pattern childGuard
    simpa only [d688, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8524 (pattern : Twelve) (guard : d1867 pattern = 1) : d660 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d660, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8502 pattern childGuard
    simpa only [d660, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d660, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8480 pattern childGuard
    simpa only [d660, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8525 (pattern : Twelve) (guard : d1867 pattern = 1) : d661 pattern ≤ (0 : Int) + d27 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d661, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8508 pattern childGuard
    simpa only [d661, d27, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d661, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8480 pattern childGuard
    simpa only [d661, d27, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8526 (pattern : Twelve) (guard : d1867 pattern = 1) : d689 pattern ≤ (0 : Int) + d50 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d689, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8524 pattern childGuard
    simpa only [d689, d50, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d689, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8525 pattern childGuard
    simpa only [d689, d50, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8527 (pattern : Twelve) (guard : d1867 pattern = 1) : d713 pattern ≤ (0 : Int) + d72 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d713, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8523 pattern childGuard
    simpa only [d713, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d713, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8526 pattern childGuard
    simpa only [d713, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8528 (pattern : Twelve) (guard : d1867 pattern = 1) : d690 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8522 pattern childGuard
    simpa only [d690, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8485 pattern childGuard
    simpa only [d690, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8529 (pattern : Twelve) (guard : d1867 pattern = 1) : d714 pattern ≤ (0 : Int) + d76 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d714, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8528 pattern childGuard
    simpa only [d714, d76, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d714, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8516 pattern childGuard
    simpa only [d714, d76, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8530 (pattern : Twelve) (guard : d1867 pattern = 1) : d738 pattern ≤ (0 : Int) + d93 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d738, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8527 pattern childGuard
    simpa only [d738, d93, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d738, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8529 pattern childGuard
    simpa only [d738, d93, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8531 (pattern : Twelve) (guard : d1867 pattern = 1) : d641 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7795 pattern childGuard
    simpa only [d1867, d641, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6994 pattern childGuard
    simpa only [d1867, d641, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8532 (pattern : Twelve) (guard : d1867 pattern = 1) : d662 pattern ≤ (0 : Int) + d30 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d662, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8531 pattern childGuard
    simpa only [d662, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d662, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8506 pattern childGuard
    simpa only [d662, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8533 (pattern : Twelve) (guard : d1867 pattern = 1) : d663 pattern ≤ (0 : Int) + d35 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d663, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8485 pattern childGuard
    simpa only [d663, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d663, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d663, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8534 (pattern : Twelve) (guard : d1867 pattern = 1) : d691 pattern ≤ (0 : Int) + d56 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d691, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8532 pattern childGuard
    simpa only [d691, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d691, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8533 pattern childGuard
    simpa only [d691, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8535 (pattern : Twelve) (guard : d1867 pattern = 1) : d657 pattern ≤ (0 : Int) + d30 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d657, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8485 pattern childGuard
    simpa only [d657, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d657, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8506 pattern childGuard
    simpa only [d657, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8536 (pattern : Twelve) (guard : d1867 pattern = 1) : d663 pattern ≤ (0 : Int) + d36 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d663, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8508 pattern childGuard
    simpa only [d663, d36, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d663, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d663, d36, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8537 (pattern : Twelve) (guard : d1867 pattern = 1) : d692 pattern ≤ (0 : Int) + d57 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d692, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8535 pattern childGuard
    simpa only [d692, d57, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d692, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8536 pattern childGuard
    simpa only [d692, d57, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8538 (pattern : Twelve) (guard : d1867 pattern = 1) : d715 pattern ≤ (0 : Int) + d77 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d715, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8534 pattern childGuard
    simpa only [d715, d77, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d715, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8537 pattern childGuard
    simpa only [d715, d77, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8539 (pattern : Twelve) (guard : d1867 pattern = 1) : d692 pattern ≤ (0 : Int) + d56 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d692, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8535 pattern childGuard
    simpa only [d692, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d692, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8533 pattern childGuard
    simpa only [d692, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
