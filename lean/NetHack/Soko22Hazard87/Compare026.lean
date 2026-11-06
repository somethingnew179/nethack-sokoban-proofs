import NetHack.Soko22Hazard87.Compare025
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare6500 (p : Pattern) (guard : d1585 p = 1) : d47685 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1584 p = 1 := by simpa only [d1585, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6499 p hg
    simpa only [d1585, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1585, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4424 p hg
    simpa only [d1585, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6501 (p : Pattern) (guard : d1586 p = 1) : d47685 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1573 p = 1 := by simpa only [d1586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6488 p hg
    simpa only [d1586, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1585 p = 1 := by simpa only [d1586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6500 p hg
    simpa only [d1586, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6502 (p : Pattern) (guard : d1587 p = 1) : d47685 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1574 p = 1 := by simpa only [d1587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6489 p hg
    simpa only [d1587, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1586 p = 1 := by simpa only [d1587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6501 p hg
    simpa only [d1587, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6503 (p : Pattern) (guard : d1588 p = 1) : d47685 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1585 p = 1 := by simpa only [d1588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6500 p hg
    simpa only [d1588, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4426 p hg
    simpa only [d1588, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6504 (p : Pattern) (guard : d1589 p = 1) : d47685 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1586 p = 1 := by simpa only [d1589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6501 p hg
    simpa only [d1589, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1588 p = 1 := by simpa only [d1589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6503 p hg
    simpa only [d1589, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6505 (p : Pattern) (guard : d1590 p = 1) : d47685 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 157 with
  | false =>
    have hg : d1587 p = 1 := by simpa only [d1590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6502 p hg
    simpa only [d1590, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1589 p = 1 := by simpa only [d1590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6504 p hg
    simpa only [d1590, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6506 (p : Pattern) (guard : d1591 p = 1) : d47686 p ≤ (-1 : Int) + d47695 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1591, d47686, d47695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4403 p hg
    simpa only [d1591, d47686, d47695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1590 p = 1 := by simpa only [d1591, d47686, d47695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6505 p hg
    simpa only [d1591, d47686, d47695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6507 (p : Pattern) (guard : d1592 p = 1) : d47687 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1592, d47687, d47696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4402 p hg
    simpa only [d1592, d47687, d47696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1591 p = 1 := by simpa only [d1592, d47687, d47696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6506 p hg
    simpa only [d1592, d47687, d47696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6508 (p : Pattern) (guard : d1593 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1576 p = 1 := by simpa only [d1593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6491 p hg
    simpa only [d1593, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4408 p hg
    simpa only [d1593, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6509 (p : Pattern) (guard : d1594 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1593 p = 1 := by simpa only [d1594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6508 p hg
    simpa only [d1594, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4408 p hg
    simpa only [d1594, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6510 (p : Pattern) (guard : d1595 p = 1) : d47619 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1594 p = 1 := by simpa only [d1595, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6509 p hg
    simpa only [d1595, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1595, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4416 p hg
    simpa only [d1595, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6511 (p : Pattern) (guard : d1596 p = 1) : d47619 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1595 p = 1 := by simpa only [d1596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6510 p hg
    simpa only [d1596, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4418 p hg
    simpa only [d1596, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6512 (p : Pattern) (guard : d1597 p = 1) : d47660 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1596 p = 1 := by simpa only [d1597, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6511 p hg
    simpa only [d1597, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1597, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4420 p hg
    simpa only [d1597, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6513 (p : Pattern) (guard : d1598 p = 1) : d47663 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1597 p = 1 := by simpa only [d1598, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6512 p hg
    simpa only [d1598, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1598, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3399 p hg
    simpa only [d1598, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6514 (p : Pattern) (guard : d1599 p = 1) : d47664 p ≤ (-1 : Int) + d47692 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1599, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4404 p hg
    simpa only [d1599, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1598 p = 1 := by simpa only [d1599, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6513 p hg
    simpa only [d1599, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6515 (p : Pattern) (guard : d1600 p = 1) : d47685 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1599 p = 1 := by simpa only [d1600, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6514 p hg
    simpa only [d1600, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1600, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4424 p hg
    simpa only [d1600, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6516 (p : Pattern) (guard : d1601 p = 1) : d47685 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1600 p = 1 := by simpa only [d1601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6515 p hg
    simpa only [d1601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4426 p hg
    simpa only [d1601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6517 (p : Pattern) (guard : d1602 p = 1) : d47685 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1588 p = 1 := by simpa only [d1602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6503 p hg
    simpa only [d1602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1601 p = 1 := by simpa only [d1602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6516 p hg
    simpa only [d1602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6518 (p : Pattern) (guard : d1603 p = 1) : d47685 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 157 with
  | false =>
    have hg : d1589 p = 1 := by simpa only [d1603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6504 p hg
    simpa only [d1603, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1602 p = 1 := by simpa only [d1603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6517 p hg
    simpa only [d1603, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6519 (p : Pattern) (guard : d1604 p = 1) : d47686 p ≤ (-1 : Int) + d47695 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1604, d47686, d47695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4403 p hg
    simpa only [d1604, d47686, d47695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1603 p = 1 := by simpa only [d1604, d47686, d47695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6518 p hg
    simpa only [d1604, d47686, d47695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6520 (p : Pattern) (guard : d1605 p = 1) : d47687 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1605, d47687, d47696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4402 p hg
    simpa only [d1605, d47687, d47696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1604 p = 1 := by simpa only [d1605, d47687, d47696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6519 p hg
    simpa only [d1605, d47687, d47696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6521 (p : Pattern) (guard : d1606 p = 1) : d47687 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 136 with
  | false =>
    have hg : d1592 p = 1 := by simpa only [d1606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6507 p hg
    simpa only [d1606, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1605 p = 1 := by simpa only [d1606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6520 p hg
    simpa only [d1606, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6522 (p : Pattern) (guard : d1607 p = 1) : d47687 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 136 with
  | false =>
    have hg : d1605 p = 1 := by simpa only [d1607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6520 p hg
    simpa only [d1607, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4432 p hg
    simpa only [d1607, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6523 (p : Pattern) (guard : d1608 p = 1) : d47687 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 135 with
  | false =>
    have hg : d1606 p = 1 := by simpa only [d1608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6521 p hg
    simpa only [d1608, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1607 p = 1 := by simpa only [d1608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6522 p hg
    simpa only [d1608, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6524 (p : Pattern) (guard : d1609 p = 1) : d47687 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 119 with
  | false =>
    have hg : d1608 p = 1 := by simpa only [d1609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6523 p hg
    simpa only [d1609, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4432 p hg
    simpa only [d1609, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6525 (p : Pattern) (guard : d1610 p = 1) : d47699 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 116 with
  | false =>
    have hg : d1609 p = 1 := by simpa only [d1610, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6524 p hg
    simpa only [d1610, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1610, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4436 p hg
    simpa only [d1610, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6526 (p : Pattern) (guard : d1611 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1611, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4401 p hg
    simpa only [d1611, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1610 p = 1 := by simpa only [d1611, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6525 p hg
    simpa only [d1611, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6527 (p : Pattern) (guard : d1612 p = 1) : d47687 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 135 with
  | false =>
    have hg : d1607 p = 1 := by simpa only [d1612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6522 p hg
    simpa only [d1612, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4432 p hg
    simpa only [d1612, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6528 (p : Pattern) (guard : d1613 p = 1) : d47687 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 119 with
  | false =>
    have hg : d1612 p = 1 := by simpa only [d1613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6527 p hg
    simpa only [d1613, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4432 p hg
    simpa only [d1613, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6529 (p : Pattern) (guard : d1614 p = 1) : d47699 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 116 with
  | false =>
    have hg : d1613 p = 1 := by simpa only [d1614, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6528 p hg
    simpa only [d1614, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1614, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4436 p hg
    simpa only [d1614, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6530 (p : Pattern) (guard : d1615 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1615, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4401 p hg
    simpa only [d1615, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1614 p = 1 := by simpa only [d1615, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6529 p hg
    simpa only [d1615, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6531 (p : Pattern) (guard : d1616 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1611 p = 1 := by simpa only [d1616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6526 p hg
    simpa only [d1616, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1615 p = 1 := by simpa only [d1616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6530 p hg
    simpa only [d1616, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6532 (p : Pattern) (guard : d1617 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 96 with
  | false =>
    have hg : d1616 p = 1 := by simpa only [d1617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6531 p hg
    simpa only [d1617, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d1617, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6533 (p : Pattern) (guard : d1618 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 95 with
  | false =>
    have hg : d1617 p = 1 := by simpa only [d1618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6532 p hg
    simpa only [d1618, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d1618, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6534 (p : Pattern) (guard : d1619 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d1619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1618 p = 1 := by simpa only [d1619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6533 p hg
    simpa only [d1619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6535 (p : Pattern) (guard : d1620 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1615 p = 1 := by simpa only [d1620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6530 p hg
    simpa only [d1620, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d1620, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6536 (p : Pattern) (guard : d1621 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 96 with
  | false =>
    have hg : d1620 p = 1 := by simpa only [d1621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6535 p hg
    simpa only [d1621, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d1621, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6537 (p : Pattern) (guard : d1622 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 95 with
  | false =>
    have hg : d1621 p = 1 := by simpa only [d1622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6536 p hg
    simpa only [d1622, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d1622, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6538 (p : Pattern) (guard : d1623 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d1623, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1622 p = 1 := by simpa only [d1623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6537 p hg
    simpa only [d1623, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6539 (p : Pattern) (guard : d1624 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 91 with
  | false =>
    have hg : d1619 p = 1 := by simpa only [d1624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6534 p hg
    simpa only [d1624, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1623 p = 1 := by simpa only [d1624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6538 p hg
    simpa only [d1624, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6540 (p : Pattern) (guard : d1625 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d1625, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1624 p = 1 := by simpa only [d1625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6539 p hg
    simpa only [d1625, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6541 (p : Pattern) (guard : d1626 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 89 with
  | false =>
    have hg : d1625 p = 1 := by simpa only [d1626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6540 p hg
    simpa only [d1626, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d1626, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6542 (p : Pattern) (guard : d1627 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d1627, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1626 p = 1 := by simpa only [d1627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6541 p hg
    simpa only [d1627, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6543 (p : Pattern) (guard : d1628 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d1628, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1627 p = 1 := by simpa only [d1628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6542 p hg
    simpa only [d1628, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6544 (p : Pattern) (guard : d1629 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d1629, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1628 p = 1 := by simpa only [d1629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6543 p hg
    simpa only [d1629, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6545 (p : Pattern) (guard : d1630 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d1630, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1629 p = 1 := by simpa only [d1630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6544 p hg
    simpa only [d1630, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6546 (p : Pattern) (guard : d1631 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 69 with
  | false =>
    have hg : d1630 p = 1 := by simpa only [d1631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6545 p hg
    simpa only [d1631, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d1631, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6547 (p : Pattern) (guard : d1632 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d1618 p = 1 := by simpa only [d1632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6533 p hg
    simpa only [d1632, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d1632, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6548 (p : Pattern) (guard : d1633 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d1622 p = 1 := by simpa only [d1633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6537 p hg
    simpa only [d1633, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d1633, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6549 (p : Pattern) (guard : d1634 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 91 with
  | false =>
    have hg : d1632 p = 1 := by simpa only [d1634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6547 p hg
    simpa only [d1634, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1633 p = 1 := by simpa only [d1634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6548 p hg
    simpa only [d1634, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6550 (p : Pattern) (guard : d1635 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d1635, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1634 p = 1 := by simpa only [d1635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6549 p hg
    simpa only [d1635, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6551 (p : Pattern) (guard : d1636 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 89 with
  | false =>
    have hg : d1635 p = 1 := by simpa only [d1636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6550 p hg
    simpa only [d1636, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d1636, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6552 (p : Pattern) (guard : d1637 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d1637, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1636 p = 1 := by simpa only [d1637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6551 p hg
    simpa only [d1637, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6553 (p : Pattern) (guard : d1638 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d1638, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1637 p = 1 := by simpa only [d1638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6552 p hg
    simpa only [d1638, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6554 (p : Pattern) (guard : d1639 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 71 with
  | false =>
    have hg : d1628 p = 1 := by simpa only [d1639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6543 p hg
    simpa only [d1639, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1638 p = 1 := by simpa only [d1639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6553 p hg
    simpa only [d1639, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6555 (p : Pattern) (guard : d1640 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 70 with
  | false =>
    have hg : d1629 p = 1 := by simpa only [d1640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6544 p hg
    simpa only [d1640, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1639 p = 1 := by simpa only [d1640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6554 p hg
    simpa only [d1640, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6556 (p : Pattern) (guard : d1641 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 69 with
  | false =>
    have hg : d1640 p = 1 := by simpa only [d1641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6555 p hg
    simpa only [d1641, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d1641, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6557 (p : Pattern) (guard : d1642 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 51 with
  | false =>
    have hg : d1631 p = 1 := by simpa only [d1642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6546 p hg
    simpa only [d1642, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1641 p = 1 := by simpa only [d1642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6556 p hg
    simpa only [d1642, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6558 (p : Pattern) (guard : d1643 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d1643, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1617 p = 1 := by simpa only [d1643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6532 p hg
    simpa only [d1643, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6559 (p : Pattern) (guard : d1644 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d1644, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1643 p = 1 := by simpa only [d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6558 p hg
    simpa only [d1644, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6560 (p : Pattern) (guard : d1645 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d1645, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1621 p = 1 := by simpa only [d1645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6536 p hg
    simpa only [d1645, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6561 (p : Pattern) (guard : d1646 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d1646, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1645 p = 1 := by simpa only [d1646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6560 p hg
    simpa only [d1646, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6562 (p : Pattern) (guard : d1647 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 91 with
  | false =>
    have hg : d1644 p = 1 := by simpa only [d1647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6559 p hg
    simpa only [d1647, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1646 p = 1 := by simpa only [d1647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6561 p hg
    simpa only [d1647, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6563 (p : Pattern) (guard : d1648 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d1648, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1647 p = 1 := by simpa only [d1648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6562 p hg
    simpa only [d1648, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6564 (p : Pattern) (guard : d1649 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 89 with
  | false =>
    have hg : d1648 p = 1 := by simpa only [d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6563 p hg
    simpa only [d1649, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d1649, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6565 (p : Pattern) (guard : d1650 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d1650, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1649 p = 1 := by simpa only [d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6564 p hg
    simpa only [d1650, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6566 (p : Pattern) (guard : d1651 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d1651, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1616 p = 1 := by simpa only [d1651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6531 p hg
    simpa only [d1651, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6567 (p : Pattern) (guard : d1652 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 95 with
  | false =>
    have hg : d1651 p = 1 := by simpa only [d1652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6566 p hg
    simpa only [d1652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d1652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6568 (p : Pattern) (guard : d1653 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d1653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1652 p = 1 := by simpa only [d1653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6567 p hg
    simpa only [d1653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6569 (p : Pattern) (guard : d1654 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d1654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1620 p = 1 := by simpa only [d1654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6535 p hg
    simpa only [d1654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6570 (p : Pattern) (guard : d1655 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 95 with
  | false =>
    have hg : d1654 p = 1 := by simpa only [d1655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6569 p hg
    simpa only [d1655, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d1655, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6571 (p : Pattern) (guard : d1656 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d1656, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1655 p = 1 := by simpa only [d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6570 p hg
    simpa only [d1656, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6572 (p : Pattern) (guard : d1657 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 91 with
  | false =>
    have hg : d1653 p = 1 := by simpa only [d1657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6568 p hg
    simpa only [d1657, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1656 p = 1 := by simpa only [d1657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6571 p hg
    simpa only [d1657, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6573 (p : Pattern) (guard : d1658 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d1658, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1657 p = 1 := by simpa only [d1658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6572 p hg
    simpa only [d1658, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6574 (p : Pattern) (guard : d1659 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 89 with
  | false =>
    have hg : d1658 p = 1 := by simpa only [d1659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6573 p hg
    simpa only [d1659, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d1659, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6575 (p : Pattern) (guard : d1660 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4408 p hg
    simpa only [d1660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1201 p = 1 := by simpa only [d1660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5916 p hg
    simpa only [d1660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6576 (p : Pattern) (guard : d1661 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4408 p hg
    simpa only [d1661, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1205 p = 1 := by simpa only [d1661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5920 p hg
    simpa only [d1661, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6577 (p : Pattern) (guard : d1662 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1660 p = 1 := by simpa only [d1662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6575 p hg
    simpa only [d1662, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1661 p = 1 := by simpa only [d1662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6576 p hg
    simpa only [d1662, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6578 (p : Pattern) (guard : d1663 p = 1) : d47619 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1662 p = 1 := by simpa only [d1663, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6577 p hg
    simpa only [d1663, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1663, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4416 p hg
    simpa only [d1663, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6579 (p : Pattern) (guard : d1664 p = 1) : d47619 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1663 p = 1 := by simpa only [d1664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6578 p hg
    simpa only [d1664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1538 p = 1 := by simpa only [d1664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6453 p hg
    simpa only [d1664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6580 (p : Pattern) (guard : d1665 p = 1) : d47660 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1664 p = 1 := by simpa only [d1665, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6579 p hg
    simpa only [d1665, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1665, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4420 p hg
    simpa only [d1665, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6581 (p : Pattern) (guard : d1666 p = 1) : d47663 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1665 p = 1 := by simpa only [d1666, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6580 p hg
    simpa only [d1666, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1666, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3399 p hg
    simpa only [d1666, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6582 (p : Pattern) (guard : d1667 p = 1) : d47664 p ≤ (-1 : Int) + d47692 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1667, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4404 p hg
    simpa only [d1667, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1666 p = 1 := by simpa only [d1667, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6581 p hg
    simpa only [d1667, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6583 (p : Pattern) (guard : d1668 p = 1) : d47685 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1667 p = 1 := by simpa only [d1668, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6582 p hg
    simpa only [d1668, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1668, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4424 p hg
    simpa only [d1668, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6584 (p : Pattern) (guard : d1669 p = 1) : d47685 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1668 p = 1 := by simpa only [d1669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6583 p hg
    simpa only [d1669, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1558 p = 1 := by simpa only [d1669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6473 p hg
    simpa only [d1669, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6585 (p : Pattern) (guard : d1670 p = 1) : d47685 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1669 p = 1 := by simpa only [d1670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6584 p hg
    simpa only [d1670, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1574 p = 1 := by simpa only [d1670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6489 p hg
    simpa only [d1670, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6586 (p : Pattern) (guard : d1671 p = 1) : d47685 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 157 with
  | false =>
    have hg : d1670 p = 1 := by simpa only [d1671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6585 p hg
    simpa only [d1671, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1587 p = 1 := by simpa only [d1671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6502 p hg
    simpa only [d1671, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6587 (p : Pattern) (guard : d1672 p = 1) : d47686 p ≤ (-1 : Int) + d47695 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1672, d47686, d47695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4403 p hg
    simpa only [d1672, d47686, d47695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1671 p = 1 := by simpa only [d1672, d47686, d47695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6586 p hg
    simpa only [d1672, d47686, d47695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6588 (p : Pattern) (guard : d1673 p = 1) : d47687 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1673, d47687, d47696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4402 p hg
    simpa only [d1673, d47687, d47696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1672 p = 1 := by simpa only [d1673, d47687, d47696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6587 p hg
    simpa only [d1673, d47687, d47696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6589 (p : Pattern) (guard : d1674 p = 1) : d47687 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 136 with
  | false =>
    have hg : d1673 p = 1 := by simpa only [d1674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6588 p hg
    simpa only [d1674, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1592 p = 1 := by simpa only [d1674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6507 p hg
    simpa only [d1674, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6590 (p : Pattern) (guard : d1675 p = 1) : d47687 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 135 with
  | false =>
    have hg : d1674 p = 1 := by simpa only [d1675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6589 p hg
    simpa only [d1675, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1606 p = 1 := by simpa only [d1675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6521 p hg
    simpa only [d1675, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6591 (p : Pattern) (guard : d1676 p = 1) : d47687 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 119 with
  | false =>
    have hg : d1675 p = 1 := by simpa only [d1676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6590 p hg
    simpa only [d1676, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4432 p hg
    simpa only [d1676, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6592 (p : Pattern) (guard : d1677 p = 1) : d47699 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 116 with
  | false =>
    have hg : d1676 p = 1 := by simpa only [d1677, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6591 p hg
    simpa only [d1677, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1677, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4436 p hg
    simpa only [d1677, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6593 (p : Pattern) (guard : d1678 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1678, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4401 p hg
    simpa only [d1678, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1677 p = 1 := by simpa only [d1678, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6592 p hg
    simpa only [d1678, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6594 (p : Pattern) (guard : d7034 p = 1) : d47687 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 136 with
  | false =>
    have hg : d1592 p = 1 := by simpa only [d7034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6507 p hg
    simpa only [d7034, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d7034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4432 p hg
    simpa only [d7034, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6595 (p : Pattern) (guard : d5120 p = 1) : d47685 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1586 p = 1 := by simpa only [d5120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6501 p hg
    simpa only [d5120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4426 p hg
    simpa only [d5120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6596 (p : Pattern) (guard : d5121 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d825 p = 1 := by simpa only [d5121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5459 p hg
    simpa only [d5121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4408 p hg
    simpa only [d5121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6597 (p : Pattern) (guard : d5122 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5121 p = 1 := by simpa only [d5122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6596 p hg
    simpa only [d5122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1547 p = 1 := by simpa only [d5122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6462 p hg
    simpa only [d5122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6598 (p : Pattern) (guard : d5123 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d5122 p = 1 := by simpa only [d5123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6597 p hg
    simpa only [d5123, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1563 p = 1 := by simpa only [d5123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6478 p hg
    simpa only [d5123, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6599 (p : Pattern) (guard : d5124 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5123 p = 1 := by simpa only [d5124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6598 p hg
    simpa only [d5124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4408 p hg
    simpa only [d5124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6600 (p : Pattern) (guard : d5125 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1545 p = 1 := by simpa only [d5125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6460 p hg
    simpa only [d5125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5124 p = 1 := by simpa only [d5125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6599 p hg
    simpa only [d5125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6601 (p : Pattern) (guard : d5126 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d5125 p = 1 := by simpa only [d5126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6600 p hg
    simpa only [d5126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1566 p = 1 := by simpa only [d5126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6481 p hg
    simpa only [d5126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6602 (p : Pattern) (guard : d5127 p = 1) : d47619 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5126 p = 1 := by simpa only [d5127, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6601 p hg
    simpa only [d5127, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5127, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4416 p hg
    simpa only [d5127, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6603 (p : Pattern) (guard : d5128 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4408 p hg
    simpa only [d5128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1563 p = 1 := by simpa only [d5128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6478 p hg
    simpa only [d5128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6604 (p : Pattern) (guard : d5129 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5128 p = 1 := by simpa only [d5129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6603 p hg
    simpa only [d5129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4408 p hg
    simpa only [d5129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6605 (p : Pattern) (guard : d5130 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d5129 p = 1 := by simpa only [d5130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6604 p hg
    simpa only [d5130, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1565 p = 1 := by simpa only [d5130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6480 p hg
    simpa only [d5130, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6606 (p : Pattern) (guard : d5131 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d5130 p = 1 := by simpa only [d5131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6605 p hg
    simpa only [d5131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1578 p = 1 := by simpa only [d5131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6493 p hg
    simpa only [d5131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6607 (p : Pattern) (guard : d5132 p = 1) : d47619 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5131 p = 1 := by simpa only [d5132, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6606 p hg
    simpa only [d5132, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5132, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4416 p hg
    simpa only [d5132, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6608 (p : Pattern) (guard : d5133 p = 1) : d47619 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d5127 p = 1 := by simpa only [d5133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6602 p hg
    simpa only [d5133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5132 p = 1 := by simpa only [d5133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6607 p hg
    simpa only [d5133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6609 (p : Pattern) (guard : d5134 p = 1) : d47660 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5133 p = 1 := by simpa only [d5134, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6608 p hg
    simpa only [d5134, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5134, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4420 p hg
    simpa only [d5134, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6610 (p : Pattern) (guard : d5135 p = 1) : d47663 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5134 p = 1 := by simpa only [d5135, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6609 p hg
    simpa only [d5135, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5135, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3399 p hg
    simpa only [d5135, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6611 (p : Pattern) (guard : d5136 p = 1) : d47664 p ≤ (-1 : Int) + d47692 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5136, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4404 p hg
    simpa only [d5136, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5135 p = 1 := by simpa only [d5136, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6610 p hg
    simpa only [d5136, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6612 (p : Pattern) (guard : d5137 p = 1) : d47685 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5136 p = 1 := by simpa only [d5137, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6611 p hg
    simpa only [d5137, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5137, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4424 p hg
    simpa only [d5137, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6613 (p : Pattern) (guard : d5138 p = 1) : d47685 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 159 with
  | false =>
    have hg : d5137 p = 1 := by simpa only [d5138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6612 p hg
    simpa only [d5138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4426 p hg
    simpa only [d5138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6614 (p : Pattern) (guard : d5139 p = 1) : d47685 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 158 with
  | false =>
    have hg : d5138 p = 1 := by simpa only [d5139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6613 p hg
    simpa only [d5139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4426 p hg
    simpa only [d5139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6615 (p : Pattern) (guard : d5140 p = 1) : d47685 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 157 with
  | false =>
    have hg : d5120 p = 1 := by simpa only [d5140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6595 p hg
    simpa only [d5140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5139 p = 1 := by simpa only [d5140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6614 p hg
    simpa only [d5140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6616 (p : Pattern) (guard : d5141 p = 1) : d47686 p ≤ (-1 : Int) + d47695 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5141, d47686, d47695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4403 p hg
    simpa only [d5141, d47686, d47695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5140 p = 1 := by simpa only [d5141, d47686, d47695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6615 p hg
    simpa only [d5141, d47686, d47695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6617 (p : Pattern) (guard : d5142 p = 1) : d47687 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5142, d47687, d47696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4402 p hg
    simpa only [d5142, d47687, d47696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5141 p = 1 := by simpa only [d5142, d47687, d47696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6616 p hg
    simpa only [d5142, d47687, d47696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6618 (p : Pattern) (guard : d5143 p = 1) : d47687 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 136 with
  | false =>
    have hg : d5142 p = 1 := by simpa only [d5143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6617 p hg
    simpa only [d5143, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4432 p hg
    simpa only [d5143, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6619 (p : Pattern) (guard : d7035 p = 1) : d47687 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 135 with
  | false =>
    have hg : d7034 p = 1 := by simpa only [d7035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6594 p hg
    simpa only [d7035, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5143 p = 1 := by simpa only [d7035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6618 p hg
    simpa only [d7035, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6620 (p : Pattern) (guard : d7036 p = 1) : d47687 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 119 with
  | false =>
    have hg : d7035 p = 1 := by simpa only [d7036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6619 p hg
    simpa only [d7036, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d7036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4432 p hg
    simpa only [d7036, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6621 (p : Pattern) (guard : d7037 p = 1) : d47699 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 116 with
  | false =>
    have hg : d7036 p = 1 := by simpa only [d7037, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6620 p hg
    simpa only [d7037, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d7037, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4436 p hg
    simpa only [d7037, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6622 (p : Pattern) (guard : d7038 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d7038, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4401 p hg
    simpa only [d7038, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d7037 p = 1 := by simpa only [d7038, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6621 p hg
    simpa only [d7038, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6623 (p : Pattern) (guard : d7039 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1678 p = 1 := by simpa only [d7039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6593 p hg
    simpa only [d7039, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d7038 p = 1 := by simpa only [d7039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6622 p hg
    simpa only [d7039, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6624 (p : Pattern) (guard : d7040 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 96 with
  | false =>
    have hg : d7039 p = 1 := by simpa only [d7040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6623 p hg
    simpa only [d7040, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d7040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d7040, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6625 (p : Pattern) (guard : d7041 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 95 with
  | false =>
    have hg : d7040 p = 1 := by simpa only [d7041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6624 p hg
    simpa only [d7041, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d7041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d7041, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6626 (p : Pattern) (guard : d7042 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d7042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d7042, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d7041 p = 1 := by simpa only [d7042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6625 p hg
    simpa only [d7042, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6627 (p : Pattern) (guard : d5144 p = 1) : d47687 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 135 with
  | false =>
    have hg : d1606 p = 1 := by simpa only [d5144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6521 p hg
    simpa only [d5144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5143 p = 1 := by simpa only [d5144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6618 p hg
    simpa only [d5144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6628 (p : Pattern) (guard : d5145 p = 1) : d47687 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 119 with
  | false =>
    have hg : d5144 p = 1 := by simpa only [d5145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6627 p hg
    simpa only [d5145, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4432 p hg
    simpa only [d5145, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6629 (p : Pattern) (guard : d5146 p = 1) : d47699 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5145 p = 1 := by simpa only [d5146, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6628 p hg
    simpa only [d5146, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5146, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4436 p hg
    simpa only [d5146, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6630 (p : Pattern) (guard : d5147 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5147, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4401 p hg
    simpa only [d5147, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5146 p = 1 := by simpa only [d5147, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6629 p hg
    simpa only [d5147, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6631 (p : Pattern) (guard : d7043 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 113 with
  | false =>
    have hg : d5147 p = 1 := by simpa only [d7043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6630 p hg
    simpa only [d7043, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1615 p = 1 := by simpa only [d7043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6530 p hg
    simpa only [d7043, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6632 (p : Pattern) (guard : d7044 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 96 with
  | false =>
    have hg : d7043 p = 1 := by simpa only [d7044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6631 p hg
    simpa only [d7044, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d7044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d7044, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6633 (p : Pattern) (guard : d7045 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 95 with
  | false =>
    have hg : d7044 p = 1 := by simpa only [d7045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6632 p hg
    simpa only [d7045, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d7045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d7045, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6634 (p : Pattern) (guard : d7046 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d7046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d7046, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d7045 p = 1 := by simpa only [d7046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6633 p hg
    simpa only [d7046, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6635 (p : Pattern) (guard : d7047 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 91 with
  | false =>
    have hg : d7042 p = 1 := by simpa only [d7047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6626 p hg
    simpa only [d7047, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d7046 p = 1 := by simpa only [d7047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6634 p hg
    simpa only [d7047, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6636 (p : Pattern) (guard : d82190 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 90 with
  | false =>
    have hg : d7047 p = 1 := by simpa only [d82190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6635 p hg
    simpa only [d82190, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d82190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d82190, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6637 (p : Pattern) (guard : d6400 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1611 p = 1 := by simpa only [d6400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6526 p hg
    simpa only [d6400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d6400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6638 (p : Pattern) (guard : d6401 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 96 with
  | false =>
    have hg : d6400 p = 1 := by simpa only [d6401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6637 p hg
    simpa only [d6401, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d6401, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6639 (p : Pattern) (guard : d6402 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 95 with
  | false =>
    have hg : d6401 p = 1 := by simpa only [d6402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6638 p hg
    simpa only [d6402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d6402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6640 (p : Pattern) (guard : d6403 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d6403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d6403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6402 p = 1 := by simpa only [d6403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6639 p hg
    simpa only [d6403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6641 (p : Pattern) (guard : d6445 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 91 with
  | false =>
    have hg : d6403 p = 1 := by simpa only [d6445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6640 p hg
    simpa only [d6445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d6445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6642 (p : Pattern) (guard : d6446 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 90 with
  | false =>
    have hg : d6445 p = 1 := by simpa only [d6446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6641 p hg
    simpa only [d6446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d6446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6643 (p : Pattern) (guard : d82191 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 89 with
  | false =>
    have hg : d82190 p = 1 := by simpa only [d82191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6636 p hg
    simpa only [d82191, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6446 p = 1 := by simpa only [d82191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6642 p hg
    simpa only [d82191, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6644 (p : Pattern) (guard : d82192 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 74 with
  | false =>
    have hg : d1659 p = 1 := by simpa only [d82192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6574 p hg
    simpa only [d82192, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82191 p = 1 := by simpa only [d82192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6643 p hg
    simpa only [d82192, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6645 (p : Pattern) (guard : d82193 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 73 with
  | false =>
    have hg : d1650 p = 1 := by simpa only [d82193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6565 p hg
    simpa only [d82193, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82192 p = 1 := by simpa only [d82193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6644 p hg
    simpa only [d82193, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6646 (p : Pattern) (guard : d82194 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d82194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d82194, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82193 p = 1 := by simpa only [d82194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6645 p hg
    simpa only [d82194, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6647 (p : Pattern) (guard : d1803 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d1643 p = 1 := by simpa only [d1803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6558 p hg
    simpa only [d1803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d1803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6648 (p : Pattern) (guard : d1804 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d1645 p = 1 := by simpa only [d1804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6560 p hg
    simpa only [d1804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d1804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6649 (p : Pattern) (guard : d1805 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 91 with
  | false =>
    have hg : d1803 p = 1 := by simpa only [d1805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6647 p hg
    simpa only [d1805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1804 p = 1 := by simpa only [d1805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6648 p hg
    simpa only [d1805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6650 (p : Pattern) (guard : d1806 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d1806, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1805 p = 1 := by simpa only [d1806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6649 p hg
    simpa only [d1806, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6651 (p : Pattern) (guard : d1807 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 89 with
  | false =>
    have hg : d1806 p = 1 := by simpa only [d1807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6650 p hg
    simpa only [d1807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d1807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6652 (p : Pattern) (guard : d1808 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d1808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1807 p = 1 := by simpa only [d1808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6651 p hg
    simpa only [d1808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6653 (p : Pattern) (guard : d1809 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d1652 p = 1 := by simpa only [d1809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6567 p hg
    simpa only [d1809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d1809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6654 (p : Pattern) (guard : d1810 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d1655 p = 1 := by simpa only [d1810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6570 p hg
    simpa only [d1810, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d1810, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6655 (p : Pattern) (guard : d1811 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 91 with
  | false =>
    have hg : d1809 p = 1 := by simpa only [d1811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6653 p hg
    simpa only [d1811, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1810 p = 1 := by simpa only [d1811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6654 p hg
    simpa only [d1811, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6656 (p : Pattern) (guard : d1812 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d1812, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1811 p = 1 := by simpa only [d1812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6655 p hg
    simpa only [d1812, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6657 (p : Pattern) (guard : d1813 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 89 with
  | false =>
    have hg : d1812 p = 1 := by simpa only [d1813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6656 p hg
    simpa only [d1813, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d1813, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6658 (p : Pattern) (guard : d7053 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d7041 p = 1 := by simpa only [d7053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6625 p hg
    simpa only [d7053, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d7053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d7053, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6659 (p : Pattern) (guard : d7054 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d7045 p = 1 := by simpa only [d7054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6633 p hg
    simpa only [d7054, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d7054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d7054, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6660 (p : Pattern) (guard : d7055 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 91 with
  | false =>
    have hg : d7053 p = 1 := by simpa only [d7055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6658 p hg
    simpa only [d7055, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d7054 p = 1 := by simpa only [d7055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6659 p hg
    simpa only [d7055, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6661 (p : Pattern) (guard : d82195 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 90 with
  | false =>
    have hg : d7055 p = 1 := by simpa only [d82195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6660 p hg
    simpa only [d82195, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d82195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d82195, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6662 (p : Pattern) (guard : d6412 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d6402 p = 1 := by simpa only [d6412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6639 p hg
    simpa only [d6412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d6412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6663 (p : Pattern) (guard : d6466 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 91 with
  | false =>
    have hg : d6412 p = 1 := by simpa only [d6466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6662 p hg
    simpa only [d6466, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d6466, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6664 (p : Pattern) (guard : d6467 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 90 with
  | false =>
    have hg : d6466 p = 1 := by simpa only [d6467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6663 p hg
    simpa only [d6467, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d6467, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6665 (p : Pattern) (guard : d82196 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 89 with
  | false =>
    have hg : d82195 p = 1 := by simpa only [d82196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6661 p hg
    simpa only [d82196, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6467 p = 1 := by simpa only [d82196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6664 p hg
    simpa only [d82196, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6666 (p : Pattern) (guard : d82197 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 74 with
  | false =>
    have hg : d1813 p = 1 := by simpa only [d82197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6657 p hg
    simpa only [d82197, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82196 p = 1 := by simpa only [d82197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6665 p hg
    simpa only [d82197, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6667 (p : Pattern) (guard : d82198 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 73 with
  | false =>
    have hg : d1808 p = 1 := by simpa only [d82198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6652 p hg
    simpa only [d82198, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82197 p = 1 := by simpa only [d82198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6666 p hg
    simpa only [d82198, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6668 (p : Pattern) (guard : d82199 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 71 with
  | false =>
    have hg : d82193 p = 1 := by simpa only [d82199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6645 p hg
    simpa only [d82199, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82198 p = 1 := by simpa only [d82199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6667 p hg
    simpa only [d82199, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6669 (p : Pattern) (guard : d82200 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 70 with
  | false =>
    have hg : d82194 p = 1 := by simpa only [d82200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6646 p hg
    simpa only [d82200, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82199 p = 1 := by simpa only [d82200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6668 p hg
    simpa only [d82200, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6670 (p : Pattern) (guard : d7062 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 91 with
  | false =>
    have hg : d7046 p = 1 := by simpa only [d7062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6634 p hg
    simpa only [d7062, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1623 p = 1 := by simpa only [d7062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6538 p hg
    simpa only [d7062, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6671 (p : Pattern) (guard : d7063 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d7063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d7063, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d7062 p = 1 := by simpa only [d7063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6670 p hg
    simpa only [d7063, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6672 (p : Pattern) (guard : d7064 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 89 with
  | false =>
    have hg : d7063 p = 1 := by simpa only [d7064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6671 p hg
    simpa only [d7064, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d7064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d7064, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6673 (p : Pattern) (guard : d7065 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d7065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d7065, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d7064 p = 1 := by simpa only [d7065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6672 p hg
    simpa only [d7065, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6674 (p : Pattern) (guard : d7066 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d7066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d7066, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d7065 p = 1 := by simpa only [d7066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6673 p hg
    simpa only [d7066, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6675 (p : Pattern) (guard : d1827 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 91 with
  | false =>
    have hg : d1623 p = 1 := by simpa only [d1827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6538 p hg
    simpa only [d1827, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d1827, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6676 (p : Pattern) (guard : d1828 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d1828, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1827 p = 1 := by simpa only [d1828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6675 p hg
    simpa only [d1828, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6677 (p : Pattern) (guard : d1829 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 89 with
  | false =>
    have hg : d1828 p = 1 := by simpa only [d1829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6676 p hg
    simpa only [d1829, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d1829, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6678 (p : Pattern) (guard : d1830 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d1830, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1829 p = 1 := by simpa only [d1830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6677 p hg
    simpa only [d1830, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6679 (p : Pattern) (guard : d1831 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d1831, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1830 p = 1 := by simpa only [d1831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6678 p hg
    simpa only [d1831, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6680 (p : Pattern) (guard : d7067 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 71 with
  | false =>
    have hg : d7066 p = 1 := by simpa only [d7067, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6674 p hg
    simpa only [d7067, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1831 p = 1 := by simpa only [d7067, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6679 p hg
    simpa only [d7067, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6681 (p : Pattern) (guard : d1833 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 91 with
  | false =>
    have hg : d1633 p = 1 := by simpa only [d1833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6548 p hg
    simpa only [d1833, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d1833, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6682 (p : Pattern) (guard : d1834 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d1834, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1833 p = 1 := by simpa only [d1834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6681 p hg
    simpa only [d1834, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6683 (p : Pattern) (guard : d1835 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 89 with
  | false =>
    have hg : d1834 p = 1 := by simpa only [d1835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6682 p hg
    simpa only [d1835, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d1835, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6684 (p : Pattern) (guard : d1836 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d1836, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1835 p = 1 := by simpa only [d1836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6683 p hg
    simpa only [d1836, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6685 (p : Pattern) (guard : d1837 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d1837, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1836 p = 1 := by simpa only [d1837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6684 p hg
    simpa only [d1837, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6686 (p : Pattern) (guard : d1838 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 71 with
  | false =>
    have hg : d1831 p = 1 := by simpa only [d1838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6679 p hg
    simpa only [d1838, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1837 p = 1 := by simpa only [d1838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6685 p hg
    simpa only [d1838, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6687 (p : Pattern) (guard : d7068 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 70 with
  | false =>
    have hg : d7067 p = 1 := by simpa only [d7068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6680 p hg
    simpa only [d7068, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1838 p = 1 := by simpa only [d7068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6686 p hg
    simpa only [d7068, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6688 (p : Pattern) (guard : d82201 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 69 with
  | false =>
    have hg : d82200 p = 1 := by simpa only [d82201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6669 p hg
    simpa only [d82201, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d7068 p = 1 := by simpa only [d82201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6687 p hg
    simpa only [d82201, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6689 (p : Pattern) (guard : d82202 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 51 with
  | false =>
    have hg : d82201 p = 1 := by simpa only [d82202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6688 p hg
    simpa only [d82202, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d82202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d82202, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6690 (p : Pattern) (guard : d82203 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 50 with
  | false =>
    have hg : d1642 p = 1 := by simpa only [d82203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6557 p hg
    simpa only [d82203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82202 p = 1 := by simpa only [d82203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6689 p hg
    simpa only [d82203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6691 (p : Pattern) (guard : d1660 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4469 p hg
    simpa only [d1660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1201 p = 1 := by simpa only [d1660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6033 p hg
    simpa only [d1660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6692 (p : Pattern) (guard : d1661 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4469 p hg
    simpa only [d1661, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1205 p = 1 := by simpa only [d1661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6037 p hg
    simpa only [d1661, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6693 (p : Pattern) (guard : d1662 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1660 p = 1 := by simpa only [d1662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6691 p hg
    simpa only [d1662, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1661 p = 1 := by simpa only [d1662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6692 p hg
    simpa only [d1662, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6694 (p : Pattern) (guard : d1663 p = 1) : d47708 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1662 p = 1 := by simpa only [d1663, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6693 p hg
    simpa only [d1663, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1663, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4477 p hg
    simpa only [d1663, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6695 (p : Pattern) (guard : d308 p = 1) : d5 p ≤ (-1 : Int) + d12 p := by
  have ha := bounds5 p
  have hb := bounds12 p
  omega
theorem compare6696 (p : Pattern) (guard : d1519 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d308 p = 1 := by simpa only [d1519, d47706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6695 p hg
    simpa only [d1519, d47706, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1519, d47706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4467 p hg
    simpa only [d1519, d47706, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6697 (p : Pattern) (guard : d1520 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 226 with
  | false =>
    have hg : d309 p = 1 := by simpa only [d1520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4887 p hg
    simpa only [d1520, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1519 p = 1 := by simpa only [d1520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6696 p hg
    simpa only [d1520, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6698 (p : Pattern) (guard : d1521 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d528 p = 1 := by simpa only [d1521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5184 p hg
    simpa only [d1521, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1520 p = 1 := by simpa only [d1521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6697 p hg
    simpa only [d1521, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6699 (p : Pattern) (guard : d1522 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d820 p = 1 := by simpa only [d1522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5560 p hg
    simpa only [d1522, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1521 p = 1 := by simpa only [d1522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6698 p hg
    simpa only [d1522, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6700 (p : Pattern) (guard : d1523 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1523, d47706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6041 p hg
    simpa only [d1523, d47706, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d308 p = 1 := by simpa only [d1523, d47706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4886 p hg
    simpa only [d1523, d47706, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6701 (p : Pattern) (guard : d1524 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1523 p = 1 := by simpa only [d1524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6700 p hg
    simpa only [d1524, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1084 p = 1 := by simpa only [d1524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6042 p hg
    simpa only [d1524, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6702 (p : Pattern) (guard : d1525 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1524 p = 1 := by simpa only [d1525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6701 p hg
    simpa only [d1525, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4469 p hg
    simpa only [d1525, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6703 (p : Pattern) (guard : d1526 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4469 p hg
    simpa only [d1526, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1525 p = 1 := by simpa only [d1526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6702 p hg
    simpa only [d1526, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6704 (p : Pattern) (guard : d1527 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d1522 p = 1 := by simpa only [d1527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6699 p hg
    simpa only [d1527, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1526 p = 1 := by simpa only [d1527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6703 p hg
    simpa only [d1527, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6705 (p : Pattern) (guard : d1528 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4469 p hg
    simpa only [d1528, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1087 p = 1 := by simpa only [d1528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6045 p hg
    simpa only [d1528, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6706 (p : Pattern) (guard : d1529 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1527 p = 1 := by simpa only [d1529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6704 p hg
    simpa only [d1529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1528 p = 1 := by simpa only [d1529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6705 p hg
    simpa only [d1529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6707 (p : Pattern) (guard : d1530 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1201 p = 1 := by simpa only [d1530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6033 p hg
    simpa only [d1530, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1529 p = 1 := by simpa only [d1530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6706 p hg
    simpa only [d1530, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6708 (p : Pattern) (guard : d1531 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1519 p = 1 := by simpa only [d1531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6696 p hg
    simpa only [d1531, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4469 p hg
    simpa only [d1531, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6709 (p : Pattern) (guard : d1532 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1520 p = 1 := by simpa only [d1532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6697 p hg
    simpa only [d1532, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1531 p = 1 := by simpa only [d1532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6708 p hg
    simpa only [d1532, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6710 (p : Pattern) (guard : d1533 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d826 p = 1 := by simpa only [d1533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5566 p hg
    simpa only [d1533, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1532 p = 1 := by simpa only [d1533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6709 p hg
    simpa only [d1533, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6711 (p : Pattern) (guard : d1534 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d1533 p = 1 := by simpa only [d1534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6710 p hg
    simpa only [d1534, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4469 p hg
    simpa only [d1534, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6712 (p : Pattern) (guard : d1535 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1534 p = 1 := by simpa only [d1535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6711 p hg
    simpa only [d1535, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4469 p hg
    simpa only [d1535, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6713 (p : Pattern) (guard : d1536 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1205 p = 1 := by simpa only [d1536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6037 p hg
    simpa only [d1536, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1535 p = 1 := by simpa only [d1536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6712 p hg
    simpa only [d1536, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6714 (p : Pattern) (guard : d1537 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1530 p = 1 := by simpa only [d1537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6707 p hg
    simpa only [d1537, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1536 p = 1 := by simpa only [d1537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6713 p hg
    simpa only [d1537, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6715 (p : Pattern) (guard : d1538 p = 1) : d47708 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1537 p = 1 := by simpa only [d1538, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6714 p hg
    simpa only [d1538, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1538, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4477 p hg
    simpa only [d1538, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6716 (p : Pattern) (guard : d1664 p = 1) : d47708 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1663 p = 1 := by simpa only [d1664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6694 p hg
    simpa only [d1664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1538 p = 1 := by simpa only [d1664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6715 p hg
    simpa only [d1664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6717 (p : Pattern) (guard : d1665 p = 1) : d47735 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1664 p = 1 := by simpa only [d1665, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6716 p hg
    simpa only [d1665, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1665, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4481 p hg
    simpa only [d1665, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6718 (p : Pattern) (guard : d1666 p = 1) : d47736 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1665 p = 1 := by simpa only [d1666, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6717 p hg
    simpa only [d1666, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1666, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d1666, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6719 (p : Pattern) (guard : d1667 p = 1) : d47737 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1667, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4465 p hg
    simpa only [d1667, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1666 p = 1 := by simpa only [d1667, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6718 p hg
    simpa only [d1667, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6720 (p : Pattern) (guard : d1668 p = 1) : d47755 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1667 p = 1 := by simpa only [d1668, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6719 p hg
    simpa only [d1668, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1668, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4485 p hg
    simpa only [d1668, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6721 (p : Pattern) (guard : d1539 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1521 p = 1 := by simpa only [d1539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6698 p hg
    simpa only [d1539, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1532 p = 1 := by simpa only [d1539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6709 p hg
    simpa only [d1539, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6722 (p : Pattern) (guard : d1540 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1519 p = 1 := by simpa only [d1540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6696 p hg
    simpa only [d1540, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15 p = 1 := by simpa only [d1540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4468 p hg
    simpa only [d1540, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6723 (p : Pattern) (guard : d1541 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1540 p = 1 := by simpa only [d1541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6722 p hg
    simpa only [d1541, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4469 p hg
    simpa only [d1541, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6724 (p : Pattern) (guard : d1542 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1525 p = 1 := by simpa only [d1542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6702 p hg
    simpa only [d1542, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1541 p = 1 := by simpa only [d1542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6723 p hg
    simpa only [d1542, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6725 (p : Pattern) (guard : d1543 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d1539 p = 1 := by simpa only [d1543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6721 p hg
    simpa only [d1543, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1542 p = 1 := by simpa only [d1543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6724 p hg
    simpa only [d1543, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6726 (p : Pattern) (guard : d1544 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4469 p hg
    simpa only [d1544, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1093 p = 1 := by simpa only [d1544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6056 p hg
    simpa only [d1544, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6727 (p : Pattern) (guard : d1545 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1543 p = 1 := by simpa only [d1545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6725 p hg
    simpa only [d1545, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1544 p = 1 := by simpa only [d1545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6726 p hg
    simpa only [d1545, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6728 (p : Pattern) (guard : d1546 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1529 p = 1 := by simpa only [d1546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6706 p hg
    simpa only [d1546, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1545 p = 1 := by simpa only [d1546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6727 p hg
    simpa only [d1546, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6729 (p : Pattern) (guard : d1547 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1531 p = 1 := by simpa only [d1547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6708 p hg
    simpa only [d1547, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4469 p hg
    simpa only [d1547, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6730 (p : Pattern) (guard : d1548 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1532 p = 1 := by simpa only [d1548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6709 p hg
    simpa only [d1548, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1547 p = 1 := by simpa only [d1548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6729 p hg
    simpa only [d1548, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6731 (p : Pattern) (guard : d1549 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d1548 p = 1 := by simpa only [d1549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6730 p hg
    simpa only [d1549, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4469 p hg
    simpa only [d1549, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6732 (p : Pattern) (guard : d1550 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1549 p = 1 := by simpa only [d1550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6731 p hg
    simpa only [d1550, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4469 p hg
    simpa only [d1550, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6733 (p : Pattern) (guard : d1551 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1535 p = 1 := by simpa only [d1551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6712 p hg
    simpa only [d1551, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1550 p = 1 := by simpa only [d1551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6732 p hg
    simpa only [d1551, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6734 (p : Pattern) (guard : d1552 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1546 p = 1 := by simpa only [d1552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6728 p hg
    simpa only [d1552, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1551 p = 1 := by simpa only [d1552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6733 p hg
    simpa only [d1552, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6735 (p : Pattern) (guard : d1553 p = 1) : d47708 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1552 p = 1 := by simpa only [d1553, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6734 p hg
    simpa only [d1553, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1553, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4477 p hg
    simpa only [d1553, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6736 (p : Pattern) (guard : d1554 p = 1) : d47708 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1538 p = 1 := by simpa only [d1554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6715 p hg
    simpa only [d1554, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d1554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6735 p hg
    simpa only [d1554, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6737 (p : Pattern) (guard : d1555 p = 1) : d47735 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1554 p = 1 := by simpa only [d1555, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6736 p hg
    simpa only [d1555, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1555, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4481 p hg
    simpa only [d1555, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6738 (p : Pattern) (guard : d1556 p = 1) : d47736 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1555 p = 1 := by simpa only [d1556, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6737 p hg
    simpa only [d1556, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1556, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d1556, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6739 (p : Pattern) (guard : d1557 p = 1) : d47737 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1557, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4465 p hg
    simpa only [d1557, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1556 p = 1 := by simpa only [d1557, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6738 p hg
    simpa only [d1557, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6740 (p : Pattern) (guard : d1558 p = 1) : d47755 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1557 p = 1 := by simpa only [d1558, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6739 p hg
    simpa only [d1558, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1558, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4485 p hg
    simpa only [d1558, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6741 (p : Pattern) (guard : d1669 p = 1) : d47755 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1668 p = 1 := by simpa only [d1669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6720 p hg
    simpa only [d1669, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1558 p = 1 := by simpa only [d1669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6740 p hg
    simpa only [d1669, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6742 (p : Pattern) (guard : d1559 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1541 p = 1 := by simpa only [d1559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6723 p hg
    simpa only [d1559, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4469 p hg
    simpa only [d1559, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6743 (p : Pattern) (guard : d1560 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d1548 p = 1 := by simpa only [d1560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6730 p hg
    simpa only [d1560, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1559 p = 1 := by simpa only [d1560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6742 p hg
    simpa only [d1560, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6744 (p : Pattern) (guard : d1561 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1560 p = 1 := by simpa only [d1561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6743 p hg
    simpa only [d1561, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1115 p = 1 := by simpa only [d1561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6080 p hg
    simpa only [d1561, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6745 (p : Pattern) (guard : d1562 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1545 p = 1 := by simpa only [d1562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6727 p hg
    simpa only [d1562, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1561 p = 1 := by simpa only [d1562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6744 p hg
    simpa only [d1562, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6746 (p : Pattern) (guard : d1563 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1547 p = 1 := by simpa only [d1563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6729 p hg
    simpa only [d1563, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4469 p hg
    simpa only [d1563, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6747 (p : Pattern) (guard : d1564 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d1563 p = 1 := by simpa only [d1564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6746 p hg
    simpa only [d1564, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4469 p hg
    simpa only [d1564, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6748 (p : Pattern) (guard : d1565 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1564 p = 1 := by simpa only [d1565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6747 p hg
    simpa only [d1565, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4469 p hg
    simpa only [d1565, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6749 (p : Pattern) (guard : d1566 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1550 p = 1 := by simpa only [d1566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6732 p hg
    simpa only [d1566, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1565 p = 1 := by simpa only [d1566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6748 p hg
    simpa only [d1566, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
