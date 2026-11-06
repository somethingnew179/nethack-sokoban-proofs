/- Staged soko4-1 certificate. No result until all kernel checks pass. -/
import NetHack.Sokoban41.Comparisons09
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban41.Diagram
theorem c1600 (pattern : Ten) (guard : d1 pattern = 1) : d198 pattern ≤ (19 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1599 pattern childGuard
    simpa only [d198, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1564 pattern childGuard
    simpa only [d198, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1601 (pattern : Ten) (guard : d1 pattern = 1) : d203 pattern ≤ (19 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1600 pattern childGuard
    simpa only [d203, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1564 pattern childGuard
    simpa only [d203, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1602 (pattern : Ten) (guard : d1 pattern = 1) : d207 pattern ≤ (19 : Int) + d10 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1596 pattern childGuard
    simpa only [d207, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1601 pattern childGuard
    simpa only [d207, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1603 (pattern : Ten) (guard : d1 pattern = 1) : d310 pattern ≤ (19 : Int) + d10 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1589 pattern childGuard
    simpa only [d310, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1592 pattern childGuard
    simpa only [d310, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1604 (pattern : Ten) (guard : d1 pattern = 1) : d314 pattern ≤ (19 : Int) + d10 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1590 pattern childGuard
    simpa only [d314, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1603 pattern childGuard
    simpa only [d314, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1605 (pattern : Ten) (guard : d1 pattern = 1) : d311 pattern ≤ (19 : Int) + d10 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1593 pattern childGuard
    simpa only [d311, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1597 pattern childGuard
    simpa only [d311, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1606 (pattern : Ten) (guard : d1 pattern = 1) : d315 pattern ≤ (19 : Int) + d10 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1594 pattern childGuard
    simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1605 pattern childGuard
    simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1607 (pattern : Ten) (guard : d1 pattern = 1) : d320 pattern ≤ (19 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1604 pattern childGuard
    simpa only [d320, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1606 pattern childGuard
    simpa only [d320, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1608 (pattern : Ten) (guard : d1 pattern = 1) : d8 pattern ≤ (19 : Int) + d10 pattern := by
  change (8 : Int) ≤ (19 : Int) + 10
  decide
theorem c1609 (pattern : Ten) (guard : d1 pattern = 1) : d312 pattern ≤ (19 : Int) + d10 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1598 pattern childGuard
    simpa only [d312, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1608 pattern childGuard
    simpa only [d312, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1610 (pattern : Ten) (guard : d1 pattern = 1) : d316 pattern ≤ (19 : Int) + d10 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1599 pattern childGuard
    simpa only [d316, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1609 pattern childGuard
    simpa only [d316, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1611 (pattern : Ten) (guard : d1 pattern = 1) : d319 pattern ≤ (19 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1610 pattern childGuard
    simpa only [d319, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1564 pattern childGuard
    simpa only [d319, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1612 (pattern : Ten) (guard : d1 pattern = 1) : d323 pattern ≤ (19 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1607 pattern childGuard
    simpa only [d323, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1611 pattern childGuard
    simpa only [d323, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1613 (pattern : Ten) (guard : d1 pattern = 1) : d195 pattern ≤ (19 : Int) + d10 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1608 pattern childGuard
    simpa only [d195, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1563 pattern childGuard
    simpa only [d195, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1614 (pattern : Ten) (guard : d1 pattern = 1) : d11 pattern ≤ (19 : Int) + d10 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1563 pattern childGuard
    simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1564 pattern childGuard
    simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1615 (pattern : Ten) (guard : d1 pattern = 1) : d196 pattern ≤ (19 : Int) + d10 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1613 pattern childGuard
    simpa only [d196, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1614 pattern childGuard
    simpa only [d196, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1616 (pattern : Ten) (guard : d1 pattern = 1) : d201 pattern ≤ (19 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1615 pattern childGuard
    simpa only [d201, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1564 pattern childGuard
    simpa only [d201, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1617 (pattern : Ten) (guard : d1 pattern = 1) : d206 pattern ≤ (19 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1616 pattern childGuard
    simpa only [d206, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1564 pattern childGuard
    simpa only [d206, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1618 (pattern : Ten) (guard : d1 pattern = 1) : d325 pattern ≤ (19 : Int) + d10 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1612 pattern childGuard
    simpa only [d325, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1617 pattern childGuard
    simpa only [d325, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1619 (pattern : Ten) (guard : d1 pattern = 1) : d344 pattern ≤ (19 : Int) + d10 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1602 pattern childGuard
    simpa only [d344, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1618 pattern childGuard
    simpa only [d344, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1620 (pattern : Ten) (guard : d1 pattern = 1) : d341 pattern ≤ (19 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1606 pattern childGuard
    simpa only [d341, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1610 pattern childGuard
    simpa only [d341, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1621 (pattern : Ten) (guard : d1 pattern = 1) : d342 pattern ≤ (19 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1620 pattern childGuard
    simpa only [d342, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1616 pattern childGuard
    simpa only [d342, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1622 (pattern : Ten) (guard : d1 pattern = 1) : d343 pattern ≤ (19 : Int) + d10 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1621 pattern childGuard
    simpa only [d343, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1564 pattern childGuard
    simpa only [d343, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1623 (pattern : Ten) (guard : d1 pattern = 1) : d345 pattern ≤ (19 : Int) + d10 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1602 pattern childGuard
    simpa only [d345, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1622 pattern childGuard
    simpa only [d345, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1624 (pattern : Ten) (guard : d1 pattern = 1) : d346 pattern ≤ (19 : Int) + d10 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1619 pattern childGuard
    simpa only [d346, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1623 pattern childGuard
    simpa only [d346, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1625 (pattern : Ten) (guard : d1 pattern = 1) : d309 pattern ≤ (19 : Int) + d10 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1586 pattern childGuard
    simpa only [d309, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1588 pattern childGuard
    simpa only [d309, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1626 (pattern : Ten) (guard : d1 pattern = 1) : d313 pattern ≤ (19 : Int) + d10 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1587 pattern childGuard
    simpa only [d313, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1625 pattern childGuard
    simpa only [d313, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1627 (pattern : Ten) (guard : d1 pattern = 1) : d317 pattern ≤ (19 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1626 pattern childGuard
    simpa only [d317, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1604 pattern childGuard
    simpa only [d317, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1628 (pattern : Ten) (guard : d1 pattern = 1) : d318 pattern ≤ (19 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1606 pattern childGuard
    simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1564 pattern childGuard
    simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1629 (pattern : Ten) (guard : d1 pattern = 1) : d321 pattern ≤ (19 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1627 pattern childGuard
    simpa only [d321, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1628 pattern childGuard
    simpa only [d321, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1630 (pattern : Ten) (guard : d1 pattern = 1) : d322 pattern ≤ (19 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1611 pattern childGuard
    simpa only [d322, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1564 pattern childGuard
    simpa only [d322, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1631 (pattern : Ten) (guard : d1 pattern = 1) : d324 pattern ≤ (19 : Int) + d10 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1629 pattern childGuard
    simpa only [d324, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1630 pattern childGuard
    simpa only [d324, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1632 (pattern : Ten) (guard : d1 pattern = 1) : d333 pattern ≤ (19 : Int) + d10 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1631 pattern childGuard
    simpa only [d333, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1564 pattern childGuard
    simpa only [d333, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1633 (pattern : Ten) (guard : d1 pattern = 1) : d334 pattern ≤ (19 : Int) + d10 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1618 pattern childGuard
    simpa only [d334, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1564 pattern childGuard
    simpa only [d334, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1634 (pattern : Ten) (guard : d1 pattern = 1) : d336 pattern ≤ (19 : Int) + d10 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1632 pattern childGuard
    simpa only [d336, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1633 pattern childGuard
    simpa only [d336, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1635 (pattern : Ten) (guard : d1 pattern = 1) : d347 pattern ≤ (19 : Int) + d10 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1624 pattern childGuard
    simpa only [d347, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1634 pattern childGuard
    simpa only [d347, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1636 (pattern : Ten) (guard : d1 pattern = 1) : d200 pattern ≤ (19 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1613 pattern childGuard
    simpa only [d200, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1564 pattern childGuard
    simpa only [d200, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1637 (pattern : Ten) (guard : d1 pattern = 1) : d205 pattern ≤ (19 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1636 pattern childGuard
    simpa only [d205, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1564 pattern childGuard
    simpa only [d205, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1638 (pattern : Ten) (guard : d1 pattern = 1) : d209 pattern ≤ (19 : Int) + d10 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1637 pattern childGuard
    simpa only [d209, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1564 pattern childGuard
    simpa only [d209, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1639 (pattern : Ten) (guard : d1 pattern = 1) : d214 pattern ≤ (19 : Int) + d10 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1638 pattern childGuard
    simpa only [d214, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1564 pattern childGuard
    simpa only [d214, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1640 (pattern : Ten) (guard : d1 pattern = 1) : d210 pattern ≤ (19 : Int) + d10 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1617 pattern childGuard
    simpa only [d210, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1564 pattern childGuard
    simpa only [d210, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1641 (pattern : Ten) (guard : d1 pattern = 1) : d335 pattern ≤ (19 : Int) + d10 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1640 pattern childGuard
    simpa only [d335, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1564 pattern childGuard
    simpa only [d335, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1642 (pattern : Ten) (guard : d1 pattern = 1) : d337 pattern ≤ (19 : Int) + d10 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1641 pattern childGuard
    simpa only [d337, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1564 pattern childGuard
    simpa only [d337, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1643 (pattern : Ten) (guard : d1 pattern = 1) : d348 pattern ≤ (19 : Int) + d10 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1639 pattern childGuard
    simpa only [d348, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1642 pattern childGuard
    simpa only [d348, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1644 (pattern : Ten) (guard : d1 pattern = 1) : d349 pattern ≤ (19 : Int) + d10 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1635 pattern childGuard
    simpa only [d349, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1643 pattern childGuard
    simpa only [d349, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1645 (pattern : Ten) (guard : d350 pattern = 1) : d192 pattern ≤ (1 : Int) + d192 pattern := by
  omega
theorem c1646 (pattern : Ten) (guard : d350 pattern = 1) : d170 pattern ≤ (3 : Int) + d170 pattern := by
  omega
theorem c1647 (pattern : Ten) (guard : d1 pattern = 1) : d349 pattern ≤ (3 : Int) + d349 pattern := by
  omega
theorem c1648 (pattern : Ten) (guard : d350 pattern = 1) : d170 pattern ≤ (4 : Int) + d170 pattern := by
  omega
theorem c1649 (pattern : Ten) (guard : d1 pattern = 1) : d349 pattern ≤ (4 : Int) + d349 pattern := by
  omega
theorem c1650 (pattern : Ten) (guard : d350 pattern = 1) : d170 pattern ≤ (5 : Int) + d170 pattern := by
  omega
theorem c1651 (pattern : Ten) (guard : d1 pattern = 1) : d349 pattern ≤ (5 : Int) + d349 pattern := by
  omega
theorem c1652 (pattern : Ten) (guard : d350 pattern = 1) : d220 pattern ≤ (1 : Int) + d220 pattern := by
  omega
theorem c1653 (pattern : Ten) (guard : d407 pattern = 1) : d23 pattern ≤ (1 : Int) + d23 pattern := by
  omega
theorem c1654 (pattern : Ten) (guard : d407 pattern = 1) : d0 pattern ≤ (1 : Int) + d0 pattern := by
  omega
theorem c1655 (pattern : Ten) (guard : d0 pattern = 1) : d9 pattern ≤ (1 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1656 (pattern : Ten) (guard : d356 pattern = 1) : d10 pattern ≤ (1 : Int) + d10 pattern := by
  omega
theorem c1657 (pattern : Ten) (guard : d406 pattern = 1) : d11 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d406, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1655 pattern childGuard
    simpa only [d406, d11, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d356 pattern = 1 := by simpa only [d406, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1656 pattern childGuard
    simpa only [d406, d11, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1658 (pattern : Ten) (guard : d0 pattern = 1) : d11 pattern ≤ (1 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1659 (pattern : Ten) (guard : d407 pattern = 1) : d11 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d406 pattern = 1 := by simpa only [d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1657 pattern childGuard
    simpa only [d407, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1658 pattern childGuard
    simpa only [d407, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1660 (pattern : Ten) (guard : d407 pattern = 1) : d13 pattern ≤ (1 : Int) + d12 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d407 pattern = 1 := by simpa only [d13, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1654 pattern childGuard
    simpa only [d13, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d407 pattern = 1 := by simpa only [d13, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1659 pattern childGuard
    simpa only [d13, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1661 (pattern : Ten) (guard : d407 pattern = 1) : d10 pattern ≤ (1 : Int) + d10 pattern := by
  omega
theorem c1662 (pattern : Ten) (guard : d407 pattern = 1) : d14 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d407 pattern = 1 := by simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1659 pattern childGuard
    simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d407 pattern = 1 := by simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1661 pattern childGuard
    simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1663 (pattern : Ten) (guard : d407 pattern = 1) : d19 pattern ≤ (1 : Int) + d18 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d407 pattern = 1 := by simpa only [d19, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1660 pattern childGuard
    simpa only [d19, d18, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d407 pattern = 1 := by simpa only [d19, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1662 pattern childGuard
    simpa only [d19, d18, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1664 (pattern : Ten) (guard : d407 pattern = 1) : d20 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d407 pattern = 1 := by simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1662 pattern childGuard
    simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d407 pattern = 1 := by simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1661 pattern childGuard
    simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1665 (pattern : Ten) (guard : d407 pattern = 1) : d24 pattern ≤ (1 : Int) + d26 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d407 pattern = 1 := by simpa only [d24, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1663 pattern childGuard
    simpa only [d24, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d407 pattern = 1 := by simpa only [d24, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1664 pattern childGuard
    simpa only [d24, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1666 (pattern : Ten) (guard : d407 pattern = 1) : d29 pattern ≤ (1 : Int) + d408 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d407 pattern = 1 := by simpa only [d29, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1653 pattern childGuard
    simpa only [d29, d408, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d407 pattern = 1 := by simpa only [d29, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1665 pattern childGuard
    simpa only [d29, d408, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1667 (pattern : Ten) (guard : d407 pattern = 1) : d25 pattern ≤ (1 : Int) + d25 pattern := by
  omega
theorem c1668 (pattern : Ten) (guard : d407 pattern = 1) : d30 pattern ≤ (1 : Int) + d227 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d407 pattern = 1 := by simpa only [d30, d227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1667 pattern childGuard
    simpa only [d30, d227, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d407 pattern = 1 := by simpa only [d30, d227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1665 pattern childGuard
    simpa only [d30, d227, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1669 (pattern : Ten) (guard : d407 pattern = 1) : d33 pattern ≤ (1 : Int) + d409 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d407 pattern = 1 := by simpa only [d33, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1666 pattern childGuard
    simpa only [d33, d409, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d407 pattern = 1 := by simpa only [d33, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1668 pattern childGuard
    simpa only [d33, d409, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1670 (pattern : Ten) (guard : d407 pattern = 1) : d26 pattern ≤ (1 : Int) + d26 pattern := by
  omega
theorem c1671 (pattern : Ten) (guard : d407 pattern = 1) : d27 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d407 pattern = 1 := by simpa only [d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1664 pattern childGuard
    simpa only [d27, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d407 pattern = 1 := by simpa only [d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1661 pattern childGuard
    simpa only [d27, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1672 (pattern : Ten) (guard : d407 pattern = 1) : d31 pattern ≤ (1 : Int) + d228 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d407 pattern = 1 := by simpa only [d31, d228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1670 pattern childGuard
    simpa only [d31, d228, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d407 pattern = 1 := by simpa only [d31, d228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1671 pattern childGuard
    simpa only [d31, d228, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1673 (pattern : Ten) (guard : d407 pattern = 1) : d28 pattern ≤ (1 : Int) + d28 pattern := by
  omega
theorem c1674 (pattern : Ten) (guard : d407 pattern = 1) : d32 pattern ≤ (1 : Int) + d229 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d407 pattern = 1 := by simpa only [d32, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1673 pattern childGuard
    simpa only [d32, d229, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d407 pattern = 1 := by simpa only [d32, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1671 pattern childGuard
    simpa only [d32, d229, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1675 (pattern : Ten) (guard : d407 pattern = 1) : d34 pattern ≤ (1 : Int) + d231 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d407 pattern = 1 := by simpa only [d34, d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1672 pattern childGuard
    simpa only [d34, d231, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d407 pattern = 1 := by simpa only [d34, d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1674 pattern childGuard
    simpa only [d34, d231, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1676 (pattern : Ten) (guard : d407 pattern = 1) : d35 pattern ≤ (1 : Int) + d410 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d407 pattern = 1 := by simpa only [d35, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1669 pattern childGuard
    simpa only [d35, d410, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d407 pattern = 1 := by simpa only [d35, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1675 pattern childGuard
    simpa only [d35, d410, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1677 (pattern : Ten) (guard : d407 pattern = 1) : d36 pattern ≤ (1 : Int) + d233 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d407 pattern = 1 := by simpa only [d36, d233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1675 pattern childGuard
    simpa only [d36, d233, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d407 pattern = 1 := by simpa only [d36, d233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1661 pattern childGuard
    simpa only [d36, d233, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1678 (pattern : Ten) (guard : d407 pattern = 1) : d37 pattern ≤ (1 : Int) + d411 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d407 pattern = 1 := by simpa only [d37, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1676 pattern childGuard
    simpa only [d37, d411, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d407 pattern = 1 := by simpa only [d37, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1677 pattern childGuard
    simpa only [d37, d411, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1679 (pattern : Ten) (guard : d0 pattern = 1) : d239 pattern ≤ (1 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1680 (pattern : Ten) (guard : d356 pattern = 1) : d1 pattern ≤ (1 : Int) + d10 pattern := by
  change (1 : Int) ≤ (1 : Int) + 10
  decide
theorem c1681 (pattern : Ten) (guard : d406 pattern = 1) : d240 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d406, d240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1679 pattern childGuard
    simpa only [d406, d240, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d356 pattern = 1 := by simpa only [d406, d240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1680 pattern childGuard
    simpa only [d406, d240, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1682 (pattern : Ten) (guard : d0 pattern = 1) : d0 pattern ≤ (1 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1683 (pattern : Ten) (guard : d406 pattern = 1) : d171 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d406, d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1682 pattern childGuard
    simpa only [d406, d171, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d356 pattern = 1 := by simpa only [d406, d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1680 pattern childGuard
    simpa only [d406, d171, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1684 (pattern : Ten) (guard : d406 pattern = 1) : d241 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d406 pattern = 1 := by simpa only [d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1681 pattern childGuard
    simpa only [d241, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d406 pattern = 1 := by simpa only [d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1683 pattern childGuard
    simpa only [d241, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1685 (pattern : Ten) (guard : d406 pattern = 1) : d242 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d406 pattern = 1 := by simpa only [d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1684 pattern childGuard
    simpa only [d242, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d406 pattern = 1 := by simpa only [d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1683 pattern childGuard
    simpa only [d242, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1686 (pattern : Ten) (guard : d406 pattern = 1) : d10 pattern ≤ (1 : Int) + d10 pattern := by
  omega
theorem c1687 (pattern : Ten) (guard : d406 pattern = 1) : d173 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d406 pattern = 1 := by simpa only [d173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1683 pattern childGuard
    simpa only [d173, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d406 pattern = 1 := by simpa only [d173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1686 pattern childGuard
    simpa only [d173, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1688 (pattern : Ten) (guard : d406 pattern = 1) : d243 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d406 pattern = 1 := by simpa only [d243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1685 pattern childGuard
    simpa only [d243, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d406 pattern = 1 := by simpa only [d243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1687 pattern childGuard
    simpa only [d243, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1689 (pattern : Ten) (guard : d406 pattern = 1) : d177 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d406 pattern = 1 := by simpa only [d177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1687 pattern childGuard
    simpa only [d177, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d406 pattern = 1 := by simpa only [d177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1686 pattern childGuard
    simpa only [d177, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1690 (pattern : Ten) (guard : d406 pattern = 1) : d244 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d406 pattern = 1 := by simpa only [d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1688 pattern childGuard
    simpa only [d244, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d406 pattern = 1 := by simpa only [d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1689 pattern childGuard
    simpa only [d244, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1691 (pattern : Ten) (guard : d406 pattern = 1) : d181 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d406 pattern = 1 := by simpa only [d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1689 pattern childGuard
    simpa only [d181, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d406 pattern = 1 := by simpa only [d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1686 pattern childGuard
    simpa only [d181, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1692 (pattern : Ten) (guard : d406 pattern = 1) : d245 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d406 pattern = 1 := by simpa only [d245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1690 pattern childGuard
    simpa only [d245, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d406 pattern = 1 := by simpa only [d245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1691 pattern childGuard
    simpa only [d245, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1693 (pattern : Ten) (guard : d0 pattern = 1) : d2 pattern ≤ (1 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1694 (pattern : Ten) (guard : d356 pattern = 1) : d3 pattern ≤ (1 : Int) + d10 pattern := by
  change (3 : Int) ≤ (1 : Int) + 10
  decide
theorem c1695 (pattern : Ten) (guard : d406 pattern = 1) : d172 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d406, d172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1693 pattern childGuard
    simpa only [d406, d172, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d356 pattern = 1 := by simpa only [d406, d172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1694 pattern childGuard
    simpa only [d406, d172, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1696 (pattern : Ten) (guard : d406 pattern = 1) : d174 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d406 pattern = 1 := by simpa only [d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1683 pattern childGuard
    simpa only [d174, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d406 pattern = 1 := by simpa only [d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1695 pattern childGuard
    simpa only [d174, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1697 (pattern : Ten) (guard : d406 pattern = 1) : d175 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d406 pattern = 1 := by simpa only [d175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1695 pattern childGuard
    simpa only [d175, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d406 pattern = 1 := by simpa only [d175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1686 pattern childGuard
    simpa only [d175, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1698 (pattern : Ten) (guard : d406 pattern = 1) : d178 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d406 pattern = 1 := by simpa only [d178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1696 pattern childGuard
    simpa only [d178, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d406 pattern = 1 := by simpa only [d178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1697 pattern childGuard
    simpa only [d178, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1699 (pattern : Ten) (guard : d406 pattern = 1) : d179 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d406 pattern = 1 := by simpa only [d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1697 pattern childGuard
    simpa only [d179, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d406 pattern = 1 := by simpa only [d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1686 pattern childGuard
    simpa only [d179, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1700 (pattern : Ten) (guard : d406 pattern = 1) : d182 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d406 pattern = 1 := by simpa only [d182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1698 pattern childGuard
    simpa only [d182, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d406 pattern = 1 := by simpa only [d182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1699 pattern childGuard
    simpa only [d182, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1701 (pattern : Ten) (guard : d406 pattern = 1) : d185 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d406 pattern = 1 := by simpa only [d185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1700 pattern childGuard
    simpa only [d185, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d406 pattern = 1 := by simpa only [d185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1691 pattern childGuard
    simpa only [d185, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1702 (pattern : Ten) (guard : d406 pattern = 1) : d246 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d406 pattern = 1 := by simpa only [d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1692 pattern childGuard
    simpa only [d246, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d406 pattern = 1 := by simpa only [d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1701 pattern childGuard
    simpa only [d246, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1703 (pattern : Ten) (guard : d406 pattern = 1) : d186 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d406 pattern = 1 := by simpa only [d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1691 pattern childGuard
    simpa only [d186, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d406 pattern = 1 := by simpa only [d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1686 pattern childGuard
    simpa only [d186, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1704 (pattern : Ten) (guard : d406 pattern = 1) : d183 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d406 pattern = 1 := by simpa only [d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1699 pattern childGuard
    simpa only [d183, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d406 pattern = 1 := by simpa only [d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1686 pattern childGuard
    simpa only [d183, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1705 (pattern : Ten) (guard : d406 pattern = 1) : d187 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d406 pattern = 1 := by simpa only [d187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1704 pattern childGuard
    simpa only [d187, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d406 pattern = 1 := by simpa only [d187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1686 pattern childGuard
    simpa only [d187, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1706 (pattern : Ten) (guard : d406 pattern = 1) : d189 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d406 pattern = 1 := by simpa only [d189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1703 pattern childGuard
    simpa only [d189, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d406 pattern = 1 := by simpa only [d189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1705 pattern childGuard
    simpa only [d189, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1707 (pattern : Ten) (guard : d406 pattern = 1) : d247 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d406 pattern = 1 := by simpa only [d247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1702 pattern childGuard
    simpa only [d247, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d406 pattern = 1 := by simpa only [d247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1706 pattern childGuard
    simpa only [d247, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1708 (pattern : Ten) (guard : d406 pattern = 1) : d191 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d406 pattern = 1 := by simpa only [d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1706 pattern childGuard
    simpa only [d191, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d406 pattern = 1 := by simpa only [d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1686 pattern childGuard
    simpa only [d191, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1709 (pattern : Ten) (guard : d406 pattern = 1) : d248 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d406 pattern = 1 := by simpa only [d248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1707 pattern childGuard
    simpa only [d248, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d406 pattern = 1 := by simpa only [d248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1708 pattern childGuard
    simpa only [d248, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1710 (pattern : Ten) (guard : d292 pattern = 1) : d23 pattern ≤ (1 : Int) + d23 pattern := by
  omega
theorem c1711 (pattern : Ten) (guard : d292 pattern = 1) : d0 pattern ≤ (1 : Int) + d0 pattern := by
  omega
theorem c1712 (pattern : Ten) (guard : d0 pattern = 1) : d9 pattern ≤ (1 : Int) + d9 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1713 (pattern : Ten) (guard : d1 pattern = 1) : d10 pattern ≤ (1 : Int) + d9 pattern := by
  change (10 : Int) ≤ (1 : Int) + 9
  decide
theorem c1714 (pattern : Ten) (guard : d171 pattern = 1) : d11 pattern ≤ (1 : Int) + d9 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d171, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1712 pattern childGuard
    simpa only [d171, d11, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d171, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1713 pattern childGuard
    simpa only [d171, d11, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1715 (pattern : Ten) (guard : d0 pattern = 1) : d11 pattern ≤ (1 : Int) + d9 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1716 (pattern : Ten) (guard : d292 pattern = 1) : d11 pattern ≤ (1 : Int) + d9 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d171 pattern = 1 := by simpa only [d292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1714 pattern childGuard
    simpa only [d292, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1715 pattern childGuard
    simpa only [d292, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1717 (pattern : Ten) (guard : d292 pattern = 1) : d13 pattern ≤ (1 : Int) + d67 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d292 pattern = 1 := by simpa only [d13, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1711 pattern childGuard
    simpa only [d13, d67, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d292 pattern = 1 := by simpa only [d13, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1716 pattern childGuard
    simpa only [d13, d67, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1718 (pattern : Ten) (guard : d292 pattern = 1) : d10 pattern ≤ (1 : Int) + d10 pattern := by
  omega
theorem c1719 (pattern : Ten) (guard : d292 pattern = 1) : d14 pattern ≤ (1 : Int) + d68 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d292 pattern = 1 := by simpa only [d14, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1716 pattern childGuard
    simpa only [d14, d68, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d292 pattern = 1 := by simpa only [d14, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1718 pattern childGuard
    simpa only [d14, d68, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1720 (pattern : Ten) (guard : d292 pattern = 1) : d19 pattern ≤ (1 : Int) + d69 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d292 pattern = 1 := by simpa only [d19, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1717 pattern childGuard
    simpa only [d19, d69, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d292 pattern = 1 := by simpa only [d19, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1719 pattern childGuard
    simpa only [d19, d69, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1721 (pattern : Ten) (guard : d292 pattern = 1) : d20 pattern ≤ (1 : Int) + d70 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d292 pattern = 1 := by simpa only [d20, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1719 pattern childGuard
    simpa only [d20, d70, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d292 pattern = 1 := by simpa only [d20, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1718 pattern childGuard
    simpa only [d20, d70, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1722 (pattern : Ten) (guard : d292 pattern = 1) : d24 pattern ≤ (1 : Int) + d71 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d292 pattern = 1 := by simpa only [d24, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1720 pattern childGuard
    simpa only [d24, d71, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d292 pattern = 1 := by simpa only [d24, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1721 pattern childGuard
    simpa only [d24, d71, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1723 (pattern : Ten) (guard : d292 pattern = 1) : d29 pattern ≤ (1 : Int) + d73 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d292 pattern = 1 := by simpa only [d29, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1710 pattern childGuard
    simpa only [d29, d73, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d292 pattern = 1 := by simpa only [d29, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1722 pattern childGuard
    simpa only [d29, d73, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1724 (pattern : Ten) (guard : d292 pattern = 1) : d25 pattern ≤ (1 : Int) + d25 pattern := by
  omega
theorem c1725 (pattern : Ten) (guard : d292 pattern = 1) : d30 pattern ≤ (1 : Int) + d74 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d292 pattern = 1 := by simpa only [d30, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1724 pattern childGuard
    simpa only [d30, d74, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d292 pattern = 1 := by simpa only [d30, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1722 pattern childGuard
    simpa only [d30, d74, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1726 (pattern : Ten) (guard : d292 pattern = 1) : d33 pattern ≤ (1 : Int) + d77 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d292 pattern = 1 := by simpa only [d33, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1723 pattern childGuard
    simpa only [d33, d77, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d292 pattern = 1 := by simpa only [d33, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1725 pattern childGuard
    simpa only [d33, d77, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1727 (pattern : Ten) (guard : d292 pattern = 1) : d26 pattern ≤ (1 : Int) + d26 pattern := by
  omega
theorem c1728 (pattern : Ten) (guard : d292 pattern = 1) : d27 pattern ≤ (1 : Int) + d72 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d292 pattern = 1 := by simpa only [d27, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1721 pattern childGuard
    simpa only [d27, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d292 pattern = 1 := by simpa only [d27, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1718 pattern childGuard
    simpa only [d27, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1729 (pattern : Ten) (guard : d292 pattern = 1) : d31 pattern ≤ (1 : Int) + d75 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d292 pattern = 1 := by simpa only [d31, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1727 pattern childGuard
    simpa only [d31, d75, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d292 pattern = 1 := by simpa only [d31, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1728 pattern childGuard
    simpa only [d31, d75, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1730 (pattern : Ten) (guard : d292 pattern = 1) : d28 pattern ≤ (1 : Int) + d28 pattern := by
  omega
theorem c1731 (pattern : Ten) (guard : d292 pattern = 1) : d32 pattern ≤ (1 : Int) + d76 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d292 pattern = 1 := by simpa only [d32, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1730 pattern childGuard
    simpa only [d32, d76, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d292 pattern = 1 := by simpa only [d32, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1728 pattern childGuard
    simpa only [d32, d76, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1732 (pattern : Ten) (guard : d292 pattern = 1) : d34 pattern ≤ (1 : Int) + d78 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d292 pattern = 1 := by simpa only [d34, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1729 pattern childGuard
    simpa only [d34, d78, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d292 pattern = 1 := by simpa only [d34, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1731 pattern childGuard
    simpa only [d34, d78, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1733 (pattern : Ten) (guard : d292 pattern = 1) : d35 pattern ≤ (1 : Int) + d79 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d292 pattern = 1 := by simpa only [d35, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1726 pattern childGuard
    simpa only [d35, d79, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d292 pattern = 1 := by simpa only [d35, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1732 pattern childGuard
    simpa only [d35, d79, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1734 (pattern : Ten) (guard : d292 pattern = 1) : d36 pattern ≤ (1 : Int) + d80 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d292 pattern = 1 := by simpa only [d36, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1732 pattern childGuard
    simpa only [d36, d80, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d292 pattern = 1 := by simpa only [d36, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1718 pattern childGuard
    simpa only [d36, d80, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1735 (pattern : Ten) (guard : d292 pattern = 1) : d37 pattern ≤ (1 : Int) + d81 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d292 pattern = 1 := by simpa only [d37, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1733 pattern childGuard
    simpa only [d37, d81, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d292 pattern = 1 := by simpa only [d37, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1734 pattern childGuard
    simpa only [d37, d81, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1736 (pattern : Ten) (guard : d0 pattern = 1) : d0 pattern ≤ (1 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1737 (pattern : Ten) (guard : d1 pattern = 1) : d1 pattern ≤ (1 : Int) + d0 pattern := by
  change (1 : Int) ≤ (1 : Int) + 0
  decide
theorem c1738 (pattern : Ten) (guard : d171 pattern = 1) : d171 pattern ≤ (1 : Int) + d0 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1736 pattern childGuard
    simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1737 pattern childGuard
    simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1739 (pattern : Ten) (guard : d171 pattern = 1) : d10 pattern ≤ (1 : Int) + d10 pattern := by
  omega
theorem c1740 (pattern : Ten) (guard : d171 pattern = 1) : d173 pattern ≤ (1 : Int) + d12 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d171 pattern = 1 := by simpa only [d173, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1738 pattern childGuard
    simpa only [d173, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d171 pattern = 1 := by simpa only [d173, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1739 pattern childGuard
    simpa only [d173, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1741 (pattern : Ten) (guard : d171 pattern = 1) : d176 pattern ≤ (1 : Int) + d17 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d171 pattern = 1 := by simpa only [d176, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1738 pattern childGuard
    simpa only [d176, d17, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d171 pattern = 1 := by simpa only [d176, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1740 pattern childGuard
    simpa only [d176, d17, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1742 (pattern : Ten) (guard : d171 pattern = 1) : d177 pattern ≤ (1 : Int) + d18 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d171 pattern = 1 := by simpa only [d177, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1740 pattern childGuard
    simpa only [d177, d18, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d171 pattern = 1 := by simpa only [d177, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1739 pattern childGuard
    simpa only [d177, d18, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1743 (pattern : Ten) (guard : d171 pattern = 1) : d180 pattern ≤ (1 : Int) + d23 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d171 pattern = 1 := by simpa only [d180, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1741 pattern childGuard
    simpa only [d180, d23, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d171 pattern = 1 := by simpa only [d180, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1742 pattern childGuard
    simpa only [d180, d23, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1744 (pattern : Ten) (guard : d171 pattern = 1) : d181 pattern ≤ (1 : Int) + d26 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d171 pattern = 1 := by simpa only [d181, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1742 pattern childGuard
    simpa only [d181, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d171 pattern = 1 := by simpa only [d181, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1739 pattern childGuard
    simpa only [d181, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1745 (pattern : Ten) (guard : d171 pattern = 1) : d184 pattern ≤ (1 : Int) + d408 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d171 pattern = 1 := by simpa only [d184, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1743 pattern childGuard
    simpa only [d184, d408, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d171 pattern = 1 := by simpa only [d184, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1744 pattern childGuard
    simpa only [d184, d408, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1746 (pattern : Ten) (guard : d0 pattern = 1) : d2 pattern ≤ (1 : Int) + d2 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1747 (pattern : Ten) (guard : d1 pattern = 1) : d3 pattern ≤ (1 : Int) + d2 pattern := by
  change (3 : Int) ≤ (1 : Int) + 2
  decide
theorem c1748 (pattern : Ten) (guard : d171 pattern = 1) : d172 pattern ≤ (1 : Int) + d2 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d171, d172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1746 pattern childGuard
    simpa only [d171, d172, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d171, d172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1747 pattern childGuard
    simpa only [d171, d172, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1749 (pattern : Ten) (guard : d171 pattern = 1) : d174 pattern ≤ (1 : Int) + d15 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d171 pattern = 1 := by simpa only [d174, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1738 pattern childGuard
    simpa only [d174, d15, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d171 pattern = 1 := by simpa only [d174, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1748 pattern childGuard
    simpa only [d174, d15, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1750 (pattern : Ten) (guard : d171 pattern = 1) : d175 pattern ≤ (1 : Int) + d16 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d171 pattern = 1 := by simpa only [d175, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1748 pattern childGuard
    simpa only [d175, d16, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d171 pattern = 1 := by simpa only [d175, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1739 pattern childGuard
    simpa only [d175, d16, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1751 (pattern : Ten) (guard : d171 pattern = 1) : d178 pattern ≤ (1 : Int) + d21 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d171 pattern = 1 := by simpa only [d178, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1749 pattern childGuard
    simpa only [d178, d21, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d171 pattern = 1 := by simpa only [d178, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1750 pattern childGuard
    simpa only [d178, d21, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1752 (pattern : Ten) (guard : d171 pattern = 1) : d179 pattern ≤ (1 : Int) + d22 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d171 pattern = 1 := by simpa only [d179, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1750 pattern childGuard
    simpa only [d179, d22, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d171 pattern = 1 := by simpa only [d179, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1739 pattern childGuard
    simpa only [d179, d22, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1753 (pattern : Ten) (guard : d171 pattern = 1) : d182 pattern ≤ (1 : Int) + d25 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d171 pattern = 1 := by simpa only [d182, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1751 pattern childGuard
    simpa only [d182, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d171 pattern = 1 := by simpa only [d182, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1752 pattern childGuard
    simpa only [d182, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1754 (pattern : Ten) (guard : d171 pattern = 1) : d185 pattern ≤ (1 : Int) + d227 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d171 pattern = 1 := by simpa only [d185, d227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1753 pattern childGuard
    simpa only [d185, d227, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d171 pattern = 1 := by simpa only [d185, d227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1744 pattern childGuard
    simpa only [d185, d227, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1755 (pattern : Ten) (guard : d171 pattern = 1) : d188 pattern ≤ (1 : Int) + d409 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d171 pattern = 1 := by simpa only [d188, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1745 pattern childGuard
    simpa only [d188, d409, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d171 pattern = 1 := by simpa only [d188, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1754 pattern childGuard
    simpa only [d188, d409, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1756 (pattern : Ten) (guard : d171 pattern = 1) : d186 pattern ≤ (1 : Int) + d228 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d171 pattern = 1 := by simpa only [d186, d228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1744 pattern childGuard
    simpa only [d186, d228, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d171 pattern = 1 := by simpa only [d186, d228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1739 pattern childGuard
    simpa only [d186, d228, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1757 (pattern : Ten) (guard : d171 pattern = 1) : d183 pattern ≤ (1 : Int) + d28 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d171 pattern = 1 := by simpa only [d183, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1752 pattern childGuard
    simpa only [d183, d28, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d171 pattern = 1 := by simpa only [d183, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1739 pattern childGuard
    simpa only [d183, d28, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1758 (pattern : Ten) (guard : d171 pattern = 1) : d187 pattern ≤ (1 : Int) + d229 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d171 pattern = 1 := by simpa only [d187, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1757 pattern childGuard
    simpa only [d187, d229, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d171 pattern = 1 := by simpa only [d187, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1739 pattern childGuard
    simpa only [d187, d229, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1759 (pattern : Ten) (guard : d171 pattern = 1) : d189 pattern ≤ (1 : Int) + d231 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d171 pattern = 1 := by simpa only [d189, d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1756 pattern childGuard
    simpa only [d189, d231, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d171 pattern = 1 := by simpa only [d189, d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1758 pattern childGuard
    simpa only [d189, d231, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban41.Diagram
