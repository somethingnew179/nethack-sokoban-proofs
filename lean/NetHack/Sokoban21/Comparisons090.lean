/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons089
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c12600 (pattern : Twelve) (guard : d1865 pattern = 1) : d1494 pattern ≤ (1 : Int) + d20 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d1494, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11341 pattern childGuard
    simpa only [d1865, d1494, d20, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d1494, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12536 pattern childGuard
    simpa only [d1865, d1494, d20, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12601 (pattern : Twelve) (guard : d1865 pattern = 1) : d1499 pattern ≤ (1 : Int) + d1644 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1499, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12559 pattern childGuard
    simpa only [d1499, d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1499, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12600 pattern childGuard
    simpa only [d1499, d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12602 (pattern : Twelve) (guard : d1865 pattern = 1) : d1500 pattern ≤ (1 : Int) + d1644 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1500, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12518 pattern childGuard
    simpa only [d1500, d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1500, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12600 pattern childGuard
    simpa only [d1500, d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12603 (pattern : Twelve) (guard : d1865 pattern = 1) : d1511 pattern ≤ (1 : Int) + d1644 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12601 pattern childGuard
    simpa only [d1511, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12602 pattern childGuard
    simpa only [d1511, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12604 (pattern : Twelve) (guard : d1865 pattern = 1) : d1526 pattern ≤ (1 : Int) + d1668 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1526, d1668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12271 pattern childGuard
    simpa only [d1526, d1668, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1526, d1668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12603 pattern childGuard
    simpa only [d1526, d1668, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12605 (pattern : Twelve) (guard : d1865 pattern = 1) : d1537 pattern ≤ (1 : Int) + d1671 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1537, d1671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12604 pattern childGuard
    simpa only [d1537, d1671, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1537, d1671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12563 pattern childGuard
    simpa only [d1537, d1671, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12606 (pattern : Twelve) (guard : d1865 pattern = 1) : d1111 pattern ≤ (1 : Int) + d1644 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1111, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12559 pattern childGuard
    simpa only [d1111, d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1111, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12537 pattern childGuard
    simpa only [d1111, d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12607 (pattern : Twelve) (guard : d1865 pattern = 1) : d1512 pattern ≤ (1 : Int) + d1647 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1512, d1647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12606 pattern childGuard
    simpa only [d1512, d1647, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1512, d1647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12567 pattern childGuard
    simpa only [d1512, d1647, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12608 (pattern : Twelve) (guard : d1865 pattern = 1) : d1527 pattern ≤ (1 : Int) + d1651 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1527, d1651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12471 pattern childGuard
    simpa only [d1527, d1651, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1527, d1651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12607 pattern childGuard
    simpa only [d1527, d1651, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12609 (pattern : Twelve) (guard : d1865 pattern = 1) : d1538 pattern ≤ (1 : Int) + d1657 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1538, d1657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12608 pattern childGuard
    simpa only [d1538, d1657, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1538, d1657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12572 pattern childGuard
    simpa only [d1538, d1657, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12610 (pattern : Twelve) (guard : d1865 pattern = 1) : d1545 pattern ≤ (1 : Int) + d1674 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1545, d1674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12605 pattern childGuard
    simpa only [d1545, d1674, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1545, d1674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12609 pattern childGuard
    simpa only [d1545, d1674, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12611 (pattern : Twelve) (guard : d1865 pattern = 1) : d1501 pattern ≤ (1 : Int) + d1665 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1501, d1665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12518 pattern childGuard
    simpa only [d1501, d1665, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1501, d1665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12585 pattern childGuard
    simpa only [d1501, d1665, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12612 (pattern : Twelve) (guard : d1865 pattern = 1) : d1513 pattern ≤ (1 : Int) + d1666 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1513, d1666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12606 pattern childGuard
    simpa only [d1513, d1666, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1513, d1666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12611 pattern childGuard
    simpa only [d1513, d1666, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12613 (pattern : Twelve) (guard : d1865 pattern = 1) : d1528 pattern ≤ (1 : Int) + d1669 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1528, d1669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12273 pattern childGuard
    simpa only [d1528, d1669, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1528, d1669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12612 pattern childGuard
    simpa only [d1528, d1669, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12614 (pattern : Twelve) (guard : d1865 pattern = 1) : d1502 pattern ≤ (1 : Int) + d42 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1502, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12241 pattern childGuard
    simpa only [d1502, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1502, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12254 pattern childGuard
    simpa only [d1502, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12615 (pattern : Twelve) (guard : d1865 pattern = 1) : d1514 pattern ≤ (1 : Int) + d1289 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1514, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12570 pattern childGuard
    simpa only [d1514, d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1514, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12614 pattern childGuard
    simpa only [d1514, d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12616 (pattern : Twelve) (guard : d1865 pattern = 1) : d1529 pattern ≤ (1 : Int) + d1300 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1529, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12615 pattern childGuard
    simpa only [d1529, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1529, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12242 pattern childGuard
    simpa only [d1529, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12617 (pattern : Twelve) (guard : d1865 pattern = 1) : d1539 pattern ≤ (1 : Int) + d1672 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1539, d1672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12613 pattern childGuard
    simpa only [d1539, d1672, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1539, d1672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12616 pattern childGuard
    simpa only [d1539, d1672, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12618 (pattern : Twelve) (guard : d1865 pattern = 1) : d1112 pattern ≤ (1 : Int) + d128 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1112, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12565 pattern childGuard
    simpa only [d1112, d128, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1112, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12242 pattern childGuard
    simpa only [d1112, d128, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12619 (pattern : Twelve) (guard : d1865 pattern = 1) : d1503 pattern ≤ (1 : Int) + d183 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1503, d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12585 pattern childGuard
    simpa only [d1503, d183, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1503, d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12242 pattern childGuard
    simpa only [d1503, d183, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12620 (pattern : Twelve) (guard : d1865 pattern = 1) : d1515 pattern ≤ (1 : Int) + d1667 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1515, d1667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12618 pattern childGuard
    simpa only [d1515, d1667, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1515, d1667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12619 pattern childGuard
    simpa only [d1515, d1667, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12621 (pattern : Twelve) (guard : d1865 pattern = 1) : d1530 pattern ≤ (1 : Int) + d1670 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1530, d1670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12497 pattern childGuard
    simpa only [d1530, d1670, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1530, d1670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12620 pattern childGuard
    simpa only [d1530, d1670, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12622 (pattern : Twelve) (guard : d1865 pattern = 1) : d1504 pattern ≤ (1 : Int) + d822 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1504, d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12345 pattern childGuard
    simpa only [d1504, d822, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1504, d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12267 pattern childGuard
    simpa only [d1504, d822, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12623 (pattern : Twelve) (guard : d1865 pattern = 1) : d1516 pattern ≤ (1 : Int) + d1252 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1516, d1252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12622 pattern childGuard
    simpa only [d1516, d1252, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1516, d1252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12438 pattern childGuard
    simpa only [d1516, d1252, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12624 (pattern : Twelve) (guard : d1865 pattern = 1) : d1531 pattern ≤ (1 : Int) + d1626 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1531, d1626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12623 pattern childGuard
    simpa only [d1531, d1626, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1531, d1626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12242 pattern childGuard
    simpa only [d1531, d1626, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12625 (pattern : Twelve) (guard : d1865 pattern = 1) : d1540 pattern ≤ (1 : Int) + d1673 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1540, d1673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12621 pattern childGuard
    simpa only [d1540, d1673, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1540, d1673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12624 pattern childGuard
    simpa only [d1540, d1673, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12626 (pattern : Twelve) (guard : d1865 pattern = 1) : d1546 pattern ≤ (1 : Int) + d1675 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1546, d1675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12617 pattern childGuard
    simpa only [d1546, d1675, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1546, d1675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12625 pattern childGuard
    simpa only [d1546, d1675, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12627 (pattern : Twelve) (guard : d1865 pattern = 1) : d1547 pattern ≤ (1 : Int) + d1662 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1547, d1662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12609 pattern childGuard
    simpa only [d1547, d1662, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1547, d1662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12242 pattern childGuard
    simpa only [d1547, d1662, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12628 (pattern : Twelve) (guard : d1865 pattern = 1) : d1550 pattern ≤ (1 : Int) + d1676 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1550, d1676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12626 pattern childGuard
    simpa only [d1550, d1676, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1550, d1676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12627 pattern childGuard
    simpa only [d1550, d1676, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12629 (pattern : Twelve) (guard : d1865 pattern = 1) : d1553 pattern ≤ (1 : Int) + d1677 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1553, d1677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12610 pattern childGuard
    simpa only [d1553, d1677, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1553, d1677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12628 pattern childGuard
    simpa only [d1553, d1677, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12630 (pattern : Twelve) (guard : d1865 pattern = 1) : d1556 pattern ≤ (1 : Int) + d1678 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1556, d1678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12599 pattern childGuard
    simpa only [d1556, d1678, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1556, d1678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12629 pattern childGuard
    simpa only [d1556, d1678, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12631 (pattern : Twelve) (guard : d1865 pattern = 1) : d1494 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d1494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11406 pattern childGuard
    simpa only [d1865, d1494, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d1494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11237 pattern childGuard
    simpa only [d1865, d1494, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12632 (pattern : Twelve) (guard : d1865 pattern = 1) : d1753 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12456 pattern childGuard
    simpa only [d1753, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12631 pattern childGuard
    simpa only [d1753, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12633 (pattern : Twelve) (guard : d1865 pattern = 1) : d1754 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12457 pattern childGuard
    simpa only [d1754, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12242 pattern childGuard
    simpa only [d1754, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12634 (pattern : Twelve) (guard : d1865 pattern = 1) : d1763 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12632 pattern childGuard
    simpa only [d1763, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12633 pattern childGuard
    simpa only [d1763, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12635 (pattern : Twelve) (guard : d1865 pattern = 1) : d503 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12456 pattern childGuard
    simpa only [d503, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12242 pattern childGuard
    simpa only [d503, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12636 (pattern : Twelve) (guard : d1865 pattern = 1) : d1507 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12458 pattern childGuard
    simpa only [d1507, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12635 pattern childGuard
    simpa only [d1507, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12637 (pattern : Twelve) (guard : d1865 pattern = 1) : d1745 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12631 pattern childGuard
    simpa only [d1745, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12254 pattern childGuard
    simpa only [d1745, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12638 (pattern : Twelve) (guard : d1865 pattern = 1) : d1746 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12631 pattern childGuard
    simpa only [d1746, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12242 pattern childGuard
    simpa only [d1746, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12639 (pattern : Twelve) (guard : d1865 pattern = 1) : d1749 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12637 pattern childGuard
    simpa only [d1749, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12638 pattern childGuard
    simpa only [d1749, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12640 (pattern : Twelve) (guard : d1865 pattern = 1) : d1755 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12636 pattern childGuard
    simpa only [d1755, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12639 pattern childGuard
    simpa only [d1755, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12641 (pattern : Twelve) (guard : d1865 pattern = 1) : d1510 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12498 pattern childGuard
    simpa only [d1510, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12459 pattern childGuard
    simpa only [d1510, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12642 (pattern : Twelve) (guard : d1865 pattern = 1) : d1525 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12641 pattern childGuard
    simpa only [d1525, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12242 pattern childGuard
    simpa only [d1525, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12643 (pattern : Twelve) (guard : d1865 pattern = 1) : d1764 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12640 pattern childGuard
    simpa only [d1764, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12642 pattern childGuard
    simpa only [d1764, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12644 (pattern : Twelve) (guard : d1865 pattern = 1) : d1770 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12634 pattern childGuard
    simpa only [d1770, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12643 pattern childGuard
    simpa only [d1770, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12645 (pattern : Twelve) (guard : d1865 pattern = 1) : d1756 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12458 pattern childGuard
    simpa only [d1756, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12637 pattern childGuard
    simpa only [d1756, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12646 (pattern : Twelve) (guard : d1865 pattern = 1) : d1757 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12498 pattern childGuard
    simpa only [d1757, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12242 pattern childGuard
    simpa only [d1757, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12647 (pattern : Twelve) (guard : d1865 pattern = 1) : d1765 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12645 pattern childGuard
    simpa only [d1765, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12646 pattern childGuard
    simpa only [d1765, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12648 (pattern : Twelve) (guard : d1865 pattern = 1) : d1747 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12254 pattern childGuard
    simpa only [d1747, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12267 pattern childGuard
    simpa only [d1747, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12649 (pattern : Twelve) (guard : d1865 pattern = 1) : d1750 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12648 pattern childGuard
    simpa only [d1750, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12438 pattern childGuard
    simpa only [d1750, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12650 (pattern : Twelve) (guard : d1865 pattern = 1) : d1758 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12641 pattern childGuard
    simpa only [d1758, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12649 pattern childGuard
    simpa only [d1758, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12651 (pattern : Twelve) (guard : d1865 pattern = 1) : d1759 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12499 pattern childGuard
    simpa only [d1759, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12242 pattern childGuard
    simpa only [d1759, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12652 (pattern : Twelve) (guard : d1865 pattern = 1) : d1766 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12650 pattern childGuard
    simpa only [d1766, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12651 pattern childGuard
    simpa only [d1766, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12653 (pattern : Twelve) (guard : d1865 pattern = 1) : d1771 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12647 pattern childGuard
    simpa only [d1771, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12652 pattern childGuard
    simpa only [d1771, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12654 (pattern : Twelve) (guard : d1865 pattern = 1) : d1772 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12643 pattern childGuard
    simpa only [d1772, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12242 pattern childGuard
    simpa only [d1772, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12655 (pattern : Twelve) (guard : d1865 pattern = 1) : d1775 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12653 pattern childGuard
    simpa only [d1775, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12654 pattern childGuard
    simpa only [d1775, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12656 (pattern : Twelve) (guard : d1865 pattern = 1) : d1777 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12644 pattern childGuard
    simpa only [d1777, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12655 pattern childGuard
    simpa only [d1777, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12657 (pattern : Twelve) (guard : d1865 pattern = 1) : d1760 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12456 pattern childGuard
    simpa only [d1760, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12637 pattern childGuard
    simpa only [d1760, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12658 (pattern : Twelve) (guard : d1865 pattern = 1) : d1767 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12657 pattern childGuard
    simpa only [d1767, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12633 pattern childGuard
    simpa only [d1767, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12659 (pattern : Twelve) (guard : d1865 pattern = 1) : d1773 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12658 pattern childGuard
    simpa only [d1773, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12643 pattern childGuard
    simpa only [d1773, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12660 (pattern : Twelve) (guard : d1865 pattern = 1) : d1748 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12631 pattern childGuard
    simpa only [d1748, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12267 pattern childGuard
    simpa only [d1748, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12661 (pattern : Twelve) (guard : d1865 pattern = 1) : d1751 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12637 pattern childGuard
    simpa only [d1751, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12660 pattern childGuard
    simpa only [d1751, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12662 (pattern : Twelve) (guard : d1865 pattern = 1) : d1761 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12458 pattern childGuard
    simpa only [d1761, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12661 pattern childGuard
    simpa only [d1761, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12663 (pattern : Twelve) (guard : d1865 pattern = 1) : d1768 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12662 pattern childGuard
    simpa only [d1768, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12642 pattern childGuard
    simpa only [d1768, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12664 (pattern : Twelve) (guard : d1865 pattern = 1) : d183 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12267 pattern childGuard
    simpa only [d183, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12242 pattern childGuard
    simpa only [d183, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12665 (pattern : Twelve) (guard : d1865 pattern = 1) : d1752 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12438 pattern childGuard
    simpa only [d1752, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12664 pattern childGuard
    simpa only [d1752, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12666 (pattern : Twelve) (guard : d1865 pattern = 1) : d1762 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12641 pattern childGuard
    simpa only [d1762, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12665 pattern childGuard
    simpa only [d1762, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12667 (pattern : Twelve) (guard : d1865 pattern = 1) : d191 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12499 pattern childGuard
    simpa only [d191, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12242 pattern childGuard
    simpa only [d191, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12668 (pattern : Twelve) (guard : d1865 pattern = 1) : d202 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12667 pattern childGuard
    simpa only [d202, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12242 pattern childGuard
    simpa only [d202, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12669 (pattern : Twelve) (guard : d1865 pattern = 1) : d1769 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12666 pattern childGuard
    simpa only [d1769, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12668 pattern childGuard
    simpa only [d1769, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12670 (pattern : Twelve) (guard : d1865 pattern = 1) : d1774 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12663 pattern childGuard
    simpa only [d1774, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12669 pattern childGuard
    simpa only [d1774, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12671 (pattern : Twelve) (guard : d1865 pattern = 1) : d1776 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12670 pattern childGuard
    simpa only [d1776, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12654 pattern childGuard
    simpa only [d1776, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12672 (pattern : Twelve) (guard : d1865 pattern = 1) : d1778 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12659 pattern childGuard
    simpa only [d1778, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12671 pattern childGuard
    simpa only [d1778, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12673 (pattern : Twelve) (guard : d1865 pattern = 1) : d1779 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12656 pattern childGuard
    simpa only [d1779, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12672 pattern childGuard
    simpa only [d1779, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12674 (pattern : Twelve) (guard : d1865 pattern = 1) : d26 pattern ≤ (1 : Int) + d26 pattern := by
  omega
theorem c12675 (pattern : Twelve) (guard : d0 pattern = 1) : d7 pattern ≤ (1 : Int) + d7 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c12676 (pattern : Twelve) (guard : d1865 pattern = 1) : d17 pattern ≤ (1 : Int) + d7 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11061 pattern childGuard
    simpa only [d1865, d17, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12675 pattern childGuard
    simpa only [d1865, d17, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12677 (pattern : Twelve) (guard : d1865 pattern = 1) : d1 pattern ≤ (1 : Int) + d1 pattern := by
  omega
theorem c12678 (pattern : Twelve) (guard : d1865 pattern = 1) : d27 pattern ≤ (1 : Int) + d2057 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d27, d2057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12676 pattern childGuard
    simpa only [d27, d2057, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d27, d2057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12677 pattern childGuard
    simpa only [d27, d2057, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12679 (pattern : Twelve) (guard : d1865 pattern = 1) : d50 pattern ≤ (1 : Int) + d2058 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d50, d2058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12674 pattern childGuard
    simpa only [d50, d2058, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d50, d2058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12678 pattern childGuard
    simpa only [d50, d2058, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12680 (pattern : Twelve) (guard : d1865 pattern = 1) : d72 pattern ≤ (1 : Int) + d2059 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d72, d2059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12208 pattern childGuard
    simpa only [d72, d2059, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d72, d2059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12679 pattern childGuard
    simpa only [d72, d2059, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12681 (pattern : Twelve) (guard : d1 pattern = 1) : d8 pattern ≤ (1 : Int) + d9 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d8, d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11213 pattern childGuard
    simpa only [d8, d9, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d8, d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11137 pattern childGuard
    simpa only [d8, d9, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12682 (pattern : Twelve) (guard : d0 pattern = 1) : d9 pattern ≤ (1 : Int) + d9 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c12683 (pattern : Twelve) (guard : d1865 pattern = 1) : d18 pattern ≤ (1 : Int) + d9 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12681 pattern childGuard
    simpa only [d1865, d18, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12682 pattern childGuard
    simpa only [d1865, d18, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12684 (pattern : Twelve) (guard : d1865 pattern = 1) : d28 pattern ≤ (1 : Int) + d2060 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d28, d2060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12676 pattern childGuard
    simpa only [d28, d2060, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d28, d2060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12683 pattern childGuard
    simpa only [d28, d2060, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12685 (pattern : Twelve) (guard : d1 pattern = 1) : d10 pattern ≤ (1 : Int) + d11 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d10, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11060 pattern childGuard
    simpa only [d10, d11, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d10, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11137 pattern childGuard
    simpa only [d10, d11, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12686 (pattern : Twelve) (guard : d0 pattern = 1) : d11 pattern ≤ (1 : Int) + d11 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c12687 (pattern : Twelve) (guard : d1865 pattern = 1) : d19 pattern ≤ (1 : Int) + d11 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12685 pattern childGuard
    simpa only [d1865, d19, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12686 pattern childGuard
    simpa only [d1865, d19, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12688 (pattern : Twelve) (guard : d1865 pattern = 1) : d29 pattern ≤ (1 : Int) + d2061 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d29, d2061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12687 pattern childGuard
    simpa only [d29, d2061, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d29, d2061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12242 pattern childGuard
    simpa only [d29, d2061, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12689 (pattern : Twelve) (guard : d1865 pattern = 1) : d51 pattern ≤ (1 : Int) + d2062 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d51, d2062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12684 pattern childGuard
    simpa only [d51, d2062, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d51, d2062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12688 pattern childGuard
    simpa only [d51, d2062, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12690 (pattern : Twelve) (guard : d1865 pattern = 1) : d73 pattern ≤ (1 : Int) + d2063 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d73, d2063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12208 pattern childGuard
    simpa only [d73, d2063, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d73, d2063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12689 pattern childGuard
    simpa only [d73, d2063, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12691 (pattern : Twelve) (guard : d1865 pattern = 1) : d91 pattern ≤ (1 : Int) + d2064 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d91, d2064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12680 pattern childGuard
    simpa only [d91, d2064, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d91, d2064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12690 pattern childGuard
    simpa only [d91, d2064, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12692 (pattern : Twelve) (guard : d1865 pattern = 1) : d30 pattern ≤ (1 : Int) + d30 pattern := by
  omega
theorem c12693 (pattern : Twelve) (guard : d0 pattern = 1) : d13 pattern ≤ (1 : Int) + d13 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c12694 (pattern : Twelve) (guard : d1865 pattern = 1) : d20 pattern ≤ (1 : Int) + d13 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11392 pattern childGuard
    simpa only [d1865, d20, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12693 pattern childGuard
    simpa only [d1865, d20, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12695 (pattern : Twelve) (guard : d1865 pattern = 1) : d31 pattern ≤ (1 : Int) + d2065 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d31, d2065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12208 pattern childGuard
    simpa only [d31, d2065, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d31, d2065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12694 pattern childGuard
    simpa only [d31, d2065, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12696 (pattern : Twelve) (guard : d1865 pattern = 1) : d52 pattern ≤ (1 : Int) + d2066 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d52, d2066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12692 pattern childGuard
    simpa only [d52, d2066, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d52, d2066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12695 pattern childGuard
    simpa only [d52, d2066, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12697 (pattern : Twelve) (guard : d0 pattern = 1) : d14 pattern ≤ (1 : Int) + d14 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c12698 (pattern : Twelve) (guard : d1865 pattern = 1) : d21 pattern ≤ (1 : Int) + d14 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11393 pattern childGuard
    simpa only [d1865, d21, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12697 pattern childGuard
    simpa only [d1865, d21, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12699 (pattern : Twelve) (guard : d1865 pattern = 1) : d32 pattern ≤ (1 : Int) + d2067 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d32, d2067, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12676 pattern childGuard
    simpa only [d32, d2067, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d32, d2067, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12698 pattern childGuard
    simpa only [d32, d2067, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12700 (pattern : Twelve) (guard : d1865 pattern = 1) : d53 pattern ≤ (1 : Int) + d2068 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d53, d2068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12692 pattern childGuard
    simpa only [d53, d2068, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d53, d2068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12699 pattern childGuard
    simpa only [d53, d2068, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12701 (pattern : Twelve) (guard : d1865 pattern = 1) : d74 pattern ≤ (1 : Int) + d2069 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d74, d2069, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12696 pattern childGuard
    simpa only [d74, d2069, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d74, d2069, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12700 pattern childGuard
    simpa only [d74, d2069, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12702 (pattern : Twelve) (guard : d1865 pattern = 1) : d33 pattern ≤ (1 : Int) + d35 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d33, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12208 pattern childGuard
    simpa only [d33, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d33, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12267 pattern childGuard
    simpa only [d33, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12703 (pattern : Twelve) (guard : d1865 pattern = 1) : d54 pattern ≤ (1 : Int) + d56 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d54, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12692 pattern childGuard
    simpa only [d54, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d54, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12702 pattern childGuard
    simpa only [d54, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12704 (pattern : Twelve) (guard : d1865 pattern = 1) : d23 pattern ≤ (1 : Int) + d9 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11138 pattern childGuard
    simpa only [d1865, d23, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12682 pattern childGuard
    simpa only [d1865, d23, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12705 (pattern : Twelve) (guard : d1865 pattern = 1) : d34 pattern ≤ (1 : Int) + d2060 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d34, d2060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12676 pattern childGuard
    simpa only [d34, d2060, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d34, d2060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12704 pattern childGuard
    simpa only [d34, d2060, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12706 (pattern : Twelve) (guard : d1865 pattern = 1) : d55 pattern ≤ (1 : Int) + d2062 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d55, d2062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12705 pattern childGuard
    simpa only [d55, d2062, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d55, d2062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12688 pattern childGuard
    simpa only [d55, d2062, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12707 (pattern : Twelve) (guard : d1865 pattern = 1) : d75 pattern ≤ (1 : Int) + d2070 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d75, d2070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12703 pattern childGuard
    simpa only [d75, d2070, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d75, d2070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12706 pattern childGuard
    simpa only [d75, d2070, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12708 (pattern : Twelve) (guard : d1865 pattern = 1) : d92 pattern ≤ (1 : Int) + d2071 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d92, d2071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12701 pattern childGuard
    simpa only [d92, d2071, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d92, d2071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12707 pattern childGuard
    simpa only [d92, d2071, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12709 (pattern : Twelve) (guard : d1865 pattern = 1) : d102 pattern ≤ (1 : Int) + d2072 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d102, d2072, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12691 pattern childGuard
    simpa only [d102, d2072, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d102, d2072, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12708 pattern childGuard
    simpa only [d102, d2072, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12710 (pattern : Twelve) (guard : d1865 pattern = 1) : d76 pattern ≤ (1 : Int) + d2063 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d76, d2063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12208 pattern childGuard
    simpa only [d76, d2063, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d76, d2063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12706 pattern childGuard
    simpa only [d76, d2063, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12711 (pattern : Twelve) (guard : d1865 pattern = 1) : d93 pattern ≤ (1 : Int) + d2064 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d93, d2064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12680 pattern childGuard
    simpa only [d93, d2064, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d93, d2064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12710 pattern childGuard
    simpa only [d93, d2064, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12712 (pattern : Twelve) (guard : d1865 pattern = 1) : d56 pattern ≤ (1 : Int) + d56 pattern := by
  omega
theorem c12713 (pattern : Twelve) (guard : d1865 pattern = 1) : d36 pattern ≤ (1 : Int) + d2073 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d36, d2073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12676 pattern childGuard
    simpa only [d36, d2073, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d36, d2073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12242 pattern childGuard
    simpa only [d36, d2073, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12714 (pattern : Twelve) (guard : d1865 pattern = 1) : d57 pattern ≤ (1 : Int) + d2074 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d57, d2074, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12692 pattern childGuard
    simpa only [d57, d2074, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d57, d2074, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12713 pattern childGuard
    simpa only [d57, d2074, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12715 (pattern : Twelve) (guard : d1865 pattern = 1) : d77 pattern ≤ (1 : Int) + d2075 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d77, d2075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12712 pattern childGuard
    simpa only [d77, d2075, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d77, d2075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12714 pattern childGuard
    simpa only [d77, d2075, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12716 (pattern : Twelve) (guard : d1865 pattern = 1) : d78 pattern ≤ (1 : Int) + d2070 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d78, d2070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12712 pattern childGuard
    simpa only [d78, d2070, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d78, d2070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12706 pattern childGuard
    simpa only [d78, d2070, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12717 (pattern : Twelve) (guard : d1865 pattern = 1) : d94 pattern ≤ (1 : Int) + d2076 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d94, d2076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12715 pattern childGuard
    simpa only [d94, d2076, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d94, d2076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12716 pattern childGuard
    simpa only [d94, d2076, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12718 (pattern : Twelve) (guard : d1865 pattern = 1) : d103 pattern ≤ (1 : Int) + d2077 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d103, d2077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12711 pattern childGuard
    simpa only [d103, d2077, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d103, d2077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12717 pattern childGuard
    simpa only [d103, d2077, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12719 (pattern : Twelve) (guard : d1865 pattern = 1) : d110 pattern ≤ (1 : Int) + d2078 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d110, d2078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12709 pattern childGuard
    simpa only [d110, d2078, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d110, d2078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12718 pattern childGuard
    simpa only [d110, d2078, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12720 (pattern : Twelve) (guard : d1865 pattern = 1) : d3 pattern ≤ (1 : Int) + d3 pattern := by
  omega
theorem c12721 (pattern : Twelve) (guard : d1865 pattern = 1) : d37 pattern ≤ (1 : Int) + d2079 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d37, d2079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12676 pattern childGuard
    simpa only [d37, d2079, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d37, d2079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12720 pattern childGuard
    simpa only [d37, d2079, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12722 (pattern : Twelve) (guard : d1865 pattern = 1) : d58 pattern ≤ (1 : Int) + d2080 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d58, d2080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12692 pattern childGuard
    simpa only [d58, d2080, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d58, d2080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12721 pattern childGuard
    simpa only [d58, d2080, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12723 (pattern : Twelve) (guard : d1865 pattern = 1) : d79 pattern ≤ (1 : Int) + d2081 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d79, d2081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12692 pattern childGuard
    simpa only [d79, d2081, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d79, d2081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12722 pattern childGuard
    simpa only [d79, d2081, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12724 (pattern : Twelve) (guard : d1865 pattern = 1) : d80 pattern ≤ (1 : Int) + d2082 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d80, d2082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12692 pattern childGuard
    simpa only [d80, d2082, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d80, d2082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12706 pattern childGuard
    simpa only [d80, d2082, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12725 (pattern : Twelve) (guard : d1865 pattern = 1) : d95 pattern ≤ (1 : Int) + d2083 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d95, d2083, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12723 pattern childGuard
    simpa only [d95, d2083, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d95, d2083, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12724 pattern childGuard
    simpa only [d95, d2083, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12726 (pattern : Twelve) (guard : d1865 pattern = 1) : d59 pattern ≤ (1 : Int) + d59 pattern := by
  omega
theorem c12727 (pattern : Twelve) (guard : d1865 pattern = 1) : d38 pattern ≤ (1 : Int) + d38 pattern := by
  omega
theorem c12728 (pattern : Twelve) (guard : d1865 pattern = 1) : d40 pattern ≤ (1 : Int) + d2084 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d40, d2084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12704 pattern childGuard
    simpa only [d40, d2084, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d40, d2084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12242 pattern childGuard
    simpa only [d40, d2084, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12729 (pattern : Twelve) (guard : d1865 pattern = 1) : d60 pattern ≤ (1 : Int) + d2085 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d60, d2085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12727 pattern childGuard
    simpa only [d60, d2085, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d60, d2085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12728 pattern childGuard
    simpa only [d60, d2085, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12730 (pattern : Twelve) (guard : d1865 pattern = 1) : d81 pattern ≤ (1 : Int) + d2086 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d81, d2086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12726 pattern childGuard
    simpa only [d81, d2086, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d81, d2086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12729 pattern childGuard
    simpa only [d81, d2086, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12731 (pattern : Twelve) (guard : d0 pattern = 1) : d15 pattern ≤ (1 : Int) + d15 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c12732 (pattern : Twelve) (guard : d1865 pattern = 1) : d24 pattern ≤ (1 : Int) + d15 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12489 pattern childGuard
    simpa only [d1865, d24, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12731 pattern childGuard
    simpa only [d1865, d24, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12733 (pattern : Twelve) (guard : d1865 pattern = 1) : d41 pattern ≤ (1 : Int) + d2087 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d41, d2087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12704 pattern childGuard
    simpa only [d41, d2087, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d41, d2087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12732 pattern childGuard
    simpa only [d41, d2087, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12734 (pattern : Twelve) (guard : d1 pattern = 1) : d16 pattern ≤ (1 : Int) + d12 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d16, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11137 pattern childGuard
    simpa only [d16, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d16, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11316 pattern childGuard
    simpa only [d16, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12735 (pattern : Twelve) (guard : d0 pattern = 1) : d12 pattern ≤ (1 : Int) + d12 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c12736 (pattern : Twelve) (guard : d1865 pattern = 1) : d25 pattern ≤ (1 : Int) + d12 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12734 pattern childGuard
    simpa only [d1865, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12735 pattern childGuard
    simpa only [d1865, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12737 (pattern : Twelve) (guard : d1865 pattern = 1) : d42 pattern ≤ (1 : Int) + d2088 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d42, d2088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12736 pattern childGuard
    simpa only [d42, d2088, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d42, d2088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12242 pattern childGuard
    simpa only [d42, d2088, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12738 (pattern : Twelve) (guard : d1865 pattern = 1) : d61 pattern ≤ (1 : Int) + d2089 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d61, d2089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12733 pattern childGuard
    simpa only [d61, d2089, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d61, d2089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12737 pattern childGuard
    simpa only [d61, d2089, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12739 (pattern : Twelve) (guard : d1865 pattern = 1) : d82 pattern ≤ (1 : Int) + d2090 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d82, d2090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12726 pattern childGuard
    simpa only [d82, d2090, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d82, d2090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12738 pattern childGuard
    simpa only [d82, d2090, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
