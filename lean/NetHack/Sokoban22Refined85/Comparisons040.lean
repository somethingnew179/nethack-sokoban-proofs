/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons039
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare5600 (p : Pattern) (guard : d4471 p = 1) : d751 p ≤ (0 : Int) + d1599 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4471 p = 1 := by simpa only [d751, d1599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5597 p hg
    simpa only [d751, d1599, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4471 p = 1 := by simpa only [d751, d1599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5599 p hg
    simpa only [d751, d1599, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5601 (p : Pattern) (guard : d4471 p = 1) : d752 p ≤ (0 : Int) + d1600 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4471 p = 1 := by simpa only [d752, d1600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5594 p hg
    simpa only [d752, d1600, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4471 p = 1 := by simpa only [d752, d1600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5600 p hg
    simpa only [d752, d1600, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5602 (p : Pattern) (guard : d0 p = 1) : d405 p ≤ (0 : Int) + d1578 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5603 (p : Pattern) (guard : d4471 p = 1) : d753 p ≤ (0 : Int) + d1604 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4471, d753, d1604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5222 p hg
    simpa only [d4471, d753, d1604, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4471, d753, d1604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5602 p hg
    simpa only [d4471, d753, d1604, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5604 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d1586 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5605 (p : Pattern) (guard : d4471 p = 1) : d746 p ≤ (0 : Int) + d1586 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4471, d746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5207 p hg
    simpa only [d4471, d746, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4471, d746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5604 p hg
    simpa only [d4471, d746, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5606 (p : Pattern) (guard : d4471 p = 1) : d754 p ≤ (0 : Int) + d1605 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4471 p = 1 := by simpa only [d754, d1605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5603 p hg
    simpa only [d754, d1605, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4471 p = 1 := by simpa only [d754, d1605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5605 p hg
    simpa only [d754, d1605, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5607 (p : Pattern) (guard : d4471 p = 1) : d755 p ≤ (0 : Int) + d1606 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4471 p = 1 := by simpa only [d755, d1606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5606 p hg
    simpa only [d755, d1606, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4471 p = 1 := by simpa only [d755, d1606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5593 p hg
    simpa only [d755, d1606, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5608 (p : Pattern) (guard : d4471 p = 1) : d756 p ≤ (0 : Int) + d1607 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4471 p = 1 := by simpa only [d756, d1607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5593 p hg
    simpa only [d756, d1607, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4471 p = 1 := by simpa only [d756, d1607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5563 p hg
    simpa only [d756, d1607, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5609 (p : Pattern) (guard : d4471 p = 1) : d757 p ≤ (0 : Int) + d1608 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4471 p = 1 := by simpa only [d757, d1608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5607 p hg
    simpa only [d757, d1608, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4471 p = 1 := by simpa only [d757, d1608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5608 p hg
    simpa only [d757, d1608, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5610 (p : Pattern) (guard : d4471 p = 1) : d758 p ≤ (0 : Int) + d1609 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4471 p = 1 := by simpa only [d758, d1609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5601 p hg
    simpa only [d758, d1609, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4471 p = 1 := by simpa only [d758, d1609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5609 p hg
    simpa only [d758, d1609, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5611 (p : Pattern) (guard : d4471 p = 1) : d759 p ≤ (0 : Int) + d1610 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4471 p = 1 := by simpa only [d759, d1610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5566 p hg
    simpa only [d759, d1610, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4471 p = 1 := by simpa only [d759, d1610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5610 p hg
    simpa only [d759, d1610, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5612 (p : Pattern) (guard : d4471 p = 1) : d760 p ≤ (0 : Int) + d1611 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4471 p = 1 := by simpa only [d760, d1611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5583 p hg
    simpa only [d760, d1611, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4471 p = 1 := by simpa only [d760, d1611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5611 p hg
    simpa only [d760, d1611, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5613 (p : Pattern) (guard : d0 p = 1) : d405 p ≤ (0 : Int) + d1613 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5614 (p : Pattern) (guard : d4471 p = 1) : d717 p ≤ (0 : Int) + d1614 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4471, d717, d1614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5114 p hg
    simpa only [d4471, d717, d1614, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4471, d717, d1614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5613 p hg
    simpa only [d4471, d717, d1614, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5615 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d1617 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5616 (p : Pattern) (guard : d4471 p = 1) : d714 p ≤ (0 : Int) + d1618 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4471, d714, d1618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5105 p hg
    simpa only [d4471, d714, d1618, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4471, d714, d1618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5615 p hg
    simpa only [d4471, d714, d1618, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5617 (p : Pattern) (guard : d4471 p = 1) : d718 p ≤ (0 : Int) + d1619 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4471 p = 1 := by simpa only [d718, d1619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5614 p hg
    simpa only [d718, d1619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4471 p = 1 := by simpa only [d718, d1619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5616 p hg
    simpa only [d718, d1619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5618 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d1625 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5619 (p : Pattern) (guard : d4471 p = 1) : d761 p ≤ (0 : Int) + d1626 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4471, d761, d1626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5249 p hg
    simpa only [d4471, d761, d1626, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4471, d761, d1626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5618 p hg
    simpa only [d4471, d761, d1626, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5620 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d1632 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5621 (p : Pattern) (guard : d4471 p = 1) : d762 p ≤ (0 : Int) + d1633 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4471, d762, d1633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5259 p hg
    simpa only [d4471, d762, d1633, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4471, d762, d1633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5620 p hg
    simpa only [d4471, d762, d1633, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5622 (p : Pattern) (guard : d4471 p = 1) : d763 p ≤ (0 : Int) + d1634 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4471 p = 1 := by simpa only [d763, d1634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5619 p hg
    simpa only [d763, d1634, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4471 p = 1 := by simpa only [d763, d1634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5621 p hg
    simpa only [d763, d1634, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5623 (p : Pattern) (guard : d4471 p = 1) : d764 p ≤ (0 : Int) + d1635 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4471 p = 1 := by simpa only [d764, d1635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5617 p hg
    simpa only [d764, d1635, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4471 p = 1 := by simpa only [d764, d1635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5622 p hg
    simpa only [d764, d1635, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5624 (p : Pattern) (guard : d4471 p = 1) : d765 p ≤ (0 : Int) + d1636 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4471 p = 1 := by simpa only [d765, d1636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5622 p hg
    simpa only [d765, d1636, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4471 p = 1 := by simpa only [d765, d1636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5563 p hg
    simpa only [d765, d1636, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5625 (p : Pattern) (guard : d4471 p = 1) : d766 p ≤ (0 : Int) + d1637 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4471 p = 1 := by simpa only [d766, d1637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5623 p hg
    simpa only [d766, d1637, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4471 p = 1 := by simpa only [d766, d1637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5624 p hg
    simpa only [d766, d1637, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5626 (p : Pattern) (guard : d4471 p = 1) : d767 p ≤ (0 : Int) + d1638 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4471 p = 1 := by simpa only [d767, d1638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5574 p hg
    simpa only [d767, d1638, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4471 p = 1 := by simpa only [d767, d1638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5625 p hg
    simpa only [d767, d1638, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5627 (p : Pattern) (guard : d4471 p = 1) : d768 p ≤ (0 : Int) + d1639 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4471 p = 1 := by simpa only [d768, d1639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5566 p hg
    simpa only [d768, d1639, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4471 p = 1 := by simpa only [d768, d1639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5626 p hg
    simpa only [d768, d1639, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5628 (p : Pattern) (guard : d0 p = 1) : d409 p ≤ (0 : Int) + d1643 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5629 (p : Pattern) (guard : d4471 p = 1) : d769 p ≤ (0 : Int) + d1644 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4471, d769, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5273 p hg
    simpa only [d4471, d769, d1644, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4471, d769, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5628 p hg
    simpa only [d4471, d769, d1644, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5630 (p : Pattern) (guard : d4471 p = 1) : d770 p ≤ (0 : Int) + d1645 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4471 p = 1 := by simpa only [d770, d1645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5585 p hg
    simpa only [d770, d1645, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4471 p = 1 := by simpa only [d770, d1645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5629 p hg
    simpa only [d770, d1645, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5631 (p : Pattern) (guard : d4471 p = 1) : d771 p ≤ (0 : Int) + d1646 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4471, d771, d1646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5281 p hg
    simpa only [d4471, d771, d1646, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4471, d771, d1646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5591 p hg
    simpa only [d4471, d771, d1646, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5632 (p : Pattern) (guard : d4471 p = 1) : d772 p ≤ (0 : Int) + d1647 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4471 p = 1 := by simpa only [d772, d1647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5590 p hg
    simpa only [d772, d1647, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4471 p = 1 := by simpa only [d772, d1647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5631 p hg
    simpa only [d772, d1647, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5633 (p : Pattern) (guard : d4471 p = 1) : d773 p ≤ (0 : Int) + d1648 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4471 p = 1 := by simpa only [d773, d1648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5630 p hg
    simpa only [d773, d1648, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4471 p = 1 := by simpa only [d773, d1648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5632 p hg
    simpa only [d773, d1648, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5634 (p : Pattern) (guard : d4471 p = 1) : d774 p ≤ (0 : Int) + d1647 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4471 p = 1 := by simpa only [d774, d1647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5596 p hg
    simpa only [d774, d1647, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4471 p = 1 := by simpa only [d774, d1647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5631 p hg
    simpa only [d774, d1647, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5635 (p : Pattern) (guard : d4471 p = 1) : d775 p ≤ (0 : Int) + d1649 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4471 p = 1 := by simpa only [d775, d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5634 p hg
    simpa only [d775, d1649, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4471 p = 1 := by simpa only [d775, d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5599 p hg
    simpa only [d775, d1649, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5636 (p : Pattern) (guard : d4471 p = 1) : d776 p ≤ (0 : Int) + d1650 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4471 p = 1 := by simpa only [d776, d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5633 p hg
    simpa only [d776, d1650, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4471 p = 1 := by simpa only [d776, d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5635 p hg
    simpa only [d776, d1650, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5637 (p : Pattern) (guard : d0 p = 1) : d405 p ≤ (0 : Int) + d1652 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5638 (p : Pattern) (guard : d4471 p = 1) : d753 p ≤ (0 : Int) + d1653 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4471, d753, d1653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5222 p hg
    simpa only [d4471, d753, d1653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4471, d753, d1653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5637 p hg
    simpa only [d4471, d753, d1653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5639 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d1655 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5640 (p : Pattern) (guard : d4471 p = 1) : d771 p ≤ (0 : Int) + d1656 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4471, d771, d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5281 p hg
    simpa only [d4471, d771, d1656, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4471, d771, d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5639 p hg
    simpa only [d4471, d771, d1656, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5641 (p : Pattern) (guard : d4471 p = 1) : d777 p ≤ (0 : Int) + d1657 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4471 p = 1 := by simpa only [d777, d1657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5638 p hg
    simpa only [d777, d1657, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4471 p = 1 := by simpa only [d777, d1657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5640 p hg
    simpa only [d777, d1657, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5642 (p : Pattern) (guard : d4471 p = 1) : d778 p ≤ (0 : Int) + d1661 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4471, d778, d1661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5304 p hg
    simpa only [d4471, d778, d1661, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4471, d778, d1661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5591 p hg
    simpa only [d4471, d778, d1661, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5643 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d1662 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5644 (p : Pattern) (guard : d4471 p = 1) : d779 p ≤ (0 : Int) + d1663 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4471, d779, d1663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5307 p hg
    simpa only [d4471, d779, d1663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4471, d779, d1663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5643 p hg
    simpa only [d4471, d779, d1663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5645 (p : Pattern) (guard : d4471 p = 1) : d780 p ≤ (0 : Int) + d1664 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4471 p = 1 := by simpa only [d780, d1664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5642 p hg
    simpa only [d780, d1664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4471 p = 1 := by simpa only [d780, d1664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5644 p hg
    simpa only [d780, d1664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5646 (p : Pattern) (guard : d4471 p = 1) : d781 p ≤ (0 : Int) + d1665 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4471 p = 1 := by simpa only [d781, d1665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5641 p hg
    simpa only [d781, d1665, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4471 p = 1 := by simpa only [d781, d1665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5645 p hg
    simpa only [d781, d1665, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5647 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d1673 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5648 (p : Pattern) (guard : d4471 p = 1) : d782 p ≤ (0 : Int) + d1674 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4471, d782, d1674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5317 p hg
    simpa only [d4471, d782, d1674, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4471, d782, d1674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5647 p hg
    simpa only [d4471, d782, d1674, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5649 (p : Pattern) (guard : d4471 p = 1) : d783 p ≤ (0 : Int) + d1675 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4471 p = 1 := by simpa only [d783, d1675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5648 p hg
    simpa only [d783, d1675, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4471 p = 1 := by simpa only [d783, d1675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5644 p hg
    simpa only [d783, d1675, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5650 (p : Pattern) (guard : d4471 p = 1) : d784 p ≤ (0 : Int) + d1676 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4471 p = 1 := by simpa only [d784, d1676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5649 p hg
    simpa only [d784, d1676, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4471 p = 1 := by simpa only [d784, d1676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5563 p hg
    simpa only [d784, d1676, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5651 (p : Pattern) (guard : d4471 p = 1) : d785 p ≤ (0 : Int) + d1677 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4471 p = 1 := by simpa only [d785, d1677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5646 p hg
    simpa only [d785, d1677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4471 p = 1 := by simpa only [d785, d1677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5650 p hg
    simpa only [d785, d1677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5652 (p : Pattern) (guard : d4471 p = 1) : d786 p ≤ (0 : Int) + d1678 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4471 p = 1 := by simpa only [d786, d1678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5636 p hg
    simpa only [d786, d1678, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4471 p = 1 := by simpa only [d786, d1678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5651 p hg
    simpa only [d786, d1678, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5653 (p : Pattern) (guard : d4471 p = 1) : d787 p ≤ (0 : Int) + d1679 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4471 p = 1 := by simpa only [d787, d1679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5566 p hg
    simpa only [d787, d1679, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4471 p = 1 := by simpa only [d787, d1679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5652 p hg
    simpa only [d787, d1679, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5654 (p : Pattern) (guard : d4471 p = 1) : d788 p ≤ (0 : Int) + d1680 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4471 p = 1 := by simpa only [d788, d1680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5627 p hg
    simpa only [d788, d1680, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4471 p = 1 := by simpa only [d788, d1680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5653 p hg
    simpa only [d788, d1680, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5655 (p : Pattern) (guard : d4471 p = 1) : d789 p ≤ (0 : Int) + d1681 p := by
  cases selected : p 48 with
  | false =>
    have hg : d4471 p = 1 := by simpa only [d789, d1681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5612 p hg
    simpa only [d789, d1681, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4471 p = 1 := by simpa only [d789, d1681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5654 p hg
    simpa only [d789, d1681, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5656 (p : Pattern) (guard : d0 p = 1) : d14 p ≤ (0 : Int) + d14 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5657 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d14 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5658 (p : Pattern) (guard : d4474 p = 1) : d15 p ≤ (0 : Int) + d14 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1207 p hg
    simpa only [d4474, d15, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5657 p hg
    simpa only [d4474, d15, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5659 (p : Pattern) (guard : d4475 p = 1) : d16 p ≤ (0 : Int) + d14 p := by
  cases selected : p 182 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4475, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5656 p hg
    simpa only [d4475, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d4475, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5658 p hg
    simpa only [d4475, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5660 (p : Pattern) (guard : d0 p = 1) : d18 p ≤ (0 : Int) + d18 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5661 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d18 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5662 (p : Pattern) (guard : d4474 p = 1) : d19 p ≤ (0 : Int) + d18 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2003 p hg
    simpa only [d4474, d19, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5661 p hg
    simpa only [d4474, d19, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5663 (p : Pattern) (guard : d4475 p = 1) : d20 p ≤ (0 : Int) + d18 p := by
  cases selected : p 182 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4475, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5660 p hg
    simpa only [d4475, d20, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d4475, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5662 p hg
    simpa only [d4475, d20, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5664 (p : Pattern) (guard : d4475 p = 1) : d21 p ≤ (0 : Int) + d4477 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d21, d4477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5659 p hg
    simpa only [d21, d4477, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d21, d4477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5663 p hg
    simpa only [d21, d4477, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5665 (p : Pattern) (guard : d4475 p = 1) : d22 p ≤ (0 : Int) + d4478 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d22, d4478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5659 p hg
    simpa only [d22, d4478, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d22, d4478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5664 p hg
    simpa only [d22, d4478, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5666 (p : Pattern) (guard : d0 p = 1) : d24 p ≤ (0 : Int) + d24 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5667 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d24 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5668 (p : Pattern) (guard : d4474 p = 1) : d25 p ≤ (0 : Int) + d24 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2010 p hg
    simpa only [d4474, d25, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5667 p hg
    simpa only [d4474, d25, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5669 (p : Pattern) (guard : d4475 p = 1) : d26 p ≤ (0 : Int) + d24 p := by
  cases selected : p 182 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4475, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5666 p hg
    simpa only [d4475, d26, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d4475, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5668 p hg
    simpa only [d4475, d26, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5670 (p : Pattern) (guard : d4475 p = 1) : d12 p ≤ (0 : Int) + d12 p := by
  omega
theorem compare5671 (p : Pattern) (guard : d4475 p = 1) : d27 p ≤ (0 : Int) + d4479 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d27, d4479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5669 p hg
    simpa only [d27, d4479, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d27, d4479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5670 p hg
    simpa only [d27, d4479, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5672 (p : Pattern) (guard : d4475 p = 1) : d28 p ≤ (0 : Int) + d4480 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d28, d4480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5664 p hg
    simpa only [d28, d4480, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d28, d4480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5671 p hg
    simpa only [d28, d4480, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5673 (p : Pattern) (guard : d4475 p = 1) : d29 p ≤ (0 : Int) + d4481 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d29, d4481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5665 p hg
    simpa only [d29, d4481, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d29, d4481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5672 p hg
    simpa only [d29, d4481, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5674 (p : Pattern) (guard : d0 p = 1) : d376 p ≤ (0 : Int) + d4481 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5675 (p : Pattern) (guard : d4476 p = 1) : d710 p ≤ (0 : Int) + d4481 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d4476, d710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5673 p hg
    simpa only [d4476, d710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4476, d710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5674 p hg
    simpa only [d4476, d710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5676 (p : Pattern) (guard : d0 p = 1) : d31 p ≤ (0 : Int) + d31 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5677 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d31 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5678 (p : Pattern) (guard : d4474 p = 1) : d32 p ≤ (0 : Int) + d31 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2017 p hg
    simpa only [d4474, d32, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5677 p hg
    simpa only [d4474, d32, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5679 (p : Pattern) (guard : d4475 p = 1) : d53 p ≤ (0 : Int) + d31 p := by
  cases selected : p 182 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4475, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5676 p hg
    simpa only [d4475, d53, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d4475, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5678 p hg
    simpa only [d4475, d53, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5680 (p : Pattern) (guard : d4475 p = 1) : d54 p ≤ (0 : Int) + d4482 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d54, d4482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5659 p hg
    simpa only [d54, d4482, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d54, d4482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5679 p hg
    simpa only [d54, d4482, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5681 (p : Pattern) (guard : d4475 p = 1) : d55 p ≤ (0 : Int) + d4483 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d55, d4483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5663 p hg
    simpa only [d55, d4483, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d55, d4483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5669 p hg
    simpa only [d55, d4483, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5682 (p : Pattern) (guard : d4475 p = 1) : d56 p ≤ (0 : Int) + d4484 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d56, d4484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5680 p hg
    simpa only [d56, d4484, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d56, d4484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5681 p hg
    simpa only [d56, d4484, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5683 (p : Pattern) (guard : d0 p = 1) : d58 p ≤ (0 : Int) + d58 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5684 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d58 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5685 (p : Pattern) (guard : d4474 p = 1) : d59 p ≤ (0 : Int) + d58 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2022 p hg
    simpa only [d4474, d59, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5684 p hg
    simpa only [d4474, d59, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5686 (p : Pattern) (guard : d4475 p = 1) : d60 p ≤ (0 : Int) + d58 p := by
  cases selected : p 182 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4475, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5683 p hg
    simpa only [d4475, d60, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d4475, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5685 p hg
    simpa only [d4475, d60, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5687 (p : Pattern) (guard : d4475 p = 1) : d61 p ≤ (0 : Int) + d4485 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d61, d4485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5663 p hg
    simpa only [d61, d4485, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d61, d4485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5686 p hg
    simpa only [d61, d4485, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5688 (p : Pattern) (guard : d0 p = 1) : d40 p ≤ (0 : Int) + d40 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5689 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d40 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5690 (p : Pattern) (guard : d4474 p = 1) : d41 p ≤ (0 : Int) + d40 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2025 p hg
    simpa only [d4474, d41, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5689 p hg
    simpa only [d4474, d41, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5691 (p : Pattern) (guard : d4475 p = 1) : d62 p ≤ (0 : Int) + d40 p := by
  cases selected : p 182 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4475, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5688 p hg
    simpa only [d4475, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d4475, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5690 p hg
    simpa only [d4475, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5692 (p : Pattern) (guard : d4475 p = 1) : d63 p ≤ (0 : Int) + d4486 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d63, d4486, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5691 p hg
    simpa only [d63, d4486, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d63, d4486, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5670 p hg
    simpa only [d63, d4486, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5693 (p : Pattern) (guard : d4475 p = 1) : d64 p ≤ (0 : Int) + d4487 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d64, d4487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5687 p hg
    simpa only [d64, d4487, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d64, d4487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5692 p hg
    simpa only [d64, d4487, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5694 (p : Pattern) (guard : d4475 p = 1) : d65 p ≤ (0 : Int) + d4488 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d65, d4488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5682 p hg
    simpa only [d65, d4488, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d65, d4488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5693 p hg
    simpa only [d65, d4488, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5695 (p : Pattern) (guard : d0 p = 1) : d391 p ≤ (0 : Int) + d4488 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5696 (p : Pattern) (guard : d4476 p = 1) : d711 p ≤ (0 : Int) + d4488 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d4476, d711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5694 p hg
    simpa only [d4476, d711, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4476, d711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5695 p hg
    simpa only [d4476, d711, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5697 (p : Pattern) (guard : d4476 p = 1) : d712 p ≤ (0 : Int) + d4489 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4476 p = 1 := by simpa only [d712, d4489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5675 p hg
    simpa only [d712, d4489, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4476 p = 1 := by simpa only [d712, d4489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5696 p hg
    simpa only [d712, d4489, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5698 (p : Pattern) (guard : d0 p = 1) : d396 p ≤ (0 : Int) + d4492 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5699 (p : Pattern) (guard : d4476 p = 1) : d713 p ≤ (0 : Int) + d4493 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d4476, d713, d4493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5673 p hg
    simpa only [d4476, d713, d4493, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4476, d713, d4493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5698 p hg
    simpa only [d4476, d713, d4493, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5700 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d4496 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5701 (p : Pattern) (guard : d4476 p = 1) : d714 p ≤ (0 : Int) + d4497 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d4476, d714, d4497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5694 p hg
    simpa only [d4476, d714, d4497, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4476, d714, d4497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5700 p hg
    simpa only [d4476, d714, d4497, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5702 (p : Pattern) (guard : d4476 p = 1) : d715 p ≤ (0 : Int) + d4498 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4476 p = 1 := by simpa only [d715, d4498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5699 p hg
    simpa only [d715, d4498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4476 p = 1 := by simpa only [d715, d4498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5701 p hg
    simpa only [d715, d4498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5703 (p : Pattern) (guard : d4476 p = 1) : d716 p ≤ (0 : Int) + d4499 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4476 p = 1 := by simpa only [d716, d4499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5697 p hg
    simpa only [d716, d4499, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4476 p = 1 := by simpa only [d716, d4499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5702 p hg
    simpa only [d716, d4499, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5704 (p : Pattern) (guard : d0 p = 1) : d405 p ≤ (0 : Int) + d4492 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5705 (p : Pattern) (guard : d4476 p = 1) : d717 p ≤ (0 : Int) + d4493 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d4476, d717, d4493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5673 p hg
    simpa only [d4476, d717, d4493, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4476, d717, d4493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5704 p hg
    simpa only [d4476, d717, d4493, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5706 (p : Pattern) (guard : d4476 p = 1) : d718 p ≤ (0 : Int) + d4498 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4476 p = 1 := by simpa only [d718, d4498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5705 p hg
    simpa only [d718, d4498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4476 p = 1 := by simpa only [d718, d4498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5701 p hg
    simpa only [d718, d4498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5707 (p : Pattern) (guard : d4475 p = 1) : d89 p ≤ (0 : Int) + d4500 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d89, d4500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5669 p hg
    simpa only [d89, d4500, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d89, d4500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5691 p hg
    simpa only [d89, d4500, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5708 (p : Pattern) (guard : d4475 p = 1) : d90 p ≤ (0 : Int) + d4501 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d90, d4501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5707 p hg
    simpa only [d90, d4501, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d90, d4501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5692 p hg
    simpa only [d90, d4501, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5709 (p : Pattern) (guard : d4475 p = 1) : d91 p ≤ (0 : Int) + d4502 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d91, d4502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5692 p hg
    simpa only [d91, d4502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d91, d4502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5670 p hg
    simpa only [d91, d4502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5710 (p : Pattern) (guard : d4475 p = 1) : d92 p ≤ (0 : Int) + d4503 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d92, d4503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5708 p hg
    simpa only [d92, d4503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d92, d4503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5709 p hg
    simpa only [d92, d4503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5711 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d4504 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5712 (p : Pattern) (guard : d4476 p = 1) : d719 p ≤ (0 : Int) + d4505 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d4476, d719, d4505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5710 p hg
    simpa only [d4476, d719, d4505, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4476, d719, d4505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5711 p hg
    simpa only [d4476, d719, d4505, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5713 (p : Pattern) (guard : d4475 p = 1) : d93 p ≤ (0 : Int) + d4504 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d93, d4504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5709 p hg
    simpa only [d93, d4504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d93, d4504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5670 p hg
    simpa only [d93, d4504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5714 (p : Pattern) (guard : d4476 p = 1) : d95 p ≤ (0 : Int) + d4506 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d4476, d95, d4506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5713 p hg
    simpa only [d4476, d95, d4506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4476, d95, d4506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4476, d95, d4506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5715 (p : Pattern) (guard : d4476 p = 1) : d720 p ≤ (0 : Int) + d4507 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4476 p = 1 := by simpa only [d720, d4507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5712 p hg
    simpa only [d720, d4507, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4476 p = 1 := by simpa only [d720, d4507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5714 p hg
    simpa only [d720, d4507, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5716 (p : Pattern) (guard : d4476 p = 1) : d721 p ≤ (0 : Int) + d4508 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4476 p = 1 := by simpa only [d721, d4508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5706 p hg
    simpa only [d721, d4508, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4476 p = 1 := by simpa only [d721, d4508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5715 p hg
    simpa only [d721, d4508, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5717 (p : Pattern) (guard : d4476 p = 1) : d722 p ≤ (0 : Int) + d4509 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4476 p = 1 := by simpa only [d722, d4509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5703 p hg
    simpa only [d722, d4509, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4476 p = 1 := by simpa only [d722, d4509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5716 p hg
    simpa only [d722, d4509, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5718 (p : Pattern) (guard : d0 p = 1) : d409 p ≤ (0 : Int) + d4481 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5719 (p : Pattern) (guard : d4476 p = 1) : d723 p ≤ (0 : Int) + d4481 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d4476, d723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5673 p hg
    simpa only [d4476, d723, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4476, d723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5718 p hg
    simpa only [d4476, d723, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5720 (p : Pattern) (guard : d0 p = 1) : d396 p ≤ (0 : Int) + d4488 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5721 (p : Pattern) (guard : d4476 p = 1) : d724 p ≤ (0 : Int) + d4488 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d4476, d724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5694 p hg
    simpa only [d4476, d724, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4476, d724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5720 p hg
    simpa only [d4476, d724, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5722 (p : Pattern) (guard : d4476 p = 1) : d725 p ≤ (0 : Int) + d4489 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4476 p = 1 := by simpa only [d725, d4489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5719 p hg
    simpa only [d725, d4489, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4476 p = 1 := by simpa only [d725, d4489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5721 p hg
    simpa only [d725, d4489, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5723 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d4492 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5724 (p : Pattern) (guard : d4476 p = 1) : d726 p ≤ (0 : Int) + d4493 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d4476, d726, d4493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5673 p hg
    simpa only [d4476, d726, d4493, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4476, d726, d4493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5723 p hg
    simpa only [d4476, d726, d4493, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5725 (p : Pattern) (guard : d4476 p = 1) : d727 p ≤ (0 : Int) + d4498 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4476 p = 1 := by simpa only [d727, d4498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5724 p hg
    simpa only [d727, d4498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4476 p = 1 := by simpa only [d727, d4498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5701 p hg
    simpa only [d727, d4498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5726 (p : Pattern) (guard : d4476 p = 1) : d728 p ≤ (0 : Int) + d4499 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4476 p = 1 := by simpa only [d728, d4499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5722 p hg
    simpa only [d728, d4499, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4476 p = 1 := by simpa only [d728, d4499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5725 p hg
    simpa only [d728, d4499, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5727 (p : Pattern) (guard : d4476 p = 1) : d12 p ≤ (0 : Int) + d12 p := by
  omega
theorem compare5728 (p : Pattern) (guard : d4476 p = 1) : d729 p ≤ (0 : Int) + d4510 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4476 p = 1 := by simpa only [d729, d4510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5725 p hg
    simpa only [d729, d4510, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4476 p = 1 := by simpa only [d729, d4510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5727 p hg
    simpa only [d729, d4510, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5729 (p : Pattern) (guard : d4476 p = 1) : d730 p ≤ (0 : Int) + d4511 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4476 p = 1 := by simpa only [d730, d4511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5726 p hg
    simpa only [d730, d4511, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4476 p = 1 := by simpa only [d730, d4511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5728 p hg
    simpa only [d730, d4511, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5730 (p : Pattern) (guard : d4476 p = 1) : d731 p ≤ (0 : Int) + d4512 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4476 p = 1 := by simpa only [d731, d4512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5717 p hg
    simpa only [d731, d4512, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4476 p = 1 := by simpa only [d731, d4512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5729 p hg
    simpa only [d731, d4512, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5731 (p : Pattern) (guard : d0 p = 1) : d398 p ≤ (0 : Int) + d4481 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5732 (p : Pattern) (guard : d4476 p = 1) : d732 p ≤ (0 : Int) + d4481 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d4476, d732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5673 p hg
    simpa only [d4476, d732, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4476, d732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5731 p hg
    simpa only [d4476, d732, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5733 (p : Pattern) (guard : d0 p = 1) : d409 p ≤ (0 : Int) + d4488 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5734 (p : Pattern) (guard : d4476 p = 1) : d733 p ≤ (0 : Int) + d4488 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d4476, d733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5694 p hg
    simpa only [d4476, d733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4476, d733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5733 p hg
    simpa only [d4476, d733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5735 (p : Pattern) (guard : d4476 p = 1) : d734 p ≤ (0 : Int) + d4489 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4476 p = 1 := by simpa only [d734, d4489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5732 p hg
    simpa only [d734, d4489, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4476 p = 1 := by simpa only [d734, d4489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5734 p hg
    simpa only [d734, d4489, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5736 (p : Pattern) (guard : d4476 p = 1) : d735 p ≤ (0 : Int) + d4499 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4476 p = 1 := by simpa only [d735, d4499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5735 p hg
    simpa only [d735, d4499, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4476 p = 1 := by simpa only [d735, d4499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5725 p hg
    simpa only [d735, d4499, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5737 (p : Pattern) (guard : d4476 p = 1) : d736 p ≤ (0 : Int) + d4508 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4476 p = 1 := by simpa only [d736, d4508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5702 p hg
    simpa only [d736, d4508, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4476 p = 1 := by simpa only [d736, d4508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5715 p hg
    simpa only [d736, d4508, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5738 (p : Pattern) (guard : d4476 p = 1) : d737 p ≤ (0 : Int) + d4509 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4476 p = 1 := by simpa only [d737, d4509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5736 p hg
    simpa only [d737, d4509, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4476 p = 1 := by simpa only [d737, d4509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5737 p hg
    simpa only [d737, d4509, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5739 (p : Pattern) (guard : d0 p = 1) : d405 p ≤ (0 : Int) + d4481 p := by
  change (0 : Int) = 1 at guard
  omega
end NetHack.Sokoban22Refined85
