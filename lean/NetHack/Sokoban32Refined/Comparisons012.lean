/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Comparisons011
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare1680 (p : Pattern) (guard : d1092 p = 1) : d187 p ≤ (0 : Int) + d510 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1661 p hg
    simpa only [d510, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1654 p hg
    simpa only [d510, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1681 (p : Pattern) (guard : d1092 p = 1) : d189 p ≤ (0 : Int) + d470 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d189, d470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1654 p hg
    simpa only [d189, d470, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d189, d470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1658 p hg
    simpa only [d189, d470, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1682 (p : Pattern) (guard : d1092 p = 1) : d190 p ≤ (0 : Int) + d511 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d190, d511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1680 p hg
    simpa only [d190, d511, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d190, d511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1681 p hg
    simpa only [d190, d511, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1683 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d68 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1684 (p : Pattern) (guard : d1092 p = 1) : d199 p ≤ (0 : Int) + d68 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1092, d199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1633 p hg
    simpa only [d1092, d199, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1683 p hg
    simpa only [d1092, d199, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1685 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d70 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1686 (p : Pattern) (guard : d1092 p = 1) : d200 p ≤ (0 : Int) + d70 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1092, d200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1636 p hg
    simpa only [d1092, d200, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1685 p hg
    simpa only [d1092, d200, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1687 (p : Pattern) (guard : d1092 p = 1) : d201 p ≤ (0 : Int) + d75 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d201, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1684 p hg
    simpa only [d201, d75, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d201, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1686 p hg
    simpa only [d201, d75, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1688 (p : Pattern) (guard : d1092 p = 1) : d202 p ≤ (0 : Int) + d491 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d202, d491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1681 p hg
    simpa only [d202, d491, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d202, d491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1687 p hg
    simpa only [d202, d491, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1689 (p : Pattern) (guard : d1092 p = 1) : d203 p ≤ (0 : Int) + d512 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d203, d512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1682 p hg
    simpa only [d203, d512, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d203, d512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1688 p hg
    simpa only [d203, d512, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1690 (p : Pattern) (guard : d1093 p = 1) : d204 p ≤ (0 : Int) + d513 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1093, d204, d513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1679 p hg
    simpa only [d1093, d204, d513, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d1093, d204, d513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1689 p hg
    simpa only [d1093, d204, d513, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1691 (p : Pattern) (guard : d0 p = 1) : d164 p ≤ (0 : Int) + d515 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1692 (p : Pattern) (guard : d1094 p = 1) : d205 p ≤ (0 : Int) + d516 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1093 p = 1 := by simpa only [d1094, d205, d516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1690 p hg
    simpa only [d1094, d205, d516, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1094, d205, d516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1691 p hg
    simpa only [d1094, d205, d516, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1693 (p : Pattern) (guard : d1094 p = 1) : d206 p ≤ (0 : Int) + d517 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1094 p = 1 := by simpa only [d206, d517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1674 p hg
    simpa only [d206, d517, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1094 p = 1 := by simpa only [d206, d517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1692 p hg
    simpa only [d206, d517, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1694 (p : Pattern) (guard : d1094 p = 1) : d207 p ≤ (0 : Int) + d518 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1094 p = 1 := by simpa only [d207, d518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1651 p hg
    simpa only [d207, d518, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1094 p = 1 := by simpa only [d207, d518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1693 p hg
    simpa only [d207, d518, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1695 (p : Pattern) (guard : d1092 p = 1) : d36 p ≤ (0 : Int) + d496 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d36, d496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1643 p hg
    simpa only [d36, d496, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d36, d496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1620 p hg
    simpa only [d36, d496, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1696 (p : Pattern) (guard : d1092 p = 1) : d42 p ≤ (0 : Int) + d61 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1092, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1666 p hg
    simpa only [d1092, d42, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1622 p hg
    simpa only [d1092, d42, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1697 (p : Pattern) (guard : d1092 p = 1) : d43 p ≤ (0 : Int) + d473 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d43, d473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1696 p hg
    simpa only [d43, d473, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d43, d473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1616 p hg
    simpa only [d43, d473, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1698 (p : Pattern) (guard : d1092 p = 1) : d44 p ≤ (0 : Int) + d497 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d44, d497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1695 p hg
    simpa only [d44, d497, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d44, d497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1697 p hg
    simpa only [d44, d497, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1699 (p : Pattern) (guard : d1092 p = 1) : d45 p ≤ (0 : Int) + d498 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d45, d498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1618 p hg
    simpa only [d45, d498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d45, d498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1698 p hg
    simpa only [d45, d498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1700 (p : Pattern) (guard : d1093 p = 1) : d45 p ≤ (0 : Int) + d499 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1093, d499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1609 p hg
    simpa only [d1093, d499, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d1093, d499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1699 p hg
    simpa only [d1093, d499, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1701 (p : Pattern) (guard : d0 p = 1) : d155 p ≤ (0 : Int) + d522 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1702 (p : Pattern) (guard : d1094 p = 1) : d208 p ≤ (0 : Int) + d523 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1093 p = 1 := by simpa only [d1094, d208, d523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1700 p hg
    simpa only [d1094, d208, d523, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1094, d208, d523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1701 p hg
    simpa only [d1094, d208, d523, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1703 (p : Pattern) (guard : d1092 p = 1) : d16 p ≤ (0 : Int) + d510 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1643 p hg
    simpa only [d510, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1612 p hg
    simpa only [d510, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1704 (p : Pattern) (guard : d1092 p = 1) : d27 p ≤ (0 : Int) + d470 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d27, d470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1612 p hg
    simpa only [d27, d470, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d27, d470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1616 p hg
    simpa only [d27, d470, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1705 (p : Pattern) (guard : d1092 p = 1) : d28 p ≤ (0 : Int) + d511 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d28, d511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1703 p hg
    simpa only [d28, d511, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d28, d511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1704 p hg
    simpa only [d28, d511, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1706 (p : Pattern) (guard : d1092 p = 1) : d76 p ≤ (0 : Int) + d491 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d76, d491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1704 p hg
    simpa only [d76, d491, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d76, d491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1645 p hg
    simpa only [d76, d491, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1707 (p : Pattern) (guard : d1092 p = 1) : d77 p ≤ (0 : Int) + d512 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d77, d512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1705 p hg
    simpa only [d77, d512, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d77, d512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1706 p hg
    simpa only [d77, d512, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1708 (p : Pattern) (guard : d1093 p = 1) : d77 p ≤ (0 : Int) + d513 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1093, d513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1679 p hg
    simpa only [d1093, d513, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d1093, d513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1707 p hg
    simpa only [d1093, d513, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1709 (p : Pattern) (guard : d0 p = 1) : d164 p ≤ (0 : Int) + d526 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1710 (p : Pattern) (guard : d1094 p = 1) : d209 p ≤ (0 : Int) + d527 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1093 p = 1 := by simpa only [d1094, d209, d527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1708 p hg
    simpa only [d1094, d209, d527, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1094, d209, d527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1709 p hg
    simpa only [d1094, d209, d527, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1711 (p : Pattern) (guard : d1094 p = 1) : d210 p ≤ (0 : Int) + d528 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1094 p = 1 := by simpa only [d210, d528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1702 p hg
    simpa only [d210, d528, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1094 p = 1 := by simpa only [d210, d528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1710 p hg
    simpa only [d210, d528, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1712 (p : Pattern) (guard : d1088 p = 1) : d36 p ≤ (0 : Int) + d496 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d36, d496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1675 p hg
    simpa only [d36, d496, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d36, d496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1600 p hg
    simpa only [d36, d496, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1713 (p : Pattern) (guard : d1088 p = 1) : d42 p ≤ (0 : Int) + d61 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1666 p hg
    simpa only [d42, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1605 p hg
    simpa only [d42, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1714 (p : Pattern) (guard : d1088 p = 1) : d43 p ≤ (0 : Int) + d473 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d43, d473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1713 p hg
    simpa only [d43, d473, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d43, d473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1594 p hg
    simpa only [d43, d473, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1715 (p : Pattern) (guard : d1088 p = 1) : d44 p ≤ (0 : Int) + d497 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d44, d497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1712 p hg
    simpa only [d44, d497, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d44, d497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1714 p hg
    simpa only [d44, d497, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1716 (p : Pattern) (guard : d1088 p = 1) : d45 p ≤ (0 : Int) + d498 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d45, d498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1596 p hg
    simpa only [d45, d498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d45, d498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1715 p hg
    simpa only [d45, d498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1717 (p : Pattern) (guard : d1088 p = 1) : d119 p ≤ (0 : Int) + d58 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1088, d119, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare221 p hg
    simpa only [d1088, d119, d58, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1088, d119, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1590 p hg
    simpa only [d1088, d119, d58, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1718 (p : Pattern) (guard : d1092 p = 1) : d211 p ≤ (0 : Int) + d58 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1092, d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1717 p hg
    simpa only [d1092, d211, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1662 p hg
    simpa only [d1092, d211, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1719 (p : Pattern) (guard : d1092 p = 1) : d212 p ≤ (0 : Int) + d519 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d212, d519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1654 p hg
    simpa only [d212, d519, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d212, d519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1718 p hg
    simpa only [d212, d519, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1720 (p : Pattern) (guard : d1092 p = 1) : d213 p ≤ (0 : Int) + d520 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d213, d520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1719 p hg
    simpa only [d213, d520, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d213, d520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1669 p hg
    simpa only [d213, d520, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1721 (p : Pattern) (guard : d1092 p = 1) : d214 p ≤ (0 : Int) + d529 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d214, d529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1682 p hg
    simpa only [d214, d529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d214, d529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1720 p hg
    simpa only [d214, d529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1722 (p : Pattern) (guard : d1093 p = 1) : d215 p ≤ (0 : Int) + d530 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1093, d215, d530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1716 p hg
    simpa only [d1093, d215, d530, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d1093, d215, d530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1721 p hg
    simpa only [d1093, d215, d530, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1723 (p : Pattern) (guard : d0 p = 1) : d164 p ≤ (0 : Int) + d531 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1724 (p : Pattern) (guard : d1094 p = 1) : d216 p ≤ (0 : Int) + d532 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1093 p = 1 := by simpa only [d1094, d216, d532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1722 p hg
    simpa only [d1094, d216, d532, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1094, d216, d532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1723 p hg
    simpa only [d1094, d216, d532, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1725 (p : Pattern) (guard : d1088 p = 1) : d16 p ≤ (0 : Int) + d510 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1675 p hg
    simpa only [d510, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1585 p hg
    simpa only [d510, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1726 (p : Pattern) (guard : d1088 p = 1) : d27 p ≤ (0 : Int) + d470 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d27, d470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1585 p hg
    simpa only [d27, d470, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d27, d470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1594 p hg
    simpa only [d27, d470, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1727 (p : Pattern) (guard : d1088 p = 1) : d28 p ≤ (0 : Int) + d511 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d28, d511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1725 p hg
    simpa only [d28, d511, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d28, d511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1726 p hg
    simpa only [d28, d511, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1728 (p : Pattern) (guard : d1088 p = 1) : d76 p ≤ (0 : Int) + d491 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d76, d491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1726 p hg
    simpa only [d76, d491, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d76, d491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1677 p hg
    simpa only [d76, d491, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1729 (p : Pattern) (guard : d1088 p = 1) : d77 p ≤ (0 : Int) + d512 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d77, d512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1727 p hg
    simpa only [d77, d512, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d77, d512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1728 p hg
    simpa only [d77, d512, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1730 (p : Pattern) (guard : d1092 p = 1) : d217 p ≤ (0 : Int) + d52 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1092, d217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1581 p hg
    simpa only [d1092, d217, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1652 p hg
    simpa only [d1092, d217, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1731 (p : Pattern) (guard : d1092 p = 1) : d218 p ≤ (0 : Int) + d54 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1092, d218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1593 p hg
    simpa only [d1092, d218, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1657 p hg
    simpa only [d1092, d218, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1732 (p : Pattern) (guard : d1092 p = 1) : d219 p ≤ (0 : Int) + d470 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d219, d470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1730 p hg
    simpa only [d219, d470, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d219, d470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1731 p hg
    simpa only [d219, d470, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1733 (p : Pattern) (guard : d1092 p = 1) : d220 p ≤ (0 : Int) + d524 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d220, d524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1730 p hg
    simpa only [d220, d524, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d220, d524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1732 p hg
    simpa only [d220, d524, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1734 (p : Pattern) (guard : d1092 p = 1) : d221 p ≤ (0 : Int) + d491 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d221, d491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1732 p hg
    simpa only [d221, d491, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d221, d491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1687 p hg
    simpa only [d221, d491, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1735 (p : Pattern) (guard : d1092 p = 1) : d222 p ≤ (0 : Int) + d525 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d222, d525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1733 p hg
    simpa only [d222, d525, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d222, d525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1734 p hg
    simpa only [d222, d525, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1736 (p : Pattern) (guard : d1093 p = 1) : d223 p ≤ (0 : Int) + d533 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1093, d223, d533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1729 p hg
    simpa only [d1093, d223, d533, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d1093, d223, d533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1735 p hg
    simpa only [d1093, d223, d533, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1737 (p : Pattern) (guard : d1094 p = 1) : d224 p ≤ (0 : Int) + d534 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1093 p = 1 := by simpa only [d1094, d224, d534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1736 p hg
    simpa only [d1094, d224, d534, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1094, d224, d534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1540 p hg
    simpa only [d1094, d224, d534, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1738 (p : Pattern) (guard : d1094 p = 1) : d225 p ≤ (0 : Int) + d535 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1094 p = 1 := by simpa only [d225, d535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d225, d535, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1094 p = 1 := by simpa only [d225, d535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1737 p hg
    simpa only [d225, d535, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1739 (p : Pattern) (guard : d1094 p = 1) : d226 p ≤ (0 : Int) + d536 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1094 p = 1 := by simpa only [d226, d536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1711 p hg
    simpa only [d226, d536, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1094 p = 1 := by simpa only [d226, d536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1738 p hg
    simpa only [d226, d536, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1740 (p : Pattern) (guard : d1094 p = 1) : d227 p ≤ (0 : Int) + d537 p := by
  cases selected : p 80 with
  | false =>
    have hg : d1094 p = 1 := by simpa only [d227, d537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1694 p hg
    simpa only [d227, d537, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1094 p = 1 := by simpa only [d227, d537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1739 p hg
    simpa only [d227, d537, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1741 (p : Pattern) (guard : d857 p = 1) : d45 p ≤ (0 : Int) + d45 p := by
  omega
theorem compare1742 (p : Pattern) (guard : d1072 p = 1) : d184 p ≤ (0 : Int) + d67 p := by
  cases selected : p 112 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d1072, d184, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1741 p hg
    simpa only [d1072, d184, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1072, d184, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1349 p hg
    simpa only [d1072, d184, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1743 (p : Pattern) (guard : d857 p = 1) : d78 p ≤ (0 : Int) + d78 p := by
  omega
theorem compare1744 (p : Pattern) (guard : d1072 p = 1) : d185 p ≤ (0 : Int) + d84 p := by
  cases selected : p 112 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d1072, d185, d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1743 p hg
    simpa only [d1072, d185, d84, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1072, d185, d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1351 p hg
    simpa only [d1072, d185, d84, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1745 (p : Pattern) (guard : d1072 p = 1) : d186 p ≤ (0 : Int) + d85 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1072 p = 1 := by simpa only [d186, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1742 p hg
    simpa only [d186, d85, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1072 p = 1 := by simpa only [d186, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1744 p hg
    simpa only [d186, d85, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1746 (p : Pattern) (guard : d857 p = 1) : d187 p ≤ (0 : Int) + d86 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d857, d187, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare199 p hg
    simpa only [d857, d187, d86, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d857, d187, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1652 p hg
    simpa only [d857, d187, d86, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1747 (p : Pattern) (guard : d857 p = 1) : d188 p ≤ (0 : Int) + d87 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d857, d188, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare211 p hg
    simpa only [d857, d188, d87, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d857, d188, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1657 p hg
    simpa only [d857, d188, d87, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1748 (p : Pattern) (guard : d857 p = 1) : d189 p ≤ (0 : Int) + d88 p := by
  cases selected : p 134 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d189, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1746 p hg
    simpa only [d189, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d189, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1747 p hg
    simpa only [d189, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1749 (p : Pattern) (guard : d857 p = 1) : d190 p ≤ (0 : Int) + d89 p := by
  cases selected : p 133 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d190, d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1746 p hg
    simpa only [d190, d89, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d190, d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1748 p hg
    simpa only [d190, d89, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1750 (p : Pattern) (guard : d857 p = 1) : d191 p ≤ (0 : Int) + d90 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d857, d191, d90, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare221 p hg
    simpa only [d857, d191, d90, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d857, d191, d90, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1662 p hg
    simpa only [d857, d191, d90, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1751 (p : Pattern) (guard : d857 p = 1) : d192 p ≤ (0 : Int) + d91 p := by
  cases selected : p 134 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d192, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1746 p hg
    simpa only [d192, d91, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d192, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1750 p hg
    simpa only [d192, d91, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1752 (p : Pattern) (guard : d857 p = 1) : d193 p ≤ (0 : Int) + d92 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d857, d193, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare232 p hg
    simpa only [d857, d193, d92, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d857, d193, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1667 p hg
    simpa only [d857, d193, d92, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1753 (p : Pattern) (guard : d857 p = 1) : d194 p ≤ (0 : Int) + d93 p := by
  cases selected : p 134 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d194, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1752 p hg
    simpa only [d194, d93, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d194, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1747 p hg
    simpa only [d194, d93, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1754 (p : Pattern) (guard : d857 p = 1) : d195 p ≤ (0 : Int) + d94 p := by
  cases selected : p 133 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d195, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1751 p hg
    simpa only [d195, d94, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d195, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1753 p hg
    simpa only [d195, d94, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1755 (p : Pattern) (guard : d857 p = 1) : d196 p ≤ (0 : Int) + d95 p := by
  cases selected : p 132 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d196, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1749 p hg
    simpa only [d196, d95, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d196, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1754 p hg
    simpa only [d196, d95, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1756 (p : Pattern) (guard : d857 p = 1) : d197 p ≤ (0 : Int) + d96 p := by
  cases selected : p 113 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d197, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1741 p hg
    simpa only [d197, d96, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d197, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1755 p hg
    simpa only [d197, d96, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1757 (p : Pattern) (guard : d0 p = 1) : d155 p ≤ (0 : Int) + d102 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1758 (p : Pattern) (guard : d1072 p = 1) : d198 p ≤ (0 : Int) + d103 p := by
  cases selected : p 112 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d1072, d198, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1756 p hg
    simpa only [d1072, d198, d103, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1072, d198, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1757 p hg
    simpa only [d1072, d198, d103, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1759 (p : Pattern) (guard : d857 p = 1) : d77 p ≤ (0 : Int) + d77 p := by
  omega
theorem compare1760 (p : Pattern) (guard : d857 p = 1) : d199 p ≤ (0 : Int) + d68 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d857, d199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare881 p hg
    simpa only [d857, d199, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d857, d199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1683 p hg
    simpa only [d857, d199, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1761 (p : Pattern) (guard : d857 p = 1) : d200 p ≤ (0 : Int) + d70 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d857, d200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1459 p hg
    simpa only [d857, d200, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d857, d200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1685 p hg
    simpa only [d857, d200, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1762 (p : Pattern) (guard : d857 p = 1) : d201 p ≤ (0 : Int) + d75 p := by
  cases selected : p 134 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d201, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1760 p hg
    simpa only [d201, d75, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d201, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1761 p hg
    simpa only [d201, d75, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1763 (p : Pattern) (guard : d857 p = 1) : d202 p ≤ (0 : Int) + d104 p := by
  cases selected : p 133 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d202, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1748 p hg
    simpa only [d202, d104, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d202, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1762 p hg
    simpa only [d202, d104, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1764 (p : Pattern) (guard : d857 p = 1) : d203 p ≤ (0 : Int) + d105 p := by
  cases selected : p 132 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d203, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1749 p hg
    simpa only [d203, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d203, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1763 p hg
    simpa only [d203, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1765 (p : Pattern) (guard : d857 p = 1) : d204 p ≤ (0 : Int) + d106 p := by
  cases selected : p 113 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d204, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1759 p hg
    simpa only [d204, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d204, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1764 p hg
    simpa only [d204, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1766 (p : Pattern) (guard : d0 p = 1) : d164 p ≤ (0 : Int) + d113 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1767 (p : Pattern) (guard : d1072 p = 1) : d205 p ≤ (0 : Int) + d114 p := by
  cases selected : p 112 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d1072, d205, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1765 p hg
    simpa only [d1072, d205, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1072, d205, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1766 p hg
    simpa only [d1072, d205, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1768 (p : Pattern) (guard : d1072 p = 1) : d206 p ≤ (0 : Int) + d115 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1072 p = 1 := by simpa only [d206, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1758 p hg
    simpa only [d206, d115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1072 p = 1 := by simpa only [d206, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1767 p hg
    simpa only [d206, d115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1769 (p : Pattern) (guard : d1072 p = 1) : d207 p ≤ (0 : Int) + d116 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1072 p = 1 := by simpa only [d207, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1745 p hg
    simpa only [d207, d116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1072 p = 1 := by simpa only [d207, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1768 p hg
    simpa only [d207, d116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1770 (p : Pattern) (guard : d1072 p = 1) : d208 p ≤ (0 : Int) + d67 p := by
  cases selected : p 112 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d1072, d208, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1741 p hg
    simpa only [d1072, d208, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1072, d208, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1356 p hg
    simpa only [d1072, d208, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1771 (p : Pattern) (guard : d1072 p = 1) : d209 p ≤ (0 : Int) + d117 p := by
  cases selected : p 112 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d1072, d209, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1759 p hg
    simpa only [d1072, d209, d117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1072, d209, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1358 p hg
    simpa only [d1072, d209, d117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1772 (p : Pattern) (guard : d1072 p = 1) : d210 p ≤ (0 : Int) + d118 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1072 p = 1 := by simpa only [d210, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1770 p hg
    simpa only [d210, d118, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1072 p = 1 := by simpa only [d210, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1771 p hg
    simpa only [d210, d118, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1773 (p : Pattern) (guard : d857 p = 1) : d211 p ≤ (0 : Int) + d120 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d857, d211, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1494 p hg
    simpa only [d857, d211, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d857, d211, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1662 p hg
    simpa only [d857, d211, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1774 (p : Pattern) (guard : d857 p = 1) : d212 p ≤ (0 : Int) + d121 p := by
  cases selected : p 134 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d212, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1746 p hg
    simpa only [d212, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d212, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1773 p hg
    simpa only [d212, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1775 (p : Pattern) (guard : d857 p = 1) : d213 p ≤ (0 : Int) + d122 p := by
  cases selected : p 133 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d213, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1774 p hg
    simpa only [d213, d122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d213, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1753 p hg
    simpa only [d213, d122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1776 (p : Pattern) (guard : d857 p = 1) : d214 p ≤ (0 : Int) + d123 p := by
  cases selected : p 132 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d214, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1749 p hg
    simpa only [d214, d123, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d214, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1775 p hg
    simpa only [d214, d123, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1777 (p : Pattern) (guard : d857 p = 1) : d215 p ≤ (0 : Int) + d124 p := by
  cases selected : p 113 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d215, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1741 p hg
    simpa only [d215, d124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d215, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1776 p hg
    simpa only [d215, d124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1778 (p : Pattern) (guard : d0 p = 1) : d164 p ≤ (0 : Int) + d127 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1779 (p : Pattern) (guard : d1072 p = 1) : d216 p ≤ (0 : Int) + d128 p := by
  cases selected : p 112 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d1072, d216, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1777 p hg
    simpa only [d1072, d216, d128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1072, d216, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1778 p hg
    simpa only [d1072, d216, d128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1780 (p : Pattern) (guard : d857 p = 1) : d217 p ≤ (0 : Int) + d53 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d857, d217, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare209 p hg
    simpa only [d857, d217, d53, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d857, d217, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1652 p hg
    simpa only [d857, d217, d53, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1781 (p : Pattern) (guard : d857 p = 1) : d218 p ≤ (0 : Int) + d55 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d857, d218, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare217 p hg
    simpa only [d857, d218, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d857, d218, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1657 p hg
    simpa only [d857, d218, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1782 (p : Pattern) (guard : d857 p = 1) : d219 p ≤ (0 : Int) + d56 p := by
  cases selected : p 134 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d219, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1780 p hg
    simpa only [d219, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d219, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1781 p hg
    simpa only [d219, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1783 (p : Pattern) (guard : d857 p = 1) : d220 p ≤ (0 : Int) + d57 p := by
  cases selected : p 133 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d220, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1780 p hg
    simpa only [d220, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d220, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1782 p hg
    simpa only [d220, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1784 (p : Pattern) (guard : d857 p = 1) : d221 p ≤ (0 : Int) + d81 p := by
  cases selected : p 133 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d221, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1782 p hg
    simpa only [d221, d81, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d221, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1762 p hg
    simpa only [d221, d81, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1785 (p : Pattern) (guard : d857 p = 1) : d222 p ≤ (0 : Int) + d82 p := by
  cases selected : p 132 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d222, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1783 p hg
    simpa only [d222, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d222, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1784 p hg
    simpa only [d222, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1786 (p : Pattern) (guard : d857 p = 1) : d223 p ≤ (0 : Int) + d129 p := by
  cases selected : p 113 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d223, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1759 p hg
    simpa only [d223, d129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d223, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1785 p hg
    simpa only [d223, d129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1787 (p : Pattern) (guard : d1072 p = 1) : d224 p ≤ (0 : Int) + d131 p := by
  cases selected : p 112 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d1072, d224, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1786 p hg
    simpa only [d1072, d224, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1072, d224, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1540 p hg
    simpa only [d1072, d224, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1788 (p : Pattern) (guard : d1072 p = 1) : d225 p ≤ (0 : Int) + d132 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1072 p = 1 := by simpa only [d225, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1779 p hg
    simpa only [d225, d132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1072 p = 1 := by simpa only [d225, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1787 p hg
    simpa only [d225, d132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1789 (p : Pattern) (guard : d1072 p = 1) : d226 p ≤ (0 : Int) + d133 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1072 p = 1 := by simpa only [d226, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1772 p hg
    simpa only [d226, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1072 p = 1 := by simpa only [d226, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1788 p hg
    simpa only [d226, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1790 (p : Pattern) (guard : d1072 p = 1) : d227 p ≤ (0 : Int) + d134 p := by
  cases selected : p 80 with
  | false =>
    have hg : d1072 p = 1 := by simpa only [d227, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1769 p hg
    simpa only [d227, d134, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1072 p = 1 := by simpa only [d227, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1789 p hg
    simpa only [d227, d134, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1791 (p : Pattern) (guard : d0 p = 1) : d141 p ≤ (0 : Int) + d468 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1792 (p : Pattern) (guard : d1095 p = 1) : d228 p ≤ (0 : Int) + d468 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1095, d228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1609 p hg
    simpa only [d1095, d228, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1095, d228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1791 p hg
    simpa only [d1095, d228, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1793 (p : Pattern) (guard : d0 p = 1) : d14 p ≤ (0 : Int) + d138 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1794 (p : Pattern) (guard : d1088 p = 1) : d15 p ≤ (0 : Int) + d459 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1088, d15, d459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare199 p hg
    simpa only [d1088, d15, d459, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1088, d15, d459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1793 p hg
    simpa only [d1088, d15, d459, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1795 (p : Pattern) (guard : d1088 p = 1) : d15 p ≤ (0 : Int) + d460 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1794 p hg
    simpa only [d460, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1581 p hg
    simpa only [d460, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1796 (p : Pattern) (guard : d1088 p = 1) : d15 p ≤ (0 : Int) + d469 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1795 p hg
    simpa only [d469, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1581 p hg
    simpa only [d469, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1797 (p : Pattern) (guard : d1088 p = 1) : d46 p ≤ (0 : Int) + d470 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d46, d470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1581 p hg
    simpa only [d46, d470, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d46, d470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1593 p hg
    simpa only [d46, d470, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1798 (p : Pattern) (guard : d1088 p = 1) : d47 p ≤ (0 : Int) + d471 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d47, d471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1796 p hg
    simpa only [d47, d471, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d47, d471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1797 p hg
    simpa only [d47, d471, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1799 (p : Pattern) (guard : d1088 p = 1) : d48 p ≤ (0 : Int) + d472 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d48, d472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1795 p hg
    simpa only [d48, d472, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d48, d472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1599 p hg
    simpa only [d48, d472, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1800 (p : Pattern) (guard : d1088 p = 1) : d49 p ≤ (0 : Int) + d473 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d49, d473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1605 p hg
    simpa only [d49, d473, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d49, d473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1593 p hg
    simpa only [d49, d473, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1801 (p : Pattern) (guard : d1088 p = 1) : d50 p ≤ (0 : Int) + d474 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d50, d474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1799 p hg
    simpa only [d50, d474, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d50, d474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1800 p hg
    simpa only [d50, d474, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1802 (p : Pattern) (guard : d1088 p = 1) : d51 p ≤ (0 : Int) + d475 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d51, d475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1798 p hg
    simpa only [d51, d475, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d51, d475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1801 p hg
    simpa only [d51, d475, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1803 (p : Pattern) (guard : d1095 p = 1) : d229 p ≤ (0 : Int) + d475 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1095, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1802 p hg
    simpa only [d1095, d229, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1095, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1628 p hg
    simpa only [d1095, d229, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1804 (p : Pattern) (guard : d1095 p = 1) : d230 p ≤ (0 : Int) + d476 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1095 p = 1 := by simpa only [d230, d476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1792 p hg
    simpa only [d230, d476, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1095 p = 1 := by simpa only [d230, d476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1803 p hg
    simpa only [d230, d476, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1805 (p : Pattern) (guard : d0 p = 1) : d150 p ≤ (0 : Int) + d487 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1806 (p : Pattern) (guard : d1095 p = 1) : d231 p ≤ (0 : Int) + d488 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1095, d231, d488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1640 p hg
    simpa only [d1095, d231, d488, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1095, d231, d488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1805 p hg
    simpa only [d1095, d231, d488, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1807 (p : Pattern) (guard : d1088 p = 1) : d46 p ≤ (0 : Int) + d461 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d46, d461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1795 p hg
    simpa only [d46, d461, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d46, d461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1593 p hg
    simpa only [d46, d461, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1808 (p : Pattern) (guard : d1088 p = 1) : d79 p ≤ (0 : Int) + d489 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d79, d489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1807 p hg
    simpa only [d79, d489, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d79, d489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1677 p hg
    simpa only [d79, d489, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1809 (p : Pattern) (guard : d1088 p = 1) : d80 p ≤ (0 : Int) + d490 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d80, d490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1798 p hg
    simpa only [d80, d490, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d80, d490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1808 p hg
    simpa only [d80, d490, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1810 (p : Pattern) (guard : d0 p = 1) : d154 p ≤ (0 : Int) + d492 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1811 (p : Pattern) (guard : d1095 p = 1) : d232 p ≤ (0 : Int) + d493 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1095, d232, d493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1809 p hg
    simpa only [d1095, d232, d493, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1095, d232, d493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1810 p hg
    simpa only [d1095, d232, d493, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1812 (p : Pattern) (guard : d1095 p = 1) : d233 p ≤ (0 : Int) + d494 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1095 p = 1 := by simpa only [d233, d494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1806 p hg
    simpa only [d233, d494, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1095 p = 1 := by simpa only [d233, d494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1811 p hg
    simpa only [d233, d494, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1813 (p : Pattern) (guard : d1095 p = 1) : d234 p ≤ (0 : Int) + d495 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1095 p = 1 := by simpa only [d234, d495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1804 p hg
    simpa only [d234, d495, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1095 p = 1 := by simpa only [d234, d495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1812 p hg
    simpa only [d234, d495, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1814 (p : Pattern) (guard : d0 p = 1) : d150 p ≤ (0 : Int) + d498 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1815 (p : Pattern) (guard : d1095 p = 1) : d235 p ≤ (0 : Int) + d499 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1095, d235, d499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1609 p hg
    simpa only [d1095, d235, d499, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1095, d235, d499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1814 p hg
    simpa only [d1095, d235, d499, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1816 (p : Pattern) (guard : d1 p = 1) : d14 p ≤ (0 : Int) + d14 p := by
  omega
theorem compare1817 (p : Pattern) (guard : d1088 p = 1) : d14 p ≤ (0 : Int) + d500 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1088, d500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1816 p hg
    simpa only [d1088, d500, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1088, d500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1793 p hg
    simpa only [d1088, d500, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1818 (p : Pattern) (guard : d1088 p = 1) : d97 p ≤ (0 : Int) + d97 p := by
  omega
theorem compare1819 (p : Pattern) (guard : d1088 p = 1) : d98 p ≤ (0 : Int) + d501 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d98, d501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1817 p hg
    simpa only [d98, d501, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d98, d501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1818 p hg
    simpa only [d98, d501, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban32Refined
