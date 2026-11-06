/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban12CostPartition.Comparisons011
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare1680 (p : Pattern) (guard : d1001 p = 1) : d181 p ≤ (0 : Int) + d55 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1000 p = 1 := by simpa only [d1001, d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1679 p hg
    simpa only [d1001, d181, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1001, d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare728 p hg
    simpa only [d1001, d181, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1681 (p : Pattern) (guard : d758 p = 1) : d128 p ≤ (0 : Int) + d65 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d758, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare463 p hg
    simpa only [d758, d128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d758, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare732 p hg
    simpa only [d758, d128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1682 (p : Pattern) (guard : d1000 p = 1) : d129 p ≤ (0 : Int) + d65 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1000, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare480 p hg
    simpa only [d1000, d129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d758 p = 1 := by simpa only [d1000, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1681 p hg
    simpa only [d1000, d129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1683 (p : Pattern) (guard : d1001 p = 1) : d240 p ≤ (0 : Int) + d65 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1000 p = 1 := by simpa only [d1001, d240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1682 p hg
    simpa only [d1001, d240, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1001, d240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare732 p hg
    simpa only [d1001, d240, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1684 (p : Pattern) (guard : d1001 p = 1) : d241 p ≤ (0 : Int) + d66 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1001 p = 1 := by simpa only [d241, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1680 p hg
    simpa only [d241, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1001 p = 1 := by simpa only [d241, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1683 p hg
    simpa only [d241, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1685 (p : Pattern) (guard : d1001 p = 1) : d242 p ≤ (0 : Int) + d1003 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1001 p = 1 := by simpa only [d242, d1003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1677 p hg
    simpa only [d242, d1003, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1001 p = 1 := by simpa only [d242, d1003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1684 p hg
    simpa only [d242, d1003, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1686 (p : Pattern) (guard : d1001 p = 1) : d315 p ≤ (0 : Int) + d1004 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1001 p = 1 := by simpa only [d315, d1004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1674 p hg
    simpa only [d315, d1004, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1001 p = 1 := by simpa only [d315, d1004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1685 p hg
    simpa only [d315, d1004, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1687 (p : Pattern) (guard : d1001 p = 1) : d66 p ≤ (0 : Int) + d66 p := by
  omega
theorem compare1688 (p : Pattern) (guard : d1001 p = 1) : d244 p ≤ (0 : Int) + d1005 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1001 p = 1 := by simpa only [d244, d1005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1685 p hg
    simpa only [d244, d1005, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1001 p = 1 := by simpa only [d244, d1005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1687 p hg
    simpa only [d244, d1005, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1689 (p : Pattern) (guard : d1001 p = 1) : d316 p ≤ (0 : Int) + d1006 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1001 p = 1 := by simpa only [d316, d1006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1686 p hg
    simpa only [d316, d1006, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1001 p = 1 := by simpa only [d316, d1006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1688 p hg
    simpa only [d316, d1006, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1690 (p : Pattern) (guard : d1001 p = 1) : d71 p ≤ (0 : Int) + d1002 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1001 p = 1 := by simpa only [d71, d1002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1666 p hg
    simpa only [d71, d1002, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1001 p = 1 := by simpa only [d71, d1002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1687 p hg
    simpa only [d71, d1002, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1691 (p : Pattern) (guard : d0 p = 1) : d138 p ≤ (0 : Int) + d137 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1692 (p : Pattern) (guard : d1 p = 1) : d120 p ≤ (0 : Int) + d137 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d120, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare287 p hg
    simpa only [d120, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d120, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare449 p hg
    simpa only [d120, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1693 (p : Pattern) (guard : d0 p = 1) : d137 p ≤ (0 : Int) + d137 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1694 (p : Pattern) (guard : d758 p = 1) : d139 p ≤ (0 : Int) + d137 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d758, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1692 p hg
    simpa only [d758, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d758, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1693 p hg
    simpa only [d758, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1695 (p : Pattern) (guard : d1000 p = 1) : d140 p ≤ (0 : Int) + d137 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1000, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1691 p hg
    simpa only [d1000, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d758 p = 1 := by simpa only [d1000, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1694 p hg
    simpa only [d1000, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1696 (p : Pattern) (guard : d1001 p = 1) : d188 p ≤ (0 : Int) + d1007 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1000 p = 1 := by simpa only [d1001, d188, d1007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1695 p hg
    simpa only [d1001, d188, d1007, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1001, d188, d1007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare728 p hg
    simpa only [d1001, d188, d1007, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1697 (p : Pattern) (guard : d0 p = 1) : d145 p ≤ (0 : Int) + d144 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1698 (p : Pattern) (guard : d1 p = 1) : d126 p ≤ (0 : Int) + d143 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d126, d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare302 p hg
    simpa only [d126, d143, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d126, d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare458 p hg
    simpa only [d126, d143, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1699 (p : Pattern) (guard : d1 p = 1) : d127 p ≤ (0 : Int) + d144 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d127, d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1692 p hg
    simpa only [d127, d144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d127, d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1698 p hg
    simpa only [d127, d144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1700 (p : Pattern) (guard : d0 p = 1) : d144 p ≤ (0 : Int) + d144 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1701 (p : Pattern) (guard : d758 p = 1) : d146 p ≤ (0 : Int) + d144 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d758, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1699 p hg
    simpa only [d758, d146, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d758, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1700 p hg
    simpa only [d758, d146, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1702 (p : Pattern) (guard : d1000 p = 1) : d147 p ≤ (0 : Int) + d144 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1000, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1697 p hg
    simpa only [d1000, d147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d758 p = 1 := by simpa only [d1000, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1701 p hg
    simpa only [d1000, d147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1703 (p : Pattern) (guard : d1001 p = 1) : d249 p ≤ (0 : Int) + d1008 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1000 p = 1 := by simpa only [d1001, d249, d1008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1702 p hg
    simpa only [d1001, d249, d1008, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1001, d249, d1008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare732 p hg
    simpa only [d1001, d249, d1008, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1704 (p : Pattern) (guard : d1001 p = 1) : d250 p ≤ (0 : Int) + d1009 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1001 p = 1 := by simpa only [d250, d1009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1696 p hg
    simpa only [d250, d1009, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1001 p = 1 := by simpa only [d250, d1009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1703 p hg
    simpa only [d250, d1009, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1705 (p : Pattern) (guard : d1001 p = 1) : d251 p ≤ (0 : Int) + d1010 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1001 p = 1 := by simpa only [d251, d1010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1704 p hg
    simpa only [d251, d1010, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1001 p = 1 := by simpa only [d251, d1010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1687 p hg
    simpa only [d251, d1010, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1706 (p : Pattern) (guard : d1001 p = 1) : d317 p ≤ (0 : Int) + d1011 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1001 p = 1 := by simpa only [d317, d1011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1690 p hg
    simpa only [d317, d1011, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1001 p = 1 := by simpa only [d317, d1011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1705 p hg
    simpa only [d317, d1011, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1707 (p : Pattern) (guard : d1 p = 1) : d120 p ≤ (0 : Int) + d56 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d120, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare282 p hg
    simpa only [d120, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d120, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare449 p hg
    simpa only [d120, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1708 (p : Pattern) (guard : d0 p = 1) : d137 p ≤ (0 : Int) + d56 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1709 (p : Pattern) (guard : d758 p = 1) : d139 p ≤ (0 : Int) + d56 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d758, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1707 p hg
    simpa only [d758, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d758, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1708 p hg
    simpa only [d758, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1710 (p : Pattern) (guard : d1000 p = 1) : d153 p ≤ (0 : Int) + d56 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1000, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1651 p hg
    simpa only [d1000, d153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d758 p = 1 := by simpa only [d1000, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1709 p hg
    simpa only [d1000, d153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1711 (p : Pattern) (guard : d1001 p = 1) : d191 p ≤ (0 : Int) + d456 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1000 p = 1 := by simpa only [d1001, d191, d456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1710 p hg
    simpa only [d1001, d191, d456, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1001, d191, d456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare728 p hg
    simpa only [d1001, d191, d456, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1712 (p : Pattern) (guard : d1 p = 1) : d126 p ≤ (0 : Int) + d61 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d126, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare295 p hg
    simpa only [d126, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d126, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare458 p hg
    simpa only [d126, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1713 (p : Pattern) (guard : d1 p = 1) : d127 p ≤ (0 : Int) + d62 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d127, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1707 p hg
    simpa only [d127, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d127, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1712 p hg
    simpa only [d127, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1714 (p : Pattern) (guard : d0 p = 1) : d144 p ≤ (0 : Int) + d62 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1715 (p : Pattern) (guard : d758 p = 1) : d146 p ≤ (0 : Int) + d62 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d758, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1713 p hg
    simpa only [d758, d146, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d758, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1714 p hg
    simpa only [d758, d146, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1716 (p : Pattern) (guard : d1000 p = 1) : d155 p ≤ (0 : Int) + d62 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1000, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1658 p hg
    simpa only [d1000, d155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d758 p = 1 := by simpa only [d1000, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1715 p hg
    simpa only [d1000, d155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1717 (p : Pattern) (guard : d1001 p = 1) : d253 p ≤ (0 : Int) + d457 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1000 p = 1 := by simpa only [d1001, d253, d457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1716 p hg
    simpa only [d1001, d253, d457, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1001, d253, d457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare732 p hg
    simpa only [d1001, d253, d457, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1718 (p : Pattern) (guard : d1001 p = 1) : d254 p ≤ (0 : Int) + d458 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1001 p = 1 := by simpa only [d254, d458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1711 p hg
    simpa only [d254, d458, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1001 p = 1 := by simpa only [d254, d458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1717 p hg
    simpa only [d254, d458, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1719 (p : Pattern) (guard : d1001 p = 1) : d255 p ≤ (0 : Int) + d1003 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1001 p = 1 := by simpa only [d255, d1003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1718 p hg
    simpa only [d255, d1003, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1001 p = 1 := by simpa only [d255, d1003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1687 p hg
    simpa only [d255, d1003, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1720 (p : Pattern) (guard : d1001 p = 1) : d256 p ≤ (0 : Int) + d1005 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1001 p = 1 := by simpa only [d256, d1005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1719 p hg
    simpa only [d256, d1005, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1001 p = 1 := by simpa only [d256, d1005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1687 p hg
    simpa only [d256, d1005, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1721 (p : Pattern) (guard : d1001 p = 1) : d318 p ≤ (0 : Int) + d1012 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1001 p = 1 := by simpa only [d318, d1012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1706 p hg
    simpa only [d318, d1012, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1001 p = 1 := by simpa only [d318, d1012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1720 p hg
    simpa only [d318, d1012, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1722 (p : Pattern) (guard : d1001 p = 1) : d319 p ≤ (0 : Int) + d1013 p := by
  cases selected : p 108 with
  | false =>
    have hg : d1001 p = 1 := by simpa only [d319, d1013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1689 p hg
    simpa only [d319, d1013, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1001 p = 1 := by simpa only [d319, d1013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1721 p hg
    simpa only [d319, d1013, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1723 (p : Pattern) (guard : d742 p = 1) : d244 p ≤ (0 : Int) + d135 p := by
  cases selected : p 133 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d244, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1481 p hg
    simpa only [d244, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d244, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare346 p hg
    simpa only [d244, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1724 (p : Pattern) (guard : d742 p = 1) : d316 p ≤ (0 : Int) + d136 p := by
  cases selected : p 132 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d316, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1482 p hg
    simpa only [d316, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d316, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1723 p hg
    simpa only [d316, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1725 (p : Pattern) (guard : d742 p = 1) : d191 p ≤ (0 : Int) + d154 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d742, d191, d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare359 p hg
    simpa only [d742, d191, d154, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d742, d191, d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1486 p hg
    simpa only [d742, d191, d154, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1726 (p : Pattern) (guard : d742 p = 1) : d253 p ≤ (0 : Int) + d156 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d742, d253, d156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare361 p hg
    simpa only [d742, d253, d156, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d742, d253, d156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1488 p hg
    simpa only [d742, d253, d156, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1727 (p : Pattern) (guard : d742 p = 1) : d254 p ≤ (0 : Int) + d157 p := by
  cases selected : p 141 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d254, d157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1725 p hg
    simpa only [d254, d157, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d254, d157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1726 p hg
    simpa only [d254, d157, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1728 (p : Pattern) (guard : d742 p = 1) : d255 p ≤ (0 : Int) + d158 p := by
  cases selected : p 134 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d255, d158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1727 p hg
    simpa only [d255, d158, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d255, d158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare346 p hg
    simpa only [d255, d158, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1729 (p : Pattern) (guard : d742 p = 1) : d256 p ≤ (0 : Int) + d159 p := by
  cases selected : p 133 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d256, d159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1728 p hg
    simpa only [d256, d159, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d256, d159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare346 p hg
    simpa only [d256, d159, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1730 (p : Pattern) (guard : d742 p = 1) : d318 p ≤ (0 : Int) + d160 p := by
  cases selected : p 132 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d318, d160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1492 p hg
    simpa only [d318, d160, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d318, d160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1729 p hg
    simpa only [d318, d160, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1731 (p : Pattern) (guard : d742 p = 1) : d319 p ≤ (0 : Int) + d161 p := by
  cases selected : p 108 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d319, d161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d319, d161, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d319, d161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1730 p hg
    simpa only [d319, d161, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1732 (p : Pattern) (guard : d0 p = 1) : d242 p ≤ (0 : Int) + d66 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1733 (p : Pattern) (guard : d821 p = 1) : d315 p ≤ (0 : Int) + d210 p := by
  cases selected : p 133 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d821, d315, d210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1470 p hg
    simpa only [d821, d315, d210, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d821, d315, d210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1732 p hg
    simpa only [d821, d315, d210, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1734 (p : Pattern) (guard : d798 p = 1) : d242 p ≤ (0 : Int) + d214 p := by
  cases selected : p 134 with
  | false =>
    have hg : d798 p = 1 := by simpa only [d242, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare725 p hg
    simpa only [d242, d214, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d798 p = 1 := by simpa only [d242, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1631 p hg
    simpa only [d242, d214, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1735 (p : Pattern) (guard : d824 p = 1) : d244 p ≤ (0 : Int) + d215 p := by
  cases selected : p 133 with
  | false =>
    have hg : d798 p = 1 := by simpa only [d824, d244, d215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1734 p hg
    simpa only [d824, d244, d215, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d824, d244, d215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare203 p hg
    simpa only [d824, d244, d215, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1736 (p : Pattern) (guard : d825 p = 1) : d316 p ≤ (0 : Int) + d216 p := by
  cases selected : p 132 with
  | false =>
    have hg : d821 p = 1 := by simpa only [d825, d316, d216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1733 p hg
    simpa only [d825, d316, d216, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d824 p = 1 := by simpa only [d825, d316, d216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1735 p hg
    simpa only [d825, d316, d216, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1737 (p : Pattern) (guard : d0 p = 1) : d251 p ≤ (0 : Int) + d66 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1738 (p : Pattern) (guard : d821 p = 1) : d317 p ≤ (0 : Int) + d217 p := by
  cases selected : p 133 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d821, d317, d217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1485 p hg
    simpa only [d821, d317, d217, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d821, d317, d217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1737 p hg
    simpa only [d821, d317, d217, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1739 (p : Pattern) (guard : d0 p = 1) : d139 p ≤ (0 : Int) + d57 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1740 (p : Pattern) (guard : d794 p = 1) : d153 p ≤ (0 : Int) + d57 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d794, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare208 p hg
    simpa only [d794, d153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d794, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1739 p hg
    simpa only [d794, d153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1741 (p : Pattern) (guard : d798 p = 1) : d191 p ≤ (0 : Int) + d68 p := by
  cases selected : p 158 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d798, d191, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1740 p hg
    simpa only [d798, d191, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d798, d191, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare728 p hg
    simpa only [d798, d191, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1742 (p : Pattern) (guard : d0 p = 1) : d146 p ≤ (0 : Int) + d63 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1743 (p : Pattern) (guard : d794 p = 1) : d155 p ≤ (0 : Int) + d63 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d794, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare320 p hg
    simpa only [d794, d155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d794, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1742 p hg
    simpa only [d794, d155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1744 (p : Pattern) (guard : d798 p = 1) : d253 p ≤ (0 : Int) + d69 p := by
  cases selected : p 158 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d798, d253, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1743 p hg
    simpa only [d798, d253, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d798, d253, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare732 p hg
    simpa only [d798, d253, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1745 (p : Pattern) (guard : d798 p = 1) : d254 p ≤ (0 : Int) + d70 p := by
  cases selected : p 141 with
  | false =>
    have hg : d798 p = 1 := by simpa only [d254, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1741 p hg
    simpa only [d254, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d798 p = 1 := by simpa only [d254, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1744 p hg
    simpa only [d254, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1746 (p : Pattern) (guard : d798 p = 1) : d255 p ≤ (0 : Int) + d71 p := by
  cases selected : p 134 with
  | false =>
    have hg : d798 p = 1 := by simpa only [d255, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1745 p hg
    simpa only [d255, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d798 p = 1 := by simpa only [d255, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare511 p hg
    simpa only [d255, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1747 (p : Pattern) (guard : d824 p = 1) : d256 p ≤ (0 : Int) + d73 p := by
  cases selected : p 133 with
  | false =>
    have hg : d798 p = 1 := by simpa only [d824, d256, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1746 p hg
    simpa only [d824, d256, d73, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d824, d256, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare203 p hg
    simpa only [d824, d256, d73, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1748 (p : Pattern) (guard : d825 p = 1) : d318 p ≤ (0 : Int) + d218 p := by
  cases selected : p 132 with
  | false =>
    have hg : d821 p = 1 := by simpa only [d825, d318, d218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1738 p hg
    simpa only [d825, d318, d218, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d824 p = 1 := by simpa only [d825, d318, d218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1747 p hg
    simpa only [d825, d318, d218, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1749 (p : Pattern) (guard : d825 p = 1) : d319 p ≤ (0 : Int) + d219 p := by
  cases selected : p 108 with
  | false =>
    have hg : d825 p = 1 := by simpa only [d319, d219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1736 p hg
    simpa only [d319, d219, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d825 p = 1 := by simpa only [d319, d219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1748 p hg
    simpa only [d319, d219, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1750 (p : Pattern) (guard : d794 p = 1) : d335 p ≤ (0 : Int) + d64 p := by
  cases selected : p 141 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d335, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1402 p hg
    simpa only [d335, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d335, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1406 p hg
    simpa only [d335, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1751 (p : Pattern) (guard : d794 p = 1) : d107 p ≤ (0 : Int) + d108 p := by
  cases selected : p 158 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1393 p hg
    simpa only [d108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare478 p hg
    simpa only [d108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1752 (p : Pattern) (guard : d794 p = 1) : d110 p ≤ (0 : Int) + d111 p := by
  cases selected : p 158 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1396 p hg
    simpa only [d111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare482 p hg
    simpa only [d111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1753 (p : Pattern) (guard : d794 p = 1) : d336 p ≤ (0 : Int) + d112 p := by
  cases selected : p 141 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d336, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1751 p hg
    simpa only [d336, d112, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d336, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1752 p hg
    simpa only [d336, d112, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1754 (p : Pattern) (guard : d794 p = 1) : d337 p ≤ (0 : Int) + d113 p := by
  cases selected : p 134 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d337, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1750 p hg
    simpa only [d337, d113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d337, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1753 p hg
    simpa only [d337, d113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1755 (p : Pattern) (guard : d0 p = 1) : d341 p ≤ (0 : Int) + d66 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1756 (p : Pattern) (guard : d801 p = 1) : d342 p ≤ (0 : Int) + d210 p := by
  cases selected : p 133 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d801, d342, d210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1754 p hg
    simpa only [d801, d342, d210, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d801, d342, d210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1755 p hg
    simpa only [d801, d342, d210, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1757 (p : Pattern) (guard : d794 p = 1) : d338 p ≤ (0 : Int) + d68 p := by
  cases selected : p 158 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d338, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1402 p hg
    simpa only [d338, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d338, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare519 p hg
    simpa only [d338, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1758 (p : Pattern) (guard : d794 p = 1) : d339 p ≤ (0 : Int) + d69 p := by
  cases selected : p 158 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d339, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1406 p hg
    simpa only [d339, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d339, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare521 p hg
    simpa only [d339, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1759 (p : Pattern) (guard : d794 p = 1) : d340 p ≤ (0 : Int) + d70 p := by
  cases selected : p 141 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d340, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1757 p hg
    simpa only [d340, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d340, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1758 p hg
    simpa only [d340, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1760 (p : Pattern) (guard : d794 p = 1) : d341 p ≤ (0 : Int) + d214 p := by
  cases selected : p 134 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d341, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1759 p hg
    simpa only [d341, d214, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d341, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare524 p hg
    simpa only [d341, d214, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1761 (p : Pattern) (guard : d801 p = 1) : d343 p ≤ (0 : Int) + d215 p := by
  cases selected : p 133 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d801, d343, d215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1760 p hg
    simpa only [d801, d343, d215, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d801, d343, d215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare203 p hg
    simpa only [d801, d343, d215, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1762 (p : Pattern) (guard : d801 p = 1) : d344 p ≤ (0 : Int) + d216 p := by
  cases selected : p 132 with
  | false =>
    have hg : d801 p = 1 := by simpa only [d344, d216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1756 p hg
    simpa only [d344, d216, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d801 p = 1 := by simpa only [d344, d216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1761 p hg
    simpa only [d344, d216, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1763 (p : Pattern) (guard : d794 p = 1) : d345 p ≤ (0 : Int) + d67 p := by
  cases selected : p 134 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d345, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1750 p hg
    simpa only [d345, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d345, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare500 p hg
    simpa only [d345, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1764 (p : Pattern) (guard : d0 p = 1) : d351 p ≤ (0 : Int) + d66 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1765 (p : Pattern) (guard : d801 p = 1) : d352 p ≤ (0 : Int) + d217 p := by
  cases selected : p 133 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d801, d352, d217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1763 p hg
    simpa only [d801, d352, d217, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d801, d352, d217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1764 p hg
    simpa only [d801, d352, d217, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1766 (p : Pattern) (guard : d794 p = 1) : d353 p ≤ (0 : Int) + d71 p := by
  cases selected : p 134 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d353, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1759 p hg
    simpa only [d353, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d353, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare500 p hg
    simpa only [d353, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1767 (p : Pattern) (guard : d801 p = 1) : d354 p ≤ (0 : Int) + d73 p := by
  cases selected : p 133 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d801, d354, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1766 p hg
    simpa only [d801, d354, d73, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d801, d354, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare203 p hg
    simpa only [d801, d354, d73, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1768 (p : Pattern) (guard : d801 p = 1) : d355 p ≤ (0 : Int) + d218 p := by
  cases selected : p 132 with
  | false =>
    have hg : d801 p = 1 := by simpa only [d355, d218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1765 p hg
    simpa only [d355, d218, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d801 p = 1 := by simpa only [d355, d218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1767 p hg
    simpa only [d355, d218, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1769 (p : Pattern) (guard : d801 p = 1) : d356 p ≤ (0 : Int) + d219 p := by
  cases selected : p 108 with
  | false =>
    have hg : d801 p = 1 := by simpa only [d356, d219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1762 p hg
    simpa only [d356, d219, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d801 p = 1 := by simpa only [d356, d219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1768 p hg
    simpa only [d356, d219, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1770 (p : Pattern) (guard : d794 p = 1) : d107 p ≤ (0 : Int) + d179 p := by
  cases selected : p 158 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1393 p hg
    simpa only [d179, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare727 p hg
    simpa only [d179, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1771 (p : Pattern) (guard : d794 p = 1) : d110 p ≤ (0 : Int) + d237 p := by
  cases selected : p 158 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1396 p hg
    simpa only [d237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare731 p hg
    simpa only [d237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1772 (p : Pattern) (guard : d794 p = 1) : d336 p ≤ (0 : Int) + d238 p := by
  cases selected : p 141 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d336, d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1770 p hg
    simpa only [d336, d238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d336, d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1771 p hg
    simpa only [d336, d238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1773 (p : Pattern) (guard : d794 p = 1) : d337 p ≤ (0 : Int) + d239 p := by
  cases selected : p 134 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d337, d239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1750 p hg
    simpa only [d337, d239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d337, d239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1772 p hg
    simpa only [d337, d239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1774 (p : Pattern) (guard : d794 p = 1) : d211 p ≤ (0 : Int) + d181 p := by
  cases selected : p 158 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d211, d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare727 p hg
    simpa only [d211, d181, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d211, d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare519 p hg
    simpa only [d211, d181, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1775 (p : Pattern) (guard : d794 p = 1) : d212 p ≤ (0 : Int) + d240 p := by
  cases selected : p 158 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d212, d240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare731 p hg
    simpa only [d212, d240, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d212, d240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare521 p hg
    simpa only [d212, d240, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1776 (p : Pattern) (guard : d794 p = 1) : d213 p ≤ (0 : Int) + d241 p := by
  cases selected : p 141 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d213, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1774 p hg
    simpa only [d213, d241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d213, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1775 p hg
    simpa only [d213, d241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1777 (p : Pattern) (guard : d794 p = 1) : d341 p ≤ (0 : Int) + d242 p := by
  cases selected : p 134 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d341, d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1759 p hg
    simpa only [d341, d242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d341, d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1776 p hg
    simpa only [d341, d242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1778 (p : Pattern) (guard : d794 p = 1) : d342 p ≤ (0 : Int) + d243 p := by
  cases selected : p 133 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d342, d243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1773 p hg
    simpa only [d342, d243, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d342, d243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1777 p hg
    simpa only [d342, d243, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1779 (p : Pattern) (guard : d794 p = 1) : d343 p ≤ (0 : Int) + d244 p := by
  cases selected : p 133 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d343, d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1777 p hg
    simpa only [d343, d244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d343, d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare500 p hg
    simpa only [d343, d244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1780 (p : Pattern) (guard : d794 p = 1) : d344 p ≤ (0 : Int) + d245 p := by
  cases selected : p 132 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d344, d245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1778 p hg
    simpa only [d344, d245, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d344, d245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1779 p hg
    simpa only [d344, d245, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1781 (p : Pattern) (guard : d794 p = 1) : d114 p ≤ (0 : Int) + d153 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d794, d114, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare208 p hg
    simpa only [d794, d114, d153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d794, d114, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1425 p hg
    simpa only [d794, d114, d153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1782 (p : Pattern) (guard : d794 p = 1) : d114 p ≤ (0 : Int) + d186 p := by
  cases selected : p 158 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1402 p hg
    simpa only [d186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1781 p hg
    simpa only [d186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1783 (p : Pattern) (guard : d794 p = 1) : d116 p ≤ (0 : Int) + d155 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d794, d116, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare320 p hg
    simpa only [d794, d116, d155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d794, d116, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1429 p hg
    simpa only [d794, d116, d155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1784 (p : Pattern) (guard : d794 p = 1) : d116 p ≤ (0 : Int) + d246 p := by
  cases selected : p 158 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1406 p hg
    simpa only [d246, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1783 p hg
    simpa only [d246, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1785 (p : Pattern) (guard : d794 p = 1) : d335 p ≤ (0 : Int) + d247 p := by
  cases selected : p 141 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d335, d247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1782 p hg
    simpa only [d335, d247, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d335, d247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1784 p hg
    simpa only [d335, d247, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1786 (p : Pattern) (guard : d794 p = 1) : d345 p ≤ (0 : Int) + d248 p := by
  cases selected : p 134 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d345, d248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1785 p hg
    simpa only [d345, d248, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d345, d248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare500 p hg
    simpa only [d345, d248, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1787 (p : Pattern) (guard : d794 p = 1) : d346 p ≤ (0 : Int) + d140 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d794, d346, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare502 p hg
    simpa only [d794, d346, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d794, d346, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1425 p hg
    simpa only [d794, d346, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1788 (p : Pattern) (guard : d794 p = 1) : d347 p ≤ (0 : Int) + d188 p := by
  cases selected : p 158 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d347, d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1787 p hg
    simpa only [d347, d188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d347, d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare519 p hg
    simpa only [d347, d188, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1789 (p : Pattern) (guard : d794 p = 1) : d348 p ≤ (0 : Int) + d147 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d794, d348, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare506 p hg
    simpa only [d794, d348, d147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d794, d348, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1429 p hg
    simpa only [d794, d348, d147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1790 (p : Pattern) (guard : d794 p = 1) : d349 p ≤ (0 : Int) + d249 p := by
  cases selected : p 158 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d349, d249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1789 p hg
    simpa only [d349, d249, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d349, d249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare521 p hg
    simpa only [d349, d249, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1791 (p : Pattern) (guard : d794 p = 1) : d350 p ≤ (0 : Int) + d250 p := by
  cases selected : p 141 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d350, d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1788 p hg
    simpa only [d350, d250, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d350, d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1790 p hg
    simpa only [d350, d250, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1792 (p : Pattern) (guard : d794 p = 1) : d351 p ≤ (0 : Int) + d251 p := by
  cases selected : p 134 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d351, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1791 p hg
    simpa only [d351, d251, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d351, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare500 p hg
    simpa only [d351, d251, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1793 (p : Pattern) (guard : d794 p = 1) : d352 p ≤ (0 : Int) + d252 p := by
  cases selected : p 133 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d352, d252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1786 p hg
    simpa only [d352, d252, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d352, d252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1792 p hg
    simpa only [d352, d252, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1794 (p : Pattern) (guard : d794 p = 1) : d338 p ≤ (0 : Int) + d191 p := by
  cases selected : p 158 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d338, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1781 p hg
    simpa only [d338, d191, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d338, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare519 p hg
    simpa only [d338, d191, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1795 (p : Pattern) (guard : d794 p = 1) : d339 p ≤ (0 : Int) + d253 p := by
  cases selected : p 158 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d339, d253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1783 p hg
    simpa only [d339, d253, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d339, d253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare521 p hg
    simpa only [d339, d253, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1796 (p : Pattern) (guard : d794 p = 1) : d340 p ≤ (0 : Int) + d254 p := by
  cases selected : p 141 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d340, d254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1794 p hg
    simpa only [d340, d254, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d340, d254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1795 p hg
    simpa only [d340, d254, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1797 (p : Pattern) (guard : d794 p = 1) : d353 p ≤ (0 : Int) + d255 p := by
  cases selected : p 134 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d353, d255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1796 p hg
    simpa only [d353, d255, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d353, d255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare500 p hg
    simpa only [d353, d255, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1798 (p : Pattern) (guard : d794 p = 1) : d354 p ≤ (0 : Int) + d256 p := by
  cases selected : p 133 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d354, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1797 p hg
    simpa only [d354, d256, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d354, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare500 p hg
    simpa only [d354, d256, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1799 (p : Pattern) (guard : d794 p = 1) : d355 p ≤ (0 : Int) + d257 p := by
  cases selected : p 132 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d355, d257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1793 p hg
    simpa only [d355, d257, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d355, d257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1798 p hg
    simpa only [d355, d257, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1800 (p : Pattern) (guard : d794 p = 1) : d356 p ≤ (0 : Int) + d258 p := by
  cases selected : p 108 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d356, d258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1780 p hg
    simpa only [d356, d258, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d356, d258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1799 p hg
    simpa only [d356, d258, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1801 (p : Pattern) (guard : d794 p = 1) : d114 p ≤ (2 : Int) + d57 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d794, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare50 p hg
    simpa only [d794, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d794, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1593 p hg
    simpa only [d794, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1802 (p : Pattern) (guard : d794 p = 1) : d116 p ≤ (2 : Int) + d63 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d794, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare53 p hg
    simpa only [d794, d116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d794, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1595 p hg
    simpa only [d794, d116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1803 (p : Pattern) (guard : d794 p = 1) : d335 p ≤ (2 : Int) + d64 p := by
  cases selected : p 141 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d335, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1801 p hg
    simpa only [d335, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d335, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1802 p hg
    simpa only [d335, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1804 (p : Pattern) (guard : d0 p = 1) : d55 p ≤ (2 : Int) + d106 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1805 (p : Pattern) (guard : d794 p = 1) : d107 p ≤ (2 : Int) + d106 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d794, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare57 p hg
    simpa only [d794, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d794, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1804 p hg
    simpa only [d794, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1806 (p : Pattern) (guard : d0 p = 1) : d55 p ≤ (2 : Int) + d121 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1807 (p : Pattern) (guard : d794 p = 1) : d107 p ≤ (2 : Int) + d122 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d794, d107, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare57 p hg
    simpa only [d794, d107, d122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d794, d107, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1806 p hg
    simpa only [d794, d107, d122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1808 (p : Pattern) (guard : d794 p = 1) : d107 p ≤ (2 : Int) + d179 p := by
  cases selected : p 158 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1805 p hg
    simpa only [d179, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1807 p hg
    simpa only [d179, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1809 (p : Pattern) (guard : d0 p = 1) : d65 p ≤ (2 : Int) + d109 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1810 (p : Pattern) (guard : d794 p = 1) : d110 p ≤ (2 : Int) + d109 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d794, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare64 p hg
    simpa only [d794, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d794, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1809 p hg
    simpa only [d794, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1811 (p : Pattern) (guard : d0 p = 1) : d65 p ≤ (2 : Int) + d128 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1812 (p : Pattern) (guard : d794 p = 1) : d110 p ≤ (2 : Int) + d129 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d794, d110, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare64 p hg
    simpa only [d794, d110, d129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d794, d110, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1811 p hg
    simpa only [d794, d110, d129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1813 (p : Pattern) (guard : d794 p = 1) : d110 p ≤ (2 : Int) + d237 p := by
  cases selected : p 158 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1810 p hg
    simpa only [d237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1812 p hg
    simpa only [d237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1814 (p : Pattern) (guard : d794 p = 1) : d336 p ≤ (2 : Int) + d238 p := by
  cases selected : p 141 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d336, d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1808 p hg
    simpa only [d336, d238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d336, d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1813 p hg
    simpa only [d336, d238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1815 (p : Pattern) (guard : d794 p = 1) : d337 p ≤ (2 : Int) + d239 p := by
  cases selected : p 134 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d337, d239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1803 p hg
    simpa only [d337, d239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d337, d239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1814 p hg
    simpa only [d337, d239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1816 (p : Pattern) (guard : d794 p = 1) : d55 p ≤ (2 : Int) + d55 p := by
  omega
theorem compare1817 (p : Pattern) (guard : d794 p = 1) : d338 p ≤ (2 : Int) + d68 p := by
  cases selected : p 158 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d338, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1801 p hg
    simpa only [d338, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d338, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1816 p hg
    simpa only [d338, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1818 (p : Pattern) (guard : d794 p = 1) : d65 p ≤ (2 : Int) + d65 p := by
  omega
theorem compare1819 (p : Pattern) (guard : d794 p = 1) : d339 p ≤ (2 : Int) + d69 p := by
  cases selected : p 158 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d339, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1802 p hg
    simpa only [d339, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d339, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1818 p hg
    simpa only [d339, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban12CostPartition
