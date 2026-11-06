/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons011
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare1680 (p : Pattern) (guard : d1 p = 1) : d243 p ≤ (0 : Int) + d160 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d243, d160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1679 p hg
    simpa only [d243, d160, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d243, d160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1605 p hg
    simpa only [d243, d160, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1681 (p : Pattern) (guard : d1 p = 1) : d244 p ≤ (0 : Int) + d161 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d244, d161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1680 p hg
    simpa only [d244, d161, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d244, d161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1609 p hg
    simpa only [d244, d161, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1682 (p : Pattern) (guard : d1 p = 1) : d211 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1323 p hg
    simpa only [d211, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d211, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1683 (p : Pattern) (guard : d1 p = 1) : d245 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1596 p hg
    simpa only [d245, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1682 p hg
    simpa only [d245, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1684 (p : Pattern) (guard : d1 p = 1) : d246 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1683 p hg
    simpa only [d246, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1608 p hg
    simpa only [d246, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1685 (p : Pattern) (guard : d1 p = 1) : d247 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare947 p hg
    simpa only [d247, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d247, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1686 (p : Pattern) (guard : d1 p = 1) : d248 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1685 p hg
    simpa only [d248, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d248, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1687 (p : Pattern) (guard : d1 p = 1) : d249 p ≤ (0 : Int) + d12 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1684 p hg
    simpa only [d249, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1686 p hg
    simpa only [d249, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1688 (p : Pattern) (guard : d1 p = 1) : d250 p ≤ (0 : Int) + d162 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d250, d162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1681 p hg
    simpa only [d250, d162, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d250, d162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1687 p hg
    simpa only [d250, d162, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1689 (p : Pattern) (guard : d1 p = 1) : d251 p ≤ (0 : Int) + d224 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d251, d224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1677 p hg
    simpa only [d251, d224, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d251, d224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1688 p hg
    simpa only [d251, d224, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1690 (p : Pattern) (guard : d0 p = 1) : d262 p ≤ (0 : Int) + d224 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1691 (p : Pattern) (guard : d4066 p = 1) : d263 p ≤ (0 : Int) + d224 p := by
  cases selected : p 116 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4066, d263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1689 p hg
    simpa only [d4066, d263, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4066, d263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1690 p hg
    simpa only [d4066, d263, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1692 (p : Pattern) (guard : d4103 p = 1) : d264 p ≤ (0 : Int) + d224 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4103, d264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1661 p hg
    simpa only [d4103, d264, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4066 p = 1 := by simpa only [d4103, d264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1691 p hg
    simpa only [d4103, d264, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1693 (p : Pattern) (guard : d4103 p = 1) : d265 p ≤ (0 : Int) + d4106 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4103 p = 1 := by simpa only [d265, d4106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1557 p hg
    simpa only [d265, d4106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4103 p = 1 := by simpa only [d265, d4106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1692 p hg
    simpa only [d265, d4106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1694 (p : Pattern) (guard : d4103 p = 1) : d266 p ≤ (0 : Int) + d4107 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4103 p = 1 := by simpa only [d266, d4107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1660 p hg
    simpa only [d266, d4107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4103 p = 1 := by simpa only [d266, d4107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1693 p hg
    simpa only [d266, d4107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1695 (p : Pattern) (guard : d4103 p = 1) : d267 p ≤ (0 : Int) + d4108 p := by
  cases selected : p 48 with
  | false =>
    have hg : d4103 p = 1 := by simpa only [d267, d4108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1617 p hg
    simpa only [d267, d4108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4103 p = 1 := by simpa only [d267, d4108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1694 p hg
    simpa only [d267, d4108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1696 (p : Pattern) (guard : d0 p = 1) : d208 p ≤ (0 : Int) + d100 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1697 (p : Pattern) (guard : d4058 p = 1) : d209 p ≤ (0 : Int) + d101 p := by
  cases selected : p 115 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4058, d209, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare777 p hg
    simpa only [d4058, d209, d101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4058, d209, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1696 p hg
    simpa only [d4058, d209, d101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1698 (p : Pattern) (guard : d4058 p = 1) : d210 p ≤ (0 : Int) + d101 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4058 p = 1 := by simpa only [d210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1149 p hg
    simpa only [d210, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4058 p = 1 := by simpa only [d210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1697 p hg
    simpa only [d210, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1699 (p : Pattern) (guard : d0 p = 1) : d263 p ≤ (0 : Int) + d308 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1700 (p : Pattern) (guard : d4058 p = 1) : d264 p ≤ (0 : Int) + d309 p := by
  cases selected : p 115 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4058, d264, d309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1108 p hg
    simpa only [d4058, d264, d309, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4058, d264, d309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1699 p hg
    simpa only [d4058, d264, d309, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1701 (p : Pattern) (guard : d4058 p = 1) : d265 p ≤ (0 : Int) + d310 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4058 p = 1 := by simpa only [d265, d310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1149 p hg
    simpa only [d265, d310, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4058 p = 1 := by simpa only [d265, d310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1700 p hg
    simpa only [d265, d310, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1702 (p : Pattern) (guard : d4058 p = 1) : d266 p ≤ (0 : Int) + d311 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4058 p = 1 := by simpa only [d266, d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1698 p hg
    simpa only [d266, d311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4058 p = 1 := by simpa only [d266, d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1701 p hg
    simpa only [d266, d311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1703 (p : Pattern) (guard : d4058 p = 1) : d267 p ≤ (0 : Int) + d312 p := by
  cases selected : p 48 with
  | false =>
    have hg : d4058 p = 1 := by simpa only [d267, d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1148 p hg
    simpa only [d267, d312, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4058 p = 1 := by simpa only [d267, d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1702 p hg
    simpa only [d267, d312, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1704 (p : Pattern) (guard : d0 p = 1) : d426 p ≤ (0 : Int) + d100 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1705 (p : Pattern) (guard : d4058 p = 1) : d489 p ≤ (0 : Int) + d101 p := by
  cases selected : p 115 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4058, d489, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare777 p hg
    simpa only [d4058, d489, d101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4058, d489, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1704 p hg
    simpa only [d4058, d489, d101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1706 (p : Pattern) (guard : d0 p = 1) : d445 p ≤ (0 : Int) + d100 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1707 (p : Pattern) (guard : d4058 p = 1) : d490 p ≤ (0 : Int) + d101 p := by
  cases selected : p 115 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4058, d490, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare777 p hg
    simpa only [d4058, d490, d101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4058, d490, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1706 p hg
    simpa only [d4058, d490, d101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1708 (p : Pattern) (guard : d4058 p = 1) : d491 p ≤ (0 : Int) + d101 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4058 p = 1 := by simpa only [d491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1705 p hg
    simpa only [d491, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4058 p = 1 := by simpa only [d491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1707 p hg
    simpa only [d491, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1709 (p : Pattern) (guard : d0 p = 1) : d445 p ≤ (0 : Int) + d166 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1710 (p : Pattern) (guard : d4058 p = 1) : d492 p ≤ (0 : Int) + d167 p := by
  cases selected : p 115 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4058, d492, d167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1103 p hg
    simpa only [d4058, d492, d167, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4058, d492, d167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1709 p hg
    simpa only [d4058, d492, d167, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1711 (p : Pattern) (guard : d4058 p = 1) : d493 p ≤ (0 : Int) + d168 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4058 p = 1 := by simpa only [d493, d168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1705 p hg
    simpa only [d493, d168, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4058 p = 1 := by simpa only [d493, d168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1710 p hg
    simpa only [d493, d168, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1712 (p : Pattern) (guard : d4058 p = 1) : d494 p ≤ (0 : Int) + d169 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4058 p = 1 := by simpa only [d494, d169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1708 p hg
    simpa only [d494, d169, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4058 p = 1 := by simpa only [d494, d169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1711 p hg
    simpa only [d494, d169, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1713 (p : Pattern) (guard : d0 p = 1) : d477 p ≤ (0 : Int) + d308 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1714 (p : Pattern) (guard : d4058 p = 1) : d495 p ≤ (0 : Int) + d309 p := by
  cases selected : p 115 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4058, d495, d309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1108 p hg
    simpa only [d4058, d495, d309, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4058, d495, d309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1713 p hg
    simpa only [d4058, d495, d309, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1715 (p : Pattern) (guard : d4058 p = 1) : d496 p ≤ (0 : Int) + d310 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4058 p = 1 := by simpa only [d496, d310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1705 p hg
    simpa only [d496, d310, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4058 p = 1 := by simpa only [d496, d310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1714 p hg
    simpa only [d496, d310, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1716 (p : Pattern) (guard : d4058 p = 1) : d497 p ≤ (0 : Int) + d311 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4058 p = 1 := by simpa only [d497, d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1708 p hg
    simpa only [d497, d311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4058 p = 1 := by simpa only [d497, d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1715 p hg
    simpa only [d497, d311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1717 (p : Pattern) (guard : d4058 p = 1) : d498 p ≤ (0 : Int) + d312 p := by
  cases selected : p 48 with
  | false =>
    have hg : d4058 p = 1 := by simpa only [d498, d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1712 p hg
    simpa only [d498, d312, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4058 p = 1 := by simpa only [d498, d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1716 p hg
    simpa only [d498, d312, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1718 (p : Pattern) (guard : d1 p = 1) : d98 p ≤ (2 : Int) + d98 p := by
  omega
theorem compare1719 (p : Pattern) (guard : d0 p = 1) : d426 p ≤ (2 : Int) + d100 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1720 (p : Pattern) (guard : d4058 p = 1) : d489 p ≤ (2 : Int) + d101 p := by
  cases selected : p 115 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4058, d489, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1718 p hg
    simpa only [d4058, d489, d101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4058, d489, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1719 p hg
    simpa only [d4058, d489, d101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1721 (p : Pattern) (guard : d0 p = 1) : d490 p ≤ (2 : Int) + d101 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1722 (p : Pattern) (guard : d4059 p = 1) : d491 p ≤ (2 : Int) + d101 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4058 p = 1 := by simpa only [d4059, d491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1720 p hg
    simpa only [d4059, d491, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4059, d491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1721 p hg
    simpa only [d4059, d491, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1723 (p : Pattern) (guard : d1 p = 1) : d0 p ≤ (2 : Int) + d1 p := by
  change (0 : Int) ≤ (2 : Int) + 1
  decide
theorem compare1724 (p : Pattern) (guard : d1 p = 1) : d12 p ≤ (2 : Int) + d12 p := by
  omega
theorem compare1725 (p : Pattern) (guard : d1 p = 1) : d13 p ≤ (2 : Int) + d102 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d13, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1723 p hg
    simpa only [d13, d102, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d13, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d13, d102, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1726 (p : Pattern) (guard : d1 p = 1) : d14 p ≤ (2 : Int) + d103 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d14, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1723 p hg
    simpa only [d14, d103, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d14, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1725 p hg
    simpa only [d14, d103, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1727 (p : Pattern) (guard : d1 p = 1) : d15 p ≤ (2 : Int) + d104 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d15, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1726 p hg
    simpa only [d15, d104, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d15, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d15, d104, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1728 (p : Pattern) (guard : d1 p = 1) : d16 p ≤ (2 : Int) + d105 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d16, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1726 p hg
    simpa only [d16, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d16, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1727 p hg
    simpa only [d16, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1729 (p : Pattern) (guard : d1 p = 1) : d4 p ≤ (2 : Int) + d5 p := by
  change (4 : Int) ≤ (2 : Int) + 5
  decide
theorem compare1730 (p : Pattern) (guard : d1 p = 1) : d17 p ≤ (2 : Int) + d106 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d17, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1729 p hg
    simpa only [d17, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d17, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d17, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1731 (p : Pattern) (guard : d1 p = 1) : d18 p ≤ (2 : Int) + d107 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d18, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1729 p hg
    simpa only [d18, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d18, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1730 p hg
    simpa only [d18, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1732 (p : Pattern) (guard : d1 p = 1) : d19 p ≤ (2 : Int) + d108 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d19, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1731 p hg
    simpa only [d19, d108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d19, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d19, d108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1733 (p : Pattern) (guard : d1 p = 1) : d20 p ≤ (2 : Int) + d109 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d20, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1731 p hg
    simpa only [d20, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d20, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1732 p hg
    simpa only [d20, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1734 (p : Pattern) (guard : d1 p = 1) : d21 p ≤ (2 : Int) + d110 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d21, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1728 p hg
    simpa only [d21, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d21, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1733 p hg
    simpa only [d21, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1735 (p : Pattern) (guard : d1 p = 1) : d22 p ≤ (2 : Int) + d111 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d22, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1728 p hg
    simpa only [d22, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d22, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1734 p hg
    simpa only [d22, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1736 (p : Pattern) (guard : d1 p = 1) : d9 p ≤ (2 : Int) + d10 p := by
  change (9 : Int) ≤ (2 : Int) + 10
  decide
theorem compare1737 (p : Pattern) (guard : d1 p = 1) : d23 p ≤ (2 : Int) + d57 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d23, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1736 p hg
    simpa only [d23, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d23, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d23, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1738 (p : Pattern) (guard : d1 p = 1) : d24 p ≤ (2 : Int) + d58 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d24, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1736 p hg
    simpa only [d24, d58, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d24, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1737 p hg
    simpa only [d24, d58, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1739 (p : Pattern) (guard : d1 p = 1) : d25 p ≤ (2 : Int) + d59 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d25, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1738 p hg
    simpa only [d25, d59, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d25, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d25, d59, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1740 (p : Pattern) (guard : d1 p = 1) : d26 p ≤ (2 : Int) + d60 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d26, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1738 p hg
    simpa only [d26, d60, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d26, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1739 p hg
    simpa only [d26, d60, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1741 (p : Pattern) (guard : d1 p = 1) : d27 p ≤ (2 : Int) + d112 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d27, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1740 p hg
    simpa only [d27, d112, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d27, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d27, d112, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1742 (p : Pattern) (guard : d1 p = 1) : d28 p ≤ (2 : Int) + d113 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d28, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1734 p hg
    simpa only [d28, d113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d28, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1741 p hg
    simpa only [d28, d113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1743 (p : Pattern) (guard : d1 p = 1) : d29 p ≤ (2 : Int) + d114 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d29, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1735 p hg
    simpa only [d29, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d29, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1742 p hg
    simpa only [d29, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1744 (p : Pattern) (guard : d1 p = 1) : d2 p ≤ (2 : Int) + d3 p := by
  change (2 : Int) ≤ (2 : Int) + 3
  decide
theorem compare1745 (p : Pattern) (guard : d1 p = 1) : d30 p ≤ (2 : Int) + d115 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d30, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1744 p hg
    simpa only [d30, d115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d30, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d30, d115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1746 (p : Pattern) (guard : d1 p = 1) : d31 p ≤ (2 : Int) + d116 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d31, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1744 p hg
    simpa only [d31, d116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d31, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1745 p hg
    simpa only [d31, d116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1747 (p : Pattern) (guard : d1 p = 1) : d32 p ≤ (2 : Int) + d117 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d32, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1746 p hg
    simpa only [d32, d117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d32, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d32, d117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1748 (p : Pattern) (guard : d1 p = 1) : d33 p ≤ (2 : Int) + d118 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d33, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1726 p hg
    simpa only [d33, d118, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d33, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1747 p hg
    simpa only [d33, d118, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1749 (p : Pattern) (guard : d1 p = 1) : d6 p ≤ (2 : Int) + d7 p := by
  change (6 : Int) ≤ (2 : Int) + 7
  decide
theorem compare1750 (p : Pattern) (guard : d1 p = 1) : d34 p ≤ (2 : Int) + d119 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d34, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1749 p hg
    simpa only [d34, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d34, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d34, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1751 (p : Pattern) (guard : d1 p = 1) : d35 p ≤ (2 : Int) + d120 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d35, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1749 p hg
    simpa only [d35, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d35, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1750 p hg
    simpa only [d35, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1752 (p : Pattern) (guard : d1 p = 1) : d36 p ≤ (2 : Int) + d121 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d36, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1751 p hg
    simpa only [d36, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d36, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d36, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1753 (p : Pattern) (guard : d1 p = 1) : d37 p ≤ (2 : Int) + d122 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d37, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1726 p hg
    simpa only [d37, d122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d37, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1752 p hg
    simpa only [d37, d122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1754 (p : Pattern) (guard : d1 p = 1) : d38 p ≤ (2 : Int) + d123 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d38, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1748 p hg
    simpa only [d38, d123, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d38, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1753 p hg
    simpa only [d38, d123, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1755 (p : Pattern) (guard : d1 p = 1) : d11 p ≤ (2 : Int) + d12 p := by
  change (11 : Int) ≤ (2 : Int) + 12
  decide
theorem compare1756 (p : Pattern) (guard : d1 p = 1) : d39 p ≤ (2 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1755 p hg
    simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1757 (p : Pattern) (guard : d1 p = 1) : d40 p ≤ (2 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1755 p hg
    simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1756 p hg
    simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1758 (p : Pattern) (guard : d1 p = 1) : d41 p ≤ (2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1757 p hg
    simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1759 (p : Pattern) (guard : d1 p = 1) : d42 p ≤ (2 : Int) + d124 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d42, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1726 p hg
    simpa only [d42, d124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d42, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1758 p hg
    simpa only [d42, d124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1760 (p : Pattern) (guard : d1 p = 1) : d43 p ≤ (2 : Int) + d125 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d43, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1731 p hg
    simpa only [d43, d125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d43, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d43, d125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1761 (p : Pattern) (guard : d1 p = 1) : d44 p ≤ (2 : Int) + d126 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d44, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1759 p hg
    simpa only [d44, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d44, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1760 p hg
    simpa only [d44, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1762 (p : Pattern) (guard : d1 p = 1) : d45 p ≤ (2 : Int) + d127 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d45, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1754 p hg
    simpa only [d45, d127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d45, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1761 p hg
    simpa only [d45, d127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1763 (p : Pattern) (guard : d1 p = 1) : d46 p ≤ (2 : Int) + d124 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d46, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1726 p hg
    simpa only [d46, d124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d46, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d46, d124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1764 (p : Pattern) (guard : d1 p = 1) : d47 p ≤ (2 : Int) + d126 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d47, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1763 p hg
    simpa only [d47, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d47, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1760 p hg
    simpa only [d47, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1765 (p : Pattern) (guard : d1 p = 1) : d48 p ≤ (2 : Int) + d70 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d48, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1738 p hg
    simpa only [d48, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d48, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d48, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1766 (p : Pattern) (guard : d1 p = 1) : d49 p ≤ (2 : Int) + d128 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d49, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1765 p hg
    simpa only [d49, d128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d49, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d49, d128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1767 (p : Pattern) (guard : d1 p = 1) : d50 p ≤ (2 : Int) + d129 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d50, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1764 p hg
    simpa only [d50, d129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d50, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1766 p hg
    simpa only [d50, d129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1768 (p : Pattern) (guard : d1 p = 1) : d51 p ≤ (2 : Int) + d130 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d51, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1762 p hg
    simpa only [d51, d130, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d51, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1767 p hg
    simpa only [d51, d130, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1769 (p : Pattern) (guard : d1 p = 1) : d52 p ≤ (2 : Int) + d131 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d52, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1743 p hg
    simpa only [d52, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d52, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1768 p hg
    simpa only [d52, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1770 (p : Pattern) (guard : d1 p = 1) : d53 p ≤ (2 : Int) + d132 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d53, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1746 p hg
    simpa only [d53, d132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d53, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1747 p hg
    simpa only [d53, d132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1771 (p : Pattern) (guard : d1 p = 1) : d54 p ≤ (2 : Int) + d133 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d54, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1728 p hg
    simpa only [d54, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d54, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1770 p hg
    simpa only [d54, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1772 (p : Pattern) (guard : d1 p = 1) : d55 p ≤ (2 : Int) + d134 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d55, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1733 p hg
    simpa only [d55, d134, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d55, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1740 p hg
    simpa only [d55, d134, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1773 (p : Pattern) (guard : d1 p = 1) : d56 p ≤ (2 : Int) + d135 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d56, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1771 p hg
    simpa only [d56, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d56, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1772 p hg
    simpa only [d56, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1774 (p : Pattern) (guard : d1 p = 1) : d10 p ≤ (2 : Int) + d11 p := by
  change (10 : Int) ≤ (2 : Int) + 11
  decide
theorem compare1775 (p : Pattern) (guard : d1 p = 1) : d57 p ≤ (2 : Int) + d39 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d57, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1774 p hg
    simpa only [d57, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d57, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d57, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1776 (p : Pattern) (guard : d1 p = 1) : d58 p ≤ (2 : Int) + d40 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d58, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1774 p hg
    simpa only [d58, d40, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d58, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1775 p hg
    simpa only [d58, d40, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1777 (p : Pattern) (guard : d1 p = 1) : d59 p ≤ (2 : Int) + d41 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d59, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1776 p hg
    simpa only [d59, d41, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d59, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d59, d41, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1778 (p : Pattern) (guard : d1 p = 1) : d60 p ≤ (2 : Int) + d62 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d60, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1776 p hg
    simpa only [d60, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d60, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1777 p hg
    simpa only [d60, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1779 (p : Pattern) (guard : d1 p = 1) : d61 p ≤ (2 : Int) + d136 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d61, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1733 p hg
    simpa only [d61, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d61, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1778 p hg
    simpa only [d61, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1780 (p : Pattern) (guard : d1 p = 1) : d62 p ≤ (2 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1757 p hg
    simpa only [d62, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1758 p hg
    simpa only [d62, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1781 (p : Pattern) (guard : d1 p = 1) : d63 p ≤ (2 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1780 p hg
    simpa only [d63, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d63, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1782 (p : Pattern) (guard : d1 p = 1) : d64 p ≤ (2 : Int) + d137 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d64, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1779 p hg
    simpa only [d64, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d64, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1781 p hg
    simpa only [d64, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1783 (p : Pattern) (guard : d1 p = 1) : d65 p ≤ (2 : Int) + d138 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d65, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1773 p hg
    simpa only [d65, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d65, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1782 p hg
    simpa only [d65, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1784 (p : Pattern) (guard : d1 p = 1) : d66 p ≤ (2 : Int) + d139 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d66, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1746 p hg
    simpa only [d66, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d66, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d66, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1785 (p : Pattern) (guard : d1 p = 1) : d67 p ≤ (2 : Int) + d140 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d67, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1753 p hg
    simpa only [d67, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d67, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1784 p hg
    simpa only [d67, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1786 (p : Pattern) (guard : d1 p = 1) : d68 p ≤ (2 : Int) + d141 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d68, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1760 p hg
    simpa only [d68, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d68, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1765 p hg
    simpa only [d68, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1787 (p : Pattern) (guard : d1 p = 1) : d69 p ≤ (2 : Int) + d142 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d69, d142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1785 p hg
    simpa only [d69, d142, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d69, d142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1786 p hg
    simpa only [d69, d142, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1788 (p : Pattern) (guard : d1 p = 1) : d70 p ≤ (2 : Int) + d72 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d70, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1776 p hg
    simpa only [d70, d72, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d70, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d70, d72, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1789 (p : Pattern) (guard : d1 p = 1) : d71 p ≤ (2 : Int) + d143 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d71, d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1760 p hg
    simpa only [d71, d143, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d71, d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1788 p hg
    simpa only [d71, d143, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1790 (p : Pattern) (guard : d1 p = 1) : d72 p ≤ (2 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1757 p hg
    simpa only [d72, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d72, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1791 (p : Pattern) (guard : d1 p = 1) : d73 p ≤ (2 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1790 p hg
    simpa only [d73, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d73, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1792 (p : Pattern) (guard : d1 p = 1) : d74 p ≤ (2 : Int) + d144 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d74, d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1789 p hg
    simpa only [d74, d144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d74, d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1791 p hg
    simpa only [d74, d144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1793 (p : Pattern) (guard : d1 p = 1) : d75 p ≤ (2 : Int) + d145 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d75, d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1787 p hg
    simpa only [d75, d145, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d75, d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1792 p hg
    simpa only [d75, d145, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1794 (p : Pattern) (guard : d1 p = 1) : d76 p ≤ (2 : Int) + d146 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d76, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1783 p hg
    simpa only [d76, d146, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d76, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1793 p hg
    simpa only [d76, d146, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1795 (p : Pattern) (guard : d1 p = 1) : d77 p ≤ (2 : Int) + d147 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d77, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1769 p hg
    simpa only [d77, d147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d77, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1794 p hg
    simpa only [d77, d147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1796 (p : Pattern) (guard : d1 p = 1) : d78 p ≤ (2 : Int) + d148 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d78, d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1751 p hg
    simpa only [d78, d148, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d78, d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1752 p hg
    simpa only [d78, d148, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1797 (p : Pattern) (guard : d1 p = 1) : d79 p ≤ (2 : Int) + d149 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d79, d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1770 p hg
    simpa only [d79, d149, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d79, d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1796 p hg
    simpa only [d79, d149, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1798 (p : Pattern) (guard : d1 p = 1) : d80 p ≤ (2 : Int) + d150 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d80, d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1797 p hg
    simpa only [d80, d150, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d80, d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1781 p hg
    simpa only [d80, d150, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1799 (p : Pattern) (guard : d1 p = 1) : d81 p ≤ (2 : Int) + d151 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d81, d151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1798 p hg
    simpa only [d81, d151, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d81, d151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d81, d151, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1800 (p : Pattern) (guard : d1 p = 1) : d82 p ≤ (2 : Int) + d152 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d82, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1743 p hg
    simpa only [d82, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d82, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1799 p hg
    simpa only [d82, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1801 (p : Pattern) (guard : d1 p = 1) : d83 p ≤ (2 : Int) + d153 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d83, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1796 p hg
    simpa only [d83, d153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d83, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d83, d153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1802 (p : Pattern) (guard : d1 p = 1) : d84 p ≤ (2 : Int) + d154 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d84, d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1801 p hg
    simpa only [d84, d154, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d84, d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d84, d154, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1803 (p : Pattern) (guard : d1 p = 1) : d85 p ≤ (2 : Int) + d155 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d85, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1802 p hg
    simpa only [d85, d155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d85, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d85, d155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1804 (p : Pattern) (guard : d1 p = 1) : d86 p ≤ (2 : Int) + d156 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d86, d156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1783 p hg
    simpa only [d86, d156, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d86, d156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1803 p hg
    simpa only [d86, d156, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1805 (p : Pattern) (guard : d1 p = 1) : d87 p ≤ (2 : Int) + d157 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d87, d157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1800 p hg
    simpa only [d87, d157, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d87, d157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1804 p hg
    simpa only [d87, d157, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1806 (p : Pattern) (guard : d1 p = 1) : d88 p ≤ (2 : Int) + d158 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d88, d158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1795 p hg
    simpa only [d88, d158, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d88, d158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1805 p hg
    simpa only [d88, d158, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1807 (p : Pattern) (guard : d1 p = 1) : d89 p ≤ (2 : Int) + d112 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d89, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1740 p hg
    simpa only [d89, d112, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d89, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1780 p hg
    simpa only [d89, d112, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1808 (p : Pattern) (guard : d1 p = 1) : d90 p ≤ (2 : Int) + d159 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d90, d159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1807 p hg
    simpa only [d90, d159, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d90, d159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1781 p hg
    simpa only [d90, d159, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1809 (p : Pattern) (guard : d1 p = 1) : d91 p ≤ (2 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1781 p hg
    simpa only [d91, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d91, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1810 (p : Pattern) (guard : d1 p = 1) : d92 p ≤ (2 : Int) + d160 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d92, d160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1808 p hg
    simpa only [d92, d160, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d92, d160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1809 p hg
    simpa only [d92, d160, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1811 (p : Pattern) (guard : d1 p = 1) : d93 p ≤ (2 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1809 p hg
    simpa only [d93, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d93, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1812 (p : Pattern) (guard : d1 p = 1) : d94 p ≤ (2 : Int) + d161 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d94, d161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1810 p hg
    simpa only [d94, d161, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d94, d161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1811 p hg
    simpa only [d94, d161, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1813 (p : Pattern) (guard : d1 p = 1) : d95 p ≤ (2 : Int) + d12 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1811 p hg
    simpa only [d95, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d95, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1814 (p : Pattern) (guard : d1 p = 1) : d96 p ≤ (2 : Int) + d162 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d96, d162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1812 p hg
    simpa only [d96, d162, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d96, d162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1813 p hg
    simpa only [d96, d162, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1815 (p : Pattern) (guard : d1 p = 1) : d97 p ≤ (2 : Int) + d163 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d97, d163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1805 p hg
    simpa only [d97, d163, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d97, d163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1814 p hg
    simpa only [d97, d163, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1816 (p : Pattern) (guard : d1 p = 1) : d98 p ≤ (2 : Int) + d164 p := by
  cases selected : p 116 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d98, d164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1806 p hg
    simpa only [d98, d164, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d98, d164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1815 p hg
    simpa only [d98, d164, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1817 (p : Pattern) (guard : d0 p = 1) : d426 p ≤ (2 : Int) + d166 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1818 (p : Pattern) (guard : d4058 p = 1) : d489 p ≤ (2 : Int) + d167 p := by
  cases selected : p 115 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4058, d489, d167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1816 p hg
    simpa only [d4058, d489, d167, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4058, d489, d167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1817 p hg
    simpa only [d4058, d489, d167, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1819 (p : Pattern) (guard : d0 p = 1) : d492 p ≤ (2 : Int) + d167 p := by
  change (0 : Int) = 1 at guard
  omega
end NetHack.Sokoban22Refined85
