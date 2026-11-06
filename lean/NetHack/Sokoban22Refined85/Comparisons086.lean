/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons085
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare12040 (p : Pattern) (guard : d4471 p = 1) : d1636 p ≤ (0 : Int) + d765 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4471 p = 1 := by simpa only [d1636, d765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12038 p hg
    simpa only [d1636, d765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4471 p = 1 := by simpa only [d1636, d765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5563 p hg
    simpa only [d1636, d765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12041 (p : Pattern) (guard : d4471 p = 1) : d1637 p ≤ (0 : Int) + d766 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4471 p = 1 := by simpa only [d1637, d766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12039 p hg
    simpa only [d1637, d766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4471 p = 1 := by simpa only [d1637, d766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12040 p hg
    simpa only [d1637, d766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12042 (p : Pattern) (guard : d4471 p = 1) : d1638 p ≤ (0 : Int) + d767 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4471 p = 1 := by simpa only [d1638, d767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11949 p hg
    simpa only [d1638, d767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4471 p = 1 := by simpa only [d1638, d767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12041 p hg
    simpa only [d1638, d767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12043 (p : Pattern) (guard : d4471 p = 1) : d1639 p ≤ (0 : Int) + d768 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4471 p = 1 := by simpa only [d1639, d768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11933 p hg
    simpa only [d1639, d768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4471 p = 1 := by simpa only [d1639, d768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12042 p hg
    simpa only [d1639, d768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12044 (p : Pattern) (guard : d4206 p = 1) : d215 p ≤ (0 : Int) + d211 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d215, d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11965 p hg
    simpa only [d215, d211, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d215, d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d215, d211, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12045 (p : Pattern) (guard : d4206 p = 1) : d1640 p ≤ (0 : Int) + d212 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1640, d212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11976 p hg
    simpa only [d1640, d212, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1640, d212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12044 p hg
    simpa only [d1640, d212, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12046 (p : Pattern) (guard : d4206 p = 1) : d217 p ≤ (0 : Int) + d213 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d217, d213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12044 p hg
    simpa only [d217, d213, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d217, d213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d217, d213, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12047 (p : Pattern) (guard : d4206 p = 1) : d1641 p ≤ (0 : Int) + d214 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1641, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12045 p hg
    simpa only [d1641, d214, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1641, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12046 p hg
    simpa only [d1641, d214, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12048 (p : Pattern) (guard : d0 p = 1) : d1643 p ≤ (0 : Int) + d409 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12049 (p : Pattern) (guard : d4471 p = 1) : d1644 p ≤ (0 : Int) + d769 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4471, d1644, d769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12047 p hg
    simpa only [d4471, d1644, d769, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4471, d1644, d769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12048 p hg
    simpa only [d4471, d1644, d769, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12050 (p : Pattern) (guard : d4471 p = 1) : d1645 p ≤ (0 : Int) + d770 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4471 p = 1 := by simpa only [d1645, d770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11972 p hg
    simpa only [d1645, d770, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4471 p = 1 := by simpa only [d1645, d770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12049 p hg
    simpa only [d1645, d770, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12051 (p : Pattern) (guard : d4206 p = 1) : d1642 p ≤ (0 : Int) + d212 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1642, d212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11989 p hg
    simpa only [d1642, d212, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1642, d212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12044 p hg
    simpa only [d1642, d212, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12052 (p : Pattern) (guard : d4206 p = 1) : d1643 p ≤ (0 : Int) + d214 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1643, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12051 p hg
    simpa only [d1643, d214, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1643, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12046 p hg
    simpa only [d1643, d214, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12053 (p : Pattern) (guard : d4471 p = 1) : d1646 p ≤ (0 : Int) + d771 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4471, d1646, d771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12052 p hg
    simpa only [d4471, d1646, d771, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4471, d1646, d771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11992 p hg
    simpa only [d4471, d1646, d771, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12054 (p : Pattern) (guard : d4471 p = 1) : d1647 p ≤ (0 : Int) + d772 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4471 p = 1 := by simpa only [d1647, d772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11988 p hg
    simpa only [d1647, d772, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4471 p = 1 := by simpa only [d1647, d772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12053 p hg
    simpa only [d1647, d772, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12055 (p : Pattern) (guard : d4471 p = 1) : d1648 p ≤ (0 : Int) + d773 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4471 p = 1 := by simpa only [d1648, d773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12050 p hg
    simpa only [d1648, d773, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4471 p = 1 := by simpa only [d1648, d773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12054 p hg
    simpa only [d1648, d773, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12056 (p : Pattern) (guard : d4471 p = 1) : d1647 p ≤ (0 : Int) + d774 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4471 p = 1 := by simpa only [d1647, d774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11997 p hg
    simpa only [d1647, d774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4471 p = 1 := by simpa only [d1647, d774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12053 p hg
    simpa only [d1647, d774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12057 (p : Pattern) (guard : d4471 p = 1) : d1649 p ≤ (0 : Int) + d775 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4471 p = 1 := by simpa only [d1649, d775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12056 p hg
    simpa only [d1649, d775, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4471 p = 1 := by simpa only [d1649, d775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12002 p hg
    simpa only [d1649, d775, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12058 (p : Pattern) (guard : d4471 p = 1) : d1650 p ≤ (0 : Int) + d776 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4471 p = 1 := by simpa only [d1650, d776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12055 p hg
    simpa only [d1650, d776, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4471 p = 1 := by simpa only [d1650, d776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12057 p hg
    simpa only [d1650, d776, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12059 (p : Pattern) (guard : d0 p = 1) : d1652 p ≤ (0 : Int) + d405 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12060 (p : Pattern) (guard : d4471 p = 1) : d1653 p ≤ (0 : Int) + d753 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4471, d1653, d753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12007 p hg
    simpa only [d4471, d1653, d753, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4471, d1653, d753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12059 p hg
    simpa only [d4471, d1653, d753, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12061 (p : Pattern) (guard : d0 p = 1) : d1655 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12062 (p : Pattern) (guard : d4471 p = 1) : d1656 p ≤ (0 : Int) + d771 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4471, d1656, d771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12052 p hg
    simpa only [d4471, d1656, d771, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4471, d1656, d771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12061 p hg
    simpa only [d4471, d1656, d771, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12063 (p : Pattern) (guard : d4471 p = 1) : d1657 p ≤ (0 : Int) + d777 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4471 p = 1 := by simpa only [d1657, d777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12060 p hg
    simpa only [d1657, d777, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4471 p = 1 := by simpa only [d1657, d777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12062 p hg
    simpa only [d1657, d777, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12064 (p : Pattern) (guard : d4206 p = 1) : d1658 p ≤ (0 : Int) + d241 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1658, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11975 p hg
    simpa only [d1658, d241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1658, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11884 p hg
    simpa only [d1658, d241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12065 (p : Pattern) (guard : d4206 p = 1) : d1659 p ≤ (0 : Int) + d242 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1659, d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11964 p hg
    simpa only [d1659, d242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1659, d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12064 p hg
    simpa only [d1659, d242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12066 (p : Pattern) (guard : d4206 p = 1) : d1660 p ≤ (0 : Int) + d243 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1660, d243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12065 p hg
    simpa only [d1660, d243, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1660, d243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11980 p hg
    simpa only [d1660, d243, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12067 (p : Pattern) (guard : d4471 p = 1) : d1661 p ≤ (0 : Int) + d778 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4471, d1661, d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12066 p hg
    simpa only [d4471, d1661, d778, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4471, d1661, d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11992 p hg
    simpa only [d4471, d1661, d778, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12068 (p : Pattern) (guard : d4206 p = 1) : d1651 p ≤ (0 : Int) + d245 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1651, d245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11975 p hg
    simpa only [d1651, d245, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1651, d245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12044 p hg
    simpa only [d1651, d245, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12069 (p : Pattern) (guard : d4206 p = 1) : d229 p ≤ (0 : Int) + d148 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d229, d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3159 p hg
    simpa only [d4206, d229, d148, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d229, d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3161 p hg
    simpa only [d4206, d229, d148, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12070 (p : Pattern) (guard : d4206 p = 1) : d230 p ≤ (0 : Int) + d153 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d230, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12069 p hg
    simpa only [d230, d153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d230, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d230, d153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12071 (p : Pattern) (guard : d4206 p = 1) : d231 p ≤ (0 : Int) + d154 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d231, d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12070 p hg
    simpa only [d231, d154, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d231, d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d231, d154, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12072 (p : Pattern) (guard : d4206 p = 1) : d1652 p ≤ (0 : Int) + d246 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1652, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12068 p hg
    simpa only [d1652, d246, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1652, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12071 p hg
    simpa only [d1652, d246, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12073 (p : Pattern) (guard : d0 p = 1) : d1662 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12074 (p : Pattern) (guard : d4471 p = 1) : d1663 p ≤ (0 : Int) + d779 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4471, d1663, d779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12072 p hg
    simpa only [d4471, d1663, d779, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4471, d1663, d779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12073 p hg
    simpa only [d4471, d1663, d779, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12075 (p : Pattern) (guard : d4471 p = 1) : d1664 p ≤ (0 : Int) + d780 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4471 p = 1 := by simpa only [d1664, d780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12067 p hg
    simpa only [d1664, d780, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4471 p = 1 := by simpa only [d1664, d780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12074 p hg
    simpa only [d1664, d780, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12076 (p : Pattern) (guard : d4471 p = 1) : d1665 p ≤ (0 : Int) + d781 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4471 p = 1 := by simpa only [d1665, d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12063 p hg
    simpa only [d1665, d781, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4471 p = 1 := by simpa only [d1665, d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12075 p hg
    simpa only [d1665, d781, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12077 (p : Pattern) (guard : d4206 p = 1) : d1666 p ≤ (0 : Int) + d252 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1666, d252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11975 p hg
    simpa only [d1666, d252, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1666, d252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11870 p hg
    simpa only [d1666, d252, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12078 (p : Pattern) (guard : d4206 p = 1) : d1667 p ≤ (0 : Int) + d253 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1667, d253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11964 p hg
    simpa only [d1667, d253, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1667, d253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12077 p hg
    simpa only [d1667, d253, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12079 (p : Pattern) (guard : d4206 p = 1) : d1668 p ≤ (0 : Int) + d254 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1668, d254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11965 p hg
    simpa only [d1668, d254, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1668, d254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11870 p hg
    simpa only [d1668, d254, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12080 (p : Pattern) (guard : d4206 p = 1) : d1669 p ≤ (0 : Int) + d255 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1669, d255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12079 p hg
    simpa only [d1669, d255, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1669, d255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d1669, d255, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12081 (p : Pattern) (guard : d4206 p = 1) : d1670 p ≤ (0 : Int) + d256 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1670, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12078 p hg
    simpa only [d1670, d256, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1670, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12080 p hg
    simpa only [d1670, d256, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12082 (p : Pattern) (guard : d0 p = 1) : d1673 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12083 (p : Pattern) (guard : d4471 p = 1) : d1674 p ≤ (0 : Int) + d782 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4471, d1674, d782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12081 p hg
    simpa only [d4471, d1674, d782, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4471, d1674, d782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12082 p hg
    simpa only [d4471, d1674, d782, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12084 (p : Pattern) (guard : d4471 p = 1) : d1675 p ≤ (0 : Int) + d783 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4471 p = 1 := by simpa only [d1675, d783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12083 p hg
    simpa only [d1675, d783, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4471 p = 1 := by simpa only [d1675, d783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12074 p hg
    simpa only [d1675, d783, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12085 (p : Pattern) (guard : d4471 p = 1) : d1676 p ≤ (0 : Int) + d784 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4471 p = 1 := by simpa only [d1676, d784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12084 p hg
    simpa only [d1676, d784, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4471 p = 1 := by simpa only [d1676, d784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5563 p hg
    simpa only [d1676, d784, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12086 (p : Pattern) (guard : d4471 p = 1) : d1677 p ≤ (0 : Int) + d785 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4471 p = 1 := by simpa only [d1677, d785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12076 p hg
    simpa only [d1677, d785, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4471 p = 1 := by simpa only [d1677, d785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12085 p hg
    simpa only [d1677, d785, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12087 (p : Pattern) (guard : d4471 p = 1) : d1678 p ≤ (0 : Int) + d786 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4471 p = 1 := by simpa only [d1678, d786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12058 p hg
    simpa only [d1678, d786, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4471 p = 1 := by simpa only [d1678, d786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12086 p hg
    simpa only [d1678, d786, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12088 (p : Pattern) (guard : d4471 p = 1) : d1679 p ≤ (0 : Int) + d787 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4471 p = 1 := by simpa only [d1679, d787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11933 p hg
    simpa only [d1679, d787, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4471 p = 1 := by simpa only [d1679, d787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12087 p hg
    simpa only [d1679, d787, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12089 (p : Pattern) (guard : d4471 p = 1) : d1680 p ≤ (0 : Int) + d788 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4471 p = 1 := by simpa only [d1680, d788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12043 p hg
    simpa only [d1680, d788, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4471 p = 1 := by simpa only [d1680, d788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12088 p hg
    simpa only [d1680, d788, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12090 (p : Pattern) (guard : d4471 p = 1) : d1681 p ≤ (0 : Int) + d789 p := by
  cases selected : p 48 with
  | false =>
    have hg : d4471 p = 1 := by simpa only [d1681, d789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12018 p hg
    simpa only [d1681, d789, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4471 p = 1 := by simpa only [d1681, d789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12089 p hg
    simpa only [d1681, d789, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12091 (p : Pattern) (guard : d0 p = 1) : d1510 p ≤ (2 : Int) + d29 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12092 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (2 : Int) + d15 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12093 (p : Pattern) (guard : d4206 p = 1) : d46 p ≤ (2 : Int) + d16 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d46, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4688 p hg
    simpa only [d4206, d46, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d46, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12092 p hg
    simpa only [d4206, d46, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12094 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (2 : Int) + d19 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12095 (p : Pattern) (guard : d4206 p = 1) : d43 p ≤ (2 : Int) + d20 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d43, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7129 p hg
    simpa only [d4206, d43, d20, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d43, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12094 p hg
    simpa only [d4206, d43, d20, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12096 (p : Pattern) (guard : d4206 p = 1) : d47 p ≤ (2 : Int) + d21 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d47, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12093 p hg
    simpa only [d47, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d47, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12095 p hg
    simpa only [d47, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12097 (p : Pattern) (guard : d4206 p = 1) : d1511 p ≤ (2 : Int) + d22 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1511, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12093 p hg
    simpa only [d1511, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1511, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12096 p hg
    simpa only [d1511, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12098 (p : Pattern) (guard : d1 p = 1) : d24 p ≤ (2 : Int) + d24 p := by
  omega
theorem compare12099 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (2 : Int) + d25 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12100 (p : Pattern) (guard : d4206 p = 1) : d48 p ≤ (2 : Int) + d26 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d48, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12098 p hg
    simpa only [d4206, d48, d26, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d48, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12099 p hg
    simpa only [d4206, d48, d26, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12101 (p : Pattern) (guard : d4206 p = 1) : d12 p ≤ (2 : Int) + d12 p := by
  omega
theorem compare12102 (p : Pattern) (guard : d4206 p = 1) : d49 p ≤ (2 : Int) + d27 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d49, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12100 p hg
    simpa only [d49, d27, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d49, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12101 p hg
    simpa only [d49, d27, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12103 (p : Pattern) (guard : d4206 p = 1) : d50 p ≤ (2 : Int) + d28 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d50, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12096 p hg
    simpa only [d50, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d50, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12102 p hg
    simpa only [d50, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12104 (p : Pattern) (guard : d4206 p = 1) : d1512 p ≤ (2 : Int) + d29 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1512, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12097 p hg
    simpa only [d1512, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1512, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12103 p hg
    simpa only [d1512, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12105 (p : Pattern) (guard : d4207 p = 1) : d1513 p ≤ (2 : Int) + d29 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4207, d1513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12091 p hg
    simpa only [d4207, d1513, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d4207, d1513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12104 p hg
    simpa only [d4207, d1513, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12106 (p : Pattern) (guard : d0 p = 1) : d1517 p ≤ (2 : Int) + d65 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12107 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (2 : Int) + d32 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12108 (p : Pattern) (guard : d4206 p = 1) : d66 p ≤ (2 : Int) + d53 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d66, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7126 p hg
    simpa only [d4206, d66, d53, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d66, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12107 p hg
    simpa only [d4206, d66, d53, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12109 (p : Pattern) (guard : d4206 p = 1) : d1518 p ≤ (2 : Int) + d54 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1518, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12093 p hg
    simpa only [d1518, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1518, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12108 p hg
    simpa only [d1518, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12110 (p : Pattern) (guard : d4206 p = 1) : d68 p ≤ (2 : Int) + d55 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d68, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12095 p hg
    simpa only [d68, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d68, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12100 p hg
    simpa only [d68, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12111 (p : Pattern) (guard : d4206 p = 1) : d1519 p ≤ (2 : Int) + d56 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1519, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12109 p hg
    simpa only [d1519, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1519, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12110 p hg
    simpa only [d1519, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12112 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (2 : Int) + d59 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12113 (p : Pattern) (guard : d4206 p = 1) : d70 p ≤ (2 : Int) + d60 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d70, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2175 p hg
    simpa only [d4206, d70, d60, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d70, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12112 p hg
    simpa only [d4206, d70, d60, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12114 (p : Pattern) (guard : d4206 p = 1) : d71 p ≤ (2 : Int) + d61 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d71, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12095 p hg
    simpa only [d71, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d71, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12113 p hg
    simpa only [d71, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12115 (p : Pattern) (guard : d1 p = 1) : d40 p ≤ (2 : Int) + d40 p := by
  omega
theorem compare12116 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (2 : Int) + d41 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12117 (p : Pattern) (guard : d4206 p = 1) : d72 p ≤ (2 : Int) + d62 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d72, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12115 p hg
    simpa only [d4206, d72, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d72, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12116 p hg
    simpa only [d4206, d72, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12118 (p : Pattern) (guard : d4206 p = 1) : d73 p ≤ (2 : Int) + d63 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d73, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12117 p hg
    simpa only [d73, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d73, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12101 p hg
    simpa only [d73, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12119 (p : Pattern) (guard : d4206 p = 1) : d74 p ≤ (2 : Int) + d64 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d74, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12114 p hg
    simpa only [d74, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d74, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12118 p hg
    simpa only [d74, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12120 (p : Pattern) (guard : d4206 p = 1) : d1520 p ≤ (2 : Int) + d65 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1520, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12111 p hg
    simpa only [d1520, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1520, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12119 p hg
    simpa only [d1520, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12121 (p : Pattern) (guard : d4207 p = 1) : d1521 p ≤ (2 : Int) + d65 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4207, d1521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12106 p hg
    simpa only [d4207, d1521, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d4207, d1521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12120 p hg
    simpa only [d4207, d1521, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12122 (p : Pattern) (guard : d4207 p = 1) : d1522 p ≤ (2 : Int) + d4729 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4207 p = 1 := by simpa only [d1522, d4729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12105 p hg
    simpa only [d1522, d4729, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4207 p = 1 := by simpa only [d1522, d4729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12121 p hg
    simpa only [d1522, d4729, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12123 (p : Pattern) (guard : d0 p = 1) : d1527 p ≤ (2 : Int) + d4729 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12124 (p : Pattern) (guard : d4208 p = 1) : d1528 p ≤ (2 : Int) + d4729 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4207 p = 1 := by simpa only [d4208, d1528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12122 p hg
    simpa only [d4208, d1528, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4208, d1528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12123 p hg
    simpa only [d4208, d1528, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12125 (p : Pattern) (guard : d0 p = 1) : d1531 p ≤ (2 : Int) + d92 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12126 (p : Pattern) (guard : d4206 p = 1) : d66 p ≤ (2 : Int) + d26 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d66, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4838 p hg
    simpa only [d4206, d66, d26, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d66, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12099 p hg
    simpa only [d4206, d66, d26, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12127 (p : Pattern) (guard : d4206 p = 1) : d173 p ≤ (2 : Int) + d62 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d173, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4856 p hg
    simpa only [d4206, d173, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d173, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12116 p hg
    simpa only [d4206, d173, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12128 (p : Pattern) (guard : d4206 p = 1) : d176 p ≤ (2 : Int) + d89 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d176, d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12126 p hg
    simpa only [d176, d89, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d176, d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12127 p hg
    simpa only [d176, d89, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12129 (p : Pattern) (guard : d4206 p = 1) : d177 p ≤ (2 : Int) + d90 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d177, d90, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12128 p hg
    simpa only [d177, d90, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d177, d90, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12118 p hg
    simpa only [d177, d90, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12130 (p : Pattern) (guard : d4206 p = 1) : d12 p ≤ (2 : Int) + d62 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4731 p hg
    simpa only [d4206, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12116 p hg
    simpa only [d4206, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12131 (p : Pattern) (guard : d4206 p = 1) : d12 p ≤ (2 : Int) + d63 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12130 p hg
    simpa only [d63, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12101 p hg
    simpa only [d63, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12132 (p : Pattern) (guard : d4206 p = 1) : d12 p ≤ (2 : Int) + d91 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12131 p hg
    simpa only [d91, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12101 p hg
    simpa only [d91, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12133 (p : Pattern) (guard : d4206 p = 1) : d1523 p ≤ (2 : Int) + d92 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1523, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12129 p hg
    simpa only [d1523, d92, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1523, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12132 p hg
    simpa only [d1523, d92, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12134 (p : Pattern) (guard : d4207 p = 1) : d1532 p ≤ (2 : Int) + d92 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4207, d1532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12125 p hg
    simpa only [d4207, d1532, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d4207, d1532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12133 p hg
    simpa only [d4207, d1532, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12135 (p : Pattern) (guard : d0 p = 1) : d1520 p ≤ (2 : Int) + d93 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12136 (p : Pattern) (guard : d4206 p = 1) : d183 p ≤ (2 : Int) + d63 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d183, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12127 p hg
    simpa only [d183, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d183, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12101 p hg
    simpa only [d183, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12137 (p : Pattern) (guard : d4206 p = 1) : d184 p ≤ (2 : Int) + d91 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d184, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12136 p hg
    simpa only [d184, d91, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d184, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12101 p hg
    simpa only [d184, d91, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12138 (p : Pattern) (guard : d4206 p = 1) : d1525 p ≤ (2 : Int) + d93 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1525, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12137 p hg
    simpa only [d1525, d93, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1525, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12101 p hg
    simpa only [d1525, d93, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12139 (p : Pattern) (guard : d4207 p = 1) : d1526 p ≤ (2 : Int) + d93 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4207, d1526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12135 p hg
    simpa only [d4207, d1526, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d4207, d1526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12138 p hg
    simpa only [d4207, d1526, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12140 (p : Pattern) (guard : d4207 p = 1) : d1533 p ≤ (2 : Int) + d4730 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4207 p = 1 := by simpa only [d1533, d4730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12134 p hg
    simpa only [d1533, d4730, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4207 p = 1 := by simpa only [d1533, d4730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12139 p hg
    simpa only [d1533, d4730, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12141 (p : Pattern) (guard : d0 p = 1) : d1541 p ≤ (2 : Int) + d4730 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12142 (p : Pattern) (guard : d4208 p = 1) : d1542 p ≤ (2 : Int) + d4730 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4207 p = 1 := by simpa only [d4208, d1542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12140 p hg
    simpa only [d4208, d1542, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4208, d1542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12141 p hg
    simpa only [d4208, d1542, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12143 (p : Pattern) (guard : d4208 p = 1) : d1543 p ≤ (2 : Int) + d4968 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4208 p = 1 := by simpa only [d1543, d4968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12124 p hg
    simpa only [d1543, d4968, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4208 p = 1 := by simpa only [d1543, d4968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12142 p hg
    simpa only [d1543, d4968, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12144 (p : Pattern) (guard : d0 p = 1) : d1546 p ≤ (2 : Int) + d29 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12145 (p : Pattern) (guard : d4207 p = 1) : d1547 p ≤ (2 : Int) + d29 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4207, d1547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12144 p hg
    simpa only [d4207, d1547, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d4207, d1547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12104 p hg
    simpa only [d4207, d1547, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12146 (p : Pattern) (guard : d0 p = 1) : d1520 p ≤ (2 : Int) + d65 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12147 (p : Pattern) (guard : d4207 p = 1) : d1520 p ≤ (2 : Int) + d65 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12146 p hg
    simpa only [d4207, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d4207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12120 p hg
    simpa only [d4207, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12148 (p : Pattern) (guard : d4207 p = 1) : d1548 p ≤ (2 : Int) + d4729 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4207 p = 1 := by simpa only [d1548, d4729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12145 p hg
    simpa only [d1548, d4729, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4207 p = 1 := by simpa only [d1548, d4729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12147 p hg
    simpa only [d1548, d4729, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12149 (p : Pattern) (guard : d4208 p = 1) : d1549 p ≤ (2 : Int) + d4729 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4207 p = 1 := by simpa only [d4208, d1549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12148 p hg
    simpa only [d4208, d1549, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4208, d1549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12123 p hg
    simpa only [d4208, d1549, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12150 (p : Pattern) (guard : d0 p = 1) : d1512 p ≤ (2 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12151 (p : Pattern) (guard : d1 p = 1) : d2 p ≤ (2 : Int) + d12 p := by
  change (2 : Int) ≤ (2 : Int) + 12
  decide
theorem compare12152 (p : Pattern) (guard : d1 p = 1) : d30 p ≤ (2 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12151 p hg
    simpa only [d30, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d30, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12153 (p : Pattern) (guard : d1 p = 1) : d31 p ≤ (2 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12151 p hg
    simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12152 p hg
    simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12154 (p : Pattern) (guard : d4206 p = 1) : d66 p ≤ (2 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12153 p hg
    simpa only [d4206, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6043 p hg
    simpa only [d4206, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12155 (p : Pattern) (guard : d4206 p = 1) : d173 p ≤ (2 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4842 p hg
    simpa only [d4206, d173, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6043 p hg
    simpa only [d4206, d173, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12156 (p : Pattern) (guard : d4206 p = 1) : d176 p ≤ (2 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12154 p hg
    simpa only [d176, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12155 p hg
    simpa only [d176, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12157 (p : Pattern) (guard : d4206 p = 1) : d72 p ≤ (2 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1757 p hg
    simpa only [d4206, d72, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6043 p hg
    simpa only [d4206, d72, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12158 (p : Pattern) (guard : d4206 p = 1) : d73 p ≤ (2 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12157 p hg
    simpa only [d73, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12101 p hg
    simpa only [d73, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12159 (p : Pattern) (guard : d4206 p = 1) : d177 p ≤ (2 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12156 p hg
    simpa only [d177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12158 p hg
    simpa only [d177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12160 (p : Pattern) (guard : d4206 p = 1) : d1523 p ≤ (2 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12159 p hg
    simpa only [d1523, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12101 p hg
    simpa only [d1523, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12161 (p : Pattern) (guard : d4207 p = 1) : d1524 p ≤ (2 : Int) + d12 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4207, d1524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12150 p hg
    simpa only [d4207, d1524, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d4207, d1524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12160 p hg
    simpa only [d4207, d1524, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12162 (p : Pattern) (guard : d0 p = 1) : d1520 p ≤ (2 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12163 (p : Pattern) (guard : d4206 p = 1) : d183 p ≤ (2 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12155 p hg
    simpa only [d183, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12101 p hg
    simpa only [d183, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12164 (p : Pattern) (guard : d4206 p = 1) : d184 p ≤ (2 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12163 p hg
    simpa only [d184, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12101 p hg
    simpa only [d184, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12165 (p : Pattern) (guard : d4206 p = 1) : d1525 p ≤ (2 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12164 p hg
    simpa only [d1525, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12101 p hg
    simpa only [d1525, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12166 (p : Pattern) (guard : d4207 p = 1) : d1526 p ≤ (2 : Int) + d12 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4207, d1526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12162 p hg
    simpa only [d4207, d1526, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d4207, d1526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12165 p hg
    simpa only [d4207, d1526, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12167 (p : Pattern) (guard : d4207 p = 1) : d1527 p ≤ (2 : Int) + d12 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4207 p = 1 := by simpa only [d1527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12161 p hg
    simpa only [d1527, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4207 p = 1 := by simpa only [d1527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12166 p hg
    simpa only [d1527, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12168 (p : Pattern) (guard : d4208 p = 1) : d1550 p ≤ (2 : Int) + d12 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4207 p = 1 := by simpa only [d4208, d1550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12167 p hg
    simpa only [d4208, d1550, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4208, d1550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6043 p hg
    simpa only [d4208, d1550, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12169 (p : Pattern) (guard : d4208 p = 1) : d1551 p ≤ (2 : Int) + d4969 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4208 p = 1 := by simpa only [d1551, d4969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12149 p hg
    simpa only [d1551, d4969, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4208 p = 1 := by simpa only [d1551, d4969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12168 p hg
    simpa only [d1551, d4969, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12170 (p : Pattern) (guard : d4208 p = 1) : d1552 p ≤ (2 : Int) + d4970 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4208 p = 1 := by simpa only [d1552, d4970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12143 p hg
    simpa only [d1552, d4970, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4208 p = 1 := by simpa only [d1552, d4970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12169 p hg
    simpa only [d1552, d4970, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12171 (p : Pattern) (guard : d0 p = 1) : d1556 p ≤ (2 : Int) + d29 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12172 (p : Pattern) (guard : d4207 p = 1) : d1557 p ≤ (2 : Int) + d29 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4207, d1557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12171 p hg
    simpa only [d4207, d1557, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d4207, d1557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12104 p hg
    simpa only [d4207, d1557, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12173 (p : Pattern) (guard : d0 p = 1) : d1560 p ≤ (2 : Int) + d65 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12174 (p : Pattern) (guard : d4207 p = 1) : d1561 p ≤ (2 : Int) + d65 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4207, d1561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12173 p hg
    simpa only [d4207, d1561, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d4207, d1561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12120 p hg
    simpa only [d4207, d1561, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12175 (p : Pattern) (guard : d4207 p = 1) : d1562 p ≤ (2 : Int) + d4729 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4207 p = 1 := by simpa only [d1562, d4729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12172 p hg
    simpa only [d1562, d4729, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4207 p = 1 := by simpa only [d1562, d4729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12174 p hg
    simpa only [d1562, d4729, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12176 (p : Pattern) (guard : d4208 p = 1) : d1563 p ≤ (2 : Int) + d4729 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4207 p = 1 := by simpa only [d4208, d1563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12175 p hg
    simpa only [d4208, d1563, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4208, d1563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12123 p hg
    simpa only [d4208, d1563, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12177 (p : Pattern) (guard : d0 p = 1) : d1512 p ≤ (2 : Int) + d92 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12178 (p : Pattern) (guard : d4207 p = 1) : d1524 p ≤ (2 : Int) + d92 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4207, d1524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12177 p hg
    simpa only [d4207, d1524, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d4207, d1524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12133 p hg
    simpa only [d4207, d1524, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12179 (p : Pattern) (guard : d4207 p = 1) : d1527 p ≤ (2 : Int) + d4730 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4207 p = 1 := by simpa only [d1527, d4730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12178 p hg
    simpa only [d1527, d4730, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4207 p = 1 := by simpa only [d1527, d4730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12139 p hg
    simpa only [d1527, d4730, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
