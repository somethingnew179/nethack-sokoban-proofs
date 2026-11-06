/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Comparisons056
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare7980 (p : Pattern) (guard : d1690 p = 1) : d11 p ≤ (0 : Int) + d11 p := by
  omega
theorem compare7981 (p : Pattern) (guard : d1690 p = 1) : d11 p ≤ (0 : Int) + d1693 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d1693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7979 p hg
    simpa only [d1693, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d1693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7980 p hg
    simpa only [d1693, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7982 (p : Pattern) (guard : d1690 p = 1) : d39 p ≤ (0 : Int) + d1556 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d39, d1556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7979 p hg
    simpa only [d39, d1556, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d39, d1556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7975 p hg
    simpa only [d39, d1556, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7983 (p : Pattern) (guard : d1690 p = 1) : d698 p ≤ (0 : Int) + d1694 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d698, d1694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7981 p hg
    simpa only [d698, d1694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d698, d1694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7982 p hg
    simpa only [d698, d1694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7984 (p : Pattern) (guard : d1690 p = 1) : d699 p ≤ (0 : Int) + d1695 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d699, d1695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7977 p hg
    simpa only [d699, d1695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d699, d1695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7983 p hg
    simpa only [d699, d1695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7985 (p : Pattern) (guard : d1690 p = 1) : d700 p ≤ (0 : Int) + d1696 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d700, d1696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7977 p hg
    simpa only [d700, d1696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d700, d1696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7984 p hg
    simpa only [d700, d1696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7986 (p : Pattern) (guard : d1690 p = 1) : d37 p ≤ (0 : Int) + d37 p := by
  omega
theorem compare7987 (p : Pattern) (guard : d1690 p = 1) : d697 p ≤ (0 : Int) + d1697 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d697, d1697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7974 p hg
    simpa only [d697, d1697, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d697, d1697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7986 p hg
    simpa only [d697, d1697, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7988 (p : Pattern) (guard : d1690 p = 1) : d39 p ≤ (0 : Int) + d39 p := by
  omega
theorem compare7989 (p : Pattern) (guard : d1690 p = 1) : d698 p ≤ (0 : Int) + d1698 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d698, d1698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7981 p hg
    simpa only [d698, d1698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d698, d1698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7988 p hg
    simpa only [d698, d1698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7990 (p : Pattern) (guard : d1690 p = 1) : d699 p ≤ (0 : Int) + d1699 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d699, d1699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7987 p hg
    simpa only [d699, d1699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d699, d1699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7989 p hg
    simpa only [d699, d1699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7991 (p : Pattern) (guard : d1690 p = 1) : d700 p ≤ (0 : Int) + d1700 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d700, d1700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7987 p hg
    simpa only [d700, d1700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d700, d1700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7990 p hg
    simpa only [d700, d1700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7992 (p : Pattern) (guard : d1690 p = 1) : d700 p ≤ (0 : Int) + d1701 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d1701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7985 p hg
    simpa only [d1701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d1701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7991 p hg
    simpa only [d1701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7993 (p : Pattern) (guard : d1690 p = 1) : d700 p ≤ (0 : Int) + d1702 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d1702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7985 p hg
    simpa only [d1702, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d1702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7992 p hg
    simpa only [d1702, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7994 (p : Pattern) (guard : d1690 p = 1) : d700 p ≤ (0 : Int) + d1703 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d1703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7992 p hg
    simpa only [d1703, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d1703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7991 p hg
    simpa only [d1703, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7995 (p : Pattern) (guard : d1690 p = 1) : d700 p ≤ (0 : Int) + d1704 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d1704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7993 p hg
    simpa only [d1704, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d1704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7994 p hg
    simpa only [d1704, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7996 (p : Pattern) (guard : d1690 p = 1) : d699 p ≤ (0 : Int) + d1705 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d1705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7984 p hg
    simpa only [d1705, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d1705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7990 p hg
    simpa only [d1705, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7997 (p : Pattern) (guard : d1690 p = 1) : d699 p ≤ (0 : Int) + d1706 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d1706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7984 p hg
    simpa only [d1706, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d1706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7996 p hg
    simpa only [d1706, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7998 (p : Pattern) (guard : d1690 p = 1) : d699 p ≤ (0 : Int) + d1707 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d1707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7996 p hg
    simpa only [d1707, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d1707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7990 p hg
    simpa only [d1707, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7999 (p : Pattern) (guard : d1690 p = 1) : d699 p ≤ (0 : Int) + d1708 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d1708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7997 p hg
    simpa only [d1708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d1708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7998 p hg
    simpa only [d1708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8000 (p : Pattern) (guard : d1690 p = 1) : d701 p ≤ (0 : Int) + d1709 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d701, d1709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7977 p hg
    simpa only [d701, d1709, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d701, d1709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7975 p hg
    simpa only [d701, d1709, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8001 (p : Pattern) (guard : d1690 p = 1) : d702 p ≤ (0 : Int) + d1710 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d702, d1710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7984 p hg
    simpa only [d702, d1710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d702, d1710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8000 p hg
    simpa only [d702, d1710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8002 (p : Pattern) (guard : d1690 p = 1) : d701 p ≤ (0 : Int) + d1711 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d701, d1711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7987 p hg
    simpa only [d701, d1711, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d701, d1711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7975 p hg
    simpa only [d701, d1711, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8003 (p : Pattern) (guard : d1690 p = 1) : d702 p ≤ (0 : Int) + d1712 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d702, d1712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7990 p hg
    simpa only [d702, d1712, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d702, d1712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8002 p hg
    simpa only [d702, d1712, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8004 (p : Pattern) (guard : d1690 p = 1) : d702 p ≤ (0 : Int) + d1713 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d1713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8001 p hg
    simpa only [d1713, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d1713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8003 p hg
    simpa only [d1713, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8005 (p : Pattern) (guard : d1690 p = 1) : d702 p ≤ (0 : Int) + d1714 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d1714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8001 p hg
    simpa only [d1714, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d1714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8004 p hg
    simpa only [d1714, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8006 (p : Pattern) (guard : d1690 p = 1) : d702 p ≤ (0 : Int) + d1715 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d1715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8004 p hg
    simpa only [d1715, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d1715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8003 p hg
    simpa only [d1715, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8007 (p : Pattern) (guard : d1690 p = 1) : d702 p ≤ (0 : Int) + d1716 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d1716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8005 p hg
    simpa only [d1716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d1716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8006 p hg
    simpa only [d1716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8008 (p : Pattern) (guard : d1690 p = 1) : d703 p ≤ (0 : Int) + d1717 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d703, d1717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7999 p hg
    simpa only [d703, d1717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d703, d1717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8007 p hg
    simpa only [d703, d1717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8009 (p : Pattern) (guard : d1690 p = 1) : d704 p ≤ (0 : Int) + d1718 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d704, d1718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7995 p hg
    simpa only [d704, d1718, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d704, d1718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8008 p hg
    simpa only [d704, d1718, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8010 (p : Pattern) (guard : d1690 p = 1) : d705 p ≤ (0 : Int) + d1719 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d705, d1719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7989 p hg
    simpa only [d705, d1719, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d705, d1719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7975 p hg
    simpa only [d705, d1719, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8011 (p : Pattern) (guard : d1690 p = 1) : d706 p ≤ (0 : Int) + d1720 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d706, d1720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7989 p hg
    simpa only [d706, d1720, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d706, d1720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8010 p hg
    simpa only [d706, d1720, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8012 (p : Pattern) (guard : d1690 p = 1) : d707 p ≤ (0 : Int) + d1721 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d707, d1721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7992 p hg
    simpa only [d707, d1721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d707, d1721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8011 p hg
    simpa only [d707, d1721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8013 (p : Pattern) (guard : d1690 p = 1) : d708 p ≤ (0 : Int) + d1722 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d708, d1722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7993 p hg
    simpa only [d708, d1722, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d708, d1722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8012 p hg
    simpa only [d708, d1722, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8014 (p : Pattern) (guard : d1690 p = 1) : d709 p ≤ (0 : Int) + d1723 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d709, d1723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7992 p hg
    simpa only [d709, d1723, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d709, d1723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8010 p hg
    simpa only [d709, d1723, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8015 (p : Pattern) (guard : d1690 p = 1) : d710 p ≤ (0 : Int) + d1724 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d710, d1724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7993 p hg
    simpa only [d710, d1724, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d710, d1724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8014 p hg
    simpa only [d710, d1724, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8016 (p : Pattern) (guard : d1690 p = 1) : d711 p ≤ (0 : Int) + d1725 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d711, d1725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8013 p hg
    simpa only [d711, d1725, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d711, d1725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8015 p hg
    simpa only [d711, d1725, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8017 (p : Pattern) (guard : d1690 p = 1) : d712 p ≤ (0 : Int) + d1726 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d712, d1726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7996 p hg
    simpa only [d712, d1726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d712, d1726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8010 p hg
    simpa only [d712, d1726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8018 (p : Pattern) (guard : d1690 p = 1) : d713 p ≤ (0 : Int) + d1727 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d713, d1727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7997 p hg
    simpa only [d713, d1727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d713, d1727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8017 p hg
    simpa only [d713, d1727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8019 (p : Pattern) (guard : d1690 p = 1) : d714 p ≤ (0 : Int) + d1728 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d714, d1728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8004 p hg
    simpa only [d714, d1728, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d714, d1728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8010 p hg
    simpa only [d714, d1728, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8020 (p : Pattern) (guard : d1690 p = 1) : d715 p ≤ (0 : Int) + d1729 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d715, d1729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8005 p hg
    simpa only [d715, d1729, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d715, d1729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8019 p hg
    simpa only [d715, d1729, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8021 (p : Pattern) (guard : d1690 p = 1) : d716 p ≤ (0 : Int) + d1730 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d716, d1730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8018 p hg
    simpa only [d716, d1730, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d716, d1730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8020 p hg
    simpa only [d716, d1730, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8022 (p : Pattern) (guard : d1690 p = 1) : d717 p ≤ (0 : Int) + d1731 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d717, d1731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8016 p hg
    simpa only [d717, d1731, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d717, d1731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8021 p hg
    simpa only [d717, d1731, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8023 (p : Pattern) (guard : d1690 p = 1) : d718 p ≤ (0 : Int) + d1732 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d718, d1732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8009 p hg
    simpa only [d718, d1732, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d718, d1732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8022 p hg
    simpa only [d718, d1732, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8024 (p : Pattern) (guard : d1690 p = 1) : d719 p ≤ (0 : Int) + d1733 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d719, d1733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7977 p hg
    simpa only [d719, d1733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d719, d1733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8000 p hg
    simpa only [d719, d1733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8025 (p : Pattern) (guard : d1690 p = 1) : d719 p ≤ (0 : Int) + d1734 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d719, d1734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7987 p hg
    simpa only [d719, d1734, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d719, d1734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8002 p hg
    simpa only [d719, d1734, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8026 (p : Pattern) (guard : d1690 p = 1) : d719 p ≤ (0 : Int) + d1735 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d1735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8024 p hg
    simpa only [d1735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d1735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8025 p hg
    simpa only [d1735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8027 (p : Pattern) (guard : d1690 p = 1) : d719 p ≤ (0 : Int) + d1736 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d1736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8024 p hg
    simpa only [d1736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d1736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8026 p hg
    simpa only [d1736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8028 (p : Pattern) (guard : d1690 p = 1) : d719 p ≤ (0 : Int) + d1737 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d1737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8026 p hg
    simpa only [d1737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d1737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8025 p hg
    simpa only [d1737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8029 (p : Pattern) (guard : d1690 p = 1) : d719 p ≤ (0 : Int) + d1738 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d1738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8027 p hg
    simpa only [d1738, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d1738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8028 p hg
    simpa only [d1738, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8030 (p : Pattern) (guard : d1690 p = 1) : d720 p ≤ (0 : Int) + d1739 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d720, d1739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7995 p hg
    simpa only [d720, d1739, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d720, d1739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8029 p hg
    simpa only [d720, d1739, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8031 (p : Pattern) (guard : d1690 p = 1) : d705 p ≤ (0 : Int) + d1740 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d705, d1740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7983 p hg
    simpa only [d705, d1740, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d705, d1740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7975 p hg
    simpa only [d705, d1740, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8032 (p : Pattern) (guard : d1690 p = 1) : d706 p ≤ (0 : Int) + d1741 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d706, d1741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7983 p hg
    simpa only [d706, d1741, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d706, d1741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8031 p hg
    simpa only [d706, d1741, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8033 (p : Pattern) (guard : d1690 p = 1) : d706 p ≤ (0 : Int) + d1742 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d1742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8032 p hg
    simpa only [d1742, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d1742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8011 p hg
    simpa only [d1742, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8034 (p : Pattern) (guard : d1690 p = 1) : d706 p ≤ (0 : Int) + d1743 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d1743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8032 p hg
    simpa only [d1743, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d1743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8033 p hg
    simpa only [d1743, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8035 (p : Pattern) (guard : d1690 p = 1) : d706 p ≤ (0 : Int) + d1744 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d1744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8033 p hg
    simpa only [d1744, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d1744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8011 p hg
    simpa only [d1744, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8036 (p : Pattern) (guard : d1690 p = 1) : d706 p ≤ (0 : Int) + d1745 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d1745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8034 p hg
    simpa only [d1745, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d1745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8035 p hg
    simpa only [d1745, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8037 (p : Pattern) (guard : d1690 p = 1) : d721 p ≤ (0 : Int) + d1746 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d721, d1746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8030 p hg
    simpa only [d721, d1746, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d721, d1746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8036 p hg
    simpa only [d721, d1746, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8038 (p : Pattern) (guard : d1690 p = 1) : d722 p ≤ (0 : Int) + d1747 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d722, d1747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8026 p hg
    simpa only [d722, d1747, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d722, d1747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8010 p hg
    simpa only [d722, d1747, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8039 (p : Pattern) (guard : d1690 p = 1) : d723 p ≤ (0 : Int) + d1748 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d723, d1748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8027 p hg
    simpa only [d723, d1748, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d723, d1748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8038 p hg
    simpa only [d723, d1748, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8040 (p : Pattern) (guard : d1690 p = 1) : d724 p ≤ (0 : Int) + d1749 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d724, d1749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8015 p hg
    simpa only [d724, d1749, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d724, d1749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8039 p hg
    simpa only [d724, d1749, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8041 (p : Pattern) (guard : d1690 p = 1) : d725 p ≤ (0 : Int) + d1750 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d725, d1750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8033 p hg
    simpa only [d725, d1750, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d725, d1750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7975 p hg
    simpa only [d725, d1750, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8042 (p : Pattern) (guard : d1690 p = 1) : d726 p ≤ (0 : Int) + d1751 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d726, d1751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8034 p hg
    simpa only [d726, d1751, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d726, d1751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8041 p hg
    simpa only [d726, d1751, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8043 (p : Pattern) (guard : d1690 p = 1) : d705 p ≤ (0 : Int) + d1752 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d1752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8031 p hg
    simpa only [d1752, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d1752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8010 p hg
    simpa only [d1752, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8044 (p : Pattern) (guard : d1690 p = 1) : d705 p ≤ (0 : Int) + d1753 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d1753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8031 p hg
    simpa only [d1753, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d1753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8043 p hg
    simpa only [d1753, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8045 (p : Pattern) (guard : d1690 p = 1) : d727 p ≤ (0 : Int) + d1754 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d727, d1754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8043 p hg
    simpa only [d727, d1754, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d727, d1754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7975 p hg
    simpa only [d727, d1754, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8046 (p : Pattern) (guard : d1690 p = 1) : d728 p ≤ (0 : Int) + d1755 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d728, d1755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8044 p hg
    simpa only [d728, d1755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d728, d1755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8045 p hg
    simpa only [d728, d1755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8047 (p : Pattern) (guard : d1690 p = 1) : d729 p ≤ (0 : Int) + d1756 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d729, d1756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8042 p hg
    simpa only [d729, d1756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d729, d1756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8046 p hg
    simpa only [d729, d1756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8048 (p : Pattern) (guard : d1690 p = 1) : d730 p ≤ (0 : Int) + d1757 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d730, d1757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8040 p hg
    simpa only [d730, d1757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d730, d1757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8047 p hg
    simpa only [d730, d1757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8049 (p : Pattern) (guard : d1690 p = 1) : d731 p ≤ (0 : Int) + d1758 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d731, d1758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8037 p hg
    simpa only [d731, d1758, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d731, d1758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8048 p hg
    simpa only [d731, d1758, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8050 (p : Pattern) (guard : d1690 p = 1) : d732 p ≤ (0 : Int) + d1759 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d732, d1759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8023 p hg
    simpa only [d732, d1759, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d732, d1759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8049 p hg
    simpa only [d732, d1759, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8051 (p : Pattern) (guard : d1690 p = 1) : d733 p ≤ (0 : Int) + d1760 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d733, d1760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8015 p hg
    simpa only [d733, d1760, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d733, d1760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8021 p hg
    simpa only [d733, d1760, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8052 (p : Pattern) (guard : d1690 p = 1) : d734 p ≤ (0 : Int) + d1761 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d734, d1761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8009 p hg
    simpa only [d734, d1761, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d734, d1761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8051 p hg
    simpa only [d734, d1761, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8053 (p : Pattern) (guard : d1690 p = 1) : d705 p ≤ (0 : Int) + d1762 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d1762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8043 p hg
    simpa only [d1762, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d1762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8010 p hg
    simpa only [d1762, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8054 (p : Pattern) (guard : d1690 p = 1) : d705 p ≤ (0 : Int) + d1763 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d1763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8044 p hg
    simpa only [d1763, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d1763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8053 p hg
    simpa only [d1763, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8055 (p : Pattern) (guard : d1690 p = 1) : d735 p ≤ (0 : Int) + d1764 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d735, d1764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8036 p hg
    simpa only [d735, d1764, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d735, d1764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8054 p hg
    simpa only [d735, d1764, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8056 (p : Pattern) (guard : d1690 p = 1) : d736 p ≤ (0 : Int) + d1765 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d736, d1765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8030 p hg
    simpa only [d736, d1765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d736, d1765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8055 p hg
    simpa only [d736, d1765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8057 (p : Pattern) (guard : d1690 p = 1) : d737 p ≤ (0 : Int) + d1766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d737, d1766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8015 p hg
    simpa only [d737, d1766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d737, d1766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8020 p hg
    simpa only [d737, d1766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8058 (p : Pattern) (guard : d1690 p = 1) : d738 p ≤ (0 : Int) + d1767 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d738, d1767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8046 p hg
    simpa only [d738, d1767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d738, d1767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7975 p hg
    simpa only [d738, d1767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8059 (p : Pattern) (guard : d1690 p = 1) : d739 p ≤ (0 : Int) + d1768 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d739, d1768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8057 p hg
    simpa only [d739, d1768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d739, d1768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8058 p hg
    simpa only [d739, d1768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8060 (p : Pattern) (guard : d1690 p = 1) : d740 p ≤ (0 : Int) + d1769 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d740, d1769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8056 p hg
    simpa only [d740, d1769, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d740, d1769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8059 p hg
    simpa only [d740, d1769, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8061 (p : Pattern) (guard : d1690 p = 1) : d741 p ≤ (0 : Int) + d1770 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d741, d1770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8052 p hg
    simpa only [d741, d1770, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d741, d1770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8060 p hg
    simpa only [d741, d1770, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8062 (p : Pattern) (guard : d1690 p = 1) : d742 p ≤ (0 : Int) + d1771 p := by
  cases selected : p 80 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d742, d1771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8050 p hg
    simpa only [d742, d1771, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d742, d1771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8061 p hg
    simpa only [d742, d1771, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8063 (p : Pattern) (guard : d1240 p = 1) : d5 p ≤ (0 : Int) + d7 p := by
  cases selected : p 159 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1240, d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4109 p hg
    simpa only [d1240, d7, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1240, d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2786 p hg
    simpa only [d1240, d7, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8064 (p : Pattern) (guard : d1240 p = 1) : d697 p ≤ (0 : Int) + d7 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8063 p hg
    simpa only [d697, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4110 p hg
    simpa only [d697, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8065 (p : Pattern) (guard : d1240 p = 1) : d11 p ≤ (0 : Int) + d13 p := by
  cases selected : p 159 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1240, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4112 p hg
    simpa only [d1240, d13, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1240, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2790 p hg
    simpa only [d1240, d13, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8066 (p : Pattern) (guard : d1240 p = 1) : d698 p ≤ (0 : Int) + d13 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8065 p hg
    simpa only [d698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4113 p hg
    simpa only [d698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8067 (p : Pattern) (guard : d1240 p = 1) : d699 p ≤ (0 : Int) + d653 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d699, d653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8064 p hg
    simpa only [d699, d653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d699, d653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8066 p hg
    simpa only [d699, d653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8068 (p : Pattern) (guard : d1240 p = 1) : d700 p ≤ (0 : Int) + d654 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d700, d654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8064 p hg
    simpa only [d700, d654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d700, d654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8067 p hg
    simpa only [d700, d654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8069 (p : Pattern) (guard : d1240 p = 1) : d701 p ≤ (0 : Int) + d655 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d701, d655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8064 p hg
    simpa only [d701, d655, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d701, d655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3436 p hg
    simpa only [d701, d655, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8070 (p : Pattern) (guard : d1240 p = 1) : d702 p ≤ (0 : Int) + d656 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d702, d656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8067 p hg
    simpa only [d702, d656, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d702, d656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8069 p hg
    simpa only [d702, d656, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8071 (p : Pattern) (guard : d1240 p = 1) : d703 p ≤ (0 : Int) + d657 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d703, d657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8067 p hg
    simpa only [d703, d657, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d703, d657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8070 p hg
    simpa only [d703, d657, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8072 (p : Pattern) (guard : d1240 p = 1) : d704 p ≤ (0 : Int) + d658 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d704, d658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8068 p hg
    simpa only [d704, d658, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d704, d658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8071 p hg
    simpa only [d704, d658, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8073 (p : Pattern) (guard : d1240 p = 1) : d705 p ≤ (0 : Int) + d659 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d705, d659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8066 p hg
    simpa only [d705, d659, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d705, d659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3436 p hg
    simpa only [d705, d659, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8074 (p : Pattern) (guard : d1240 p = 1) : d706 p ≤ (0 : Int) + d660 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d706, d660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8066 p hg
    simpa only [d706, d660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d706, d660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8073 p hg
    simpa only [d706, d660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8075 (p : Pattern) (guard : d1240 p = 1) : d707 p ≤ (0 : Int) + d661 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d707, d661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8068 p hg
    simpa only [d707, d661, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d707, d661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8074 p hg
    simpa only [d707, d661, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8076 (p : Pattern) (guard : d1240 p = 1) : d708 p ≤ (0 : Int) + d662 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d708, d662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8068 p hg
    simpa only [d708, d662, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d708, d662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8075 p hg
    simpa only [d708, d662, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8077 (p : Pattern) (guard : d1240 p = 1) : d709 p ≤ (0 : Int) + d663 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d709, d663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8068 p hg
    simpa only [d709, d663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d709, d663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8073 p hg
    simpa only [d709, d663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8078 (p : Pattern) (guard : d1240 p = 1) : d710 p ≤ (0 : Int) + d664 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d710, d664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8068 p hg
    simpa only [d710, d664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d710, d664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8077 p hg
    simpa only [d710, d664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8079 (p : Pattern) (guard : d1240 p = 1) : d711 p ≤ (0 : Int) + d665 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d711, d665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8076 p hg
    simpa only [d711, d665, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d711, d665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8078 p hg
    simpa only [d711, d665, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8080 (p : Pattern) (guard : d1240 p = 1) : d712 p ≤ (0 : Int) + d666 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d712, d666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8067 p hg
    simpa only [d712, d666, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d712, d666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8073 p hg
    simpa only [d712, d666, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8081 (p : Pattern) (guard : d1240 p = 1) : d713 p ≤ (0 : Int) + d667 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d713, d667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8067 p hg
    simpa only [d713, d667, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d713, d667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8080 p hg
    simpa only [d713, d667, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8082 (p : Pattern) (guard : d1240 p = 1) : d714 p ≤ (0 : Int) + d668 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d714, d668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8070 p hg
    simpa only [d714, d668, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d714, d668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8073 p hg
    simpa only [d714, d668, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8083 (p : Pattern) (guard : d1240 p = 1) : d715 p ≤ (0 : Int) + d669 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d715, d669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8070 p hg
    simpa only [d715, d669, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d715, d669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8082 p hg
    simpa only [d715, d669, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8084 (p : Pattern) (guard : d1240 p = 1) : d716 p ≤ (0 : Int) + d670 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d716, d670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8081 p hg
    simpa only [d716, d670, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d716, d670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8083 p hg
    simpa only [d716, d670, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8085 (p : Pattern) (guard : d1240 p = 1) : d717 p ≤ (0 : Int) + d671 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d717, d671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8079 p hg
    simpa only [d717, d671, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d717, d671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8084 p hg
    simpa only [d717, d671, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8086 (p : Pattern) (guard : d1240 p = 1) : d718 p ≤ (0 : Int) + d672 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d718, d672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8072 p hg
    simpa only [d718, d672, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d718, d672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8085 p hg
    simpa only [d718, d672, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8087 (p : Pattern) (guard : d1240 p = 1) : d719 p ≤ (0 : Int) + d673 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d719, d673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8064 p hg
    simpa only [d719, d673, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d719, d673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8069 p hg
    simpa only [d719, d673, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8088 (p : Pattern) (guard : d1240 p = 1) : d720 p ≤ (0 : Int) + d674 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d720, d674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8068 p hg
    simpa only [d720, d674, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d720, d674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8087 p hg
    simpa only [d720, d674, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8089 (p : Pattern) (guard : d1240 p = 1) : d721 p ≤ (0 : Int) + d675 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d721, d675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8088 p hg
    simpa only [d721, d675, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d721, d675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8074 p hg
    simpa only [d721, d675, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8090 (p : Pattern) (guard : d1240 p = 1) : d722 p ≤ (0 : Int) + d676 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d722, d676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8087 p hg
    simpa only [d722, d676, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d722, d676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8073 p hg
    simpa only [d722, d676, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8091 (p : Pattern) (guard : d1240 p = 1) : d723 p ≤ (0 : Int) + d677 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d723, d677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8087 p hg
    simpa only [d723, d677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d723, d677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8090 p hg
    simpa only [d723, d677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8092 (p : Pattern) (guard : d1240 p = 1) : d724 p ≤ (0 : Int) + d678 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d724, d678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8078 p hg
    simpa only [d724, d678, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d724, d678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8091 p hg
    simpa only [d724, d678, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8093 (p : Pattern) (guard : d1240 p = 1) : d725 p ≤ (0 : Int) + d679 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d725, d679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8074 p hg
    simpa only [d725, d679, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d725, d679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3436 p hg
    simpa only [d725, d679, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8094 (p : Pattern) (guard : d1240 p = 1) : d726 p ≤ (0 : Int) + d680 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d726, d680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8074 p hg
    simpa only [d726, d680, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d726, d680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8093 p hg
    simpa only [d726, d680, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8095 (p : Pattern) (guard : d1240 p = 1) : d727 p ≤ (0 : Int) + d681 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d727, d681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8073 p hg
    simpa only [d727, d681, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d727, d681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3436 p hg
    simpa only [d727, d681, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8096 (p : Pattern) (guard : d1240 p = 1) : d728 p ≤ (0 : Int) + d682 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d728, d682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8073 p hg
    simpa only [d728, d682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d728, d682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8095 p hg
    simpa only [d728, d682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8097 (p : Pattern) (guard : d1240 p = 1) : d729 p ≤ (0 : Int) + d683 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d729, d683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8094 p hg
    simpa only [d729, d683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d729, d683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8096 p hg
    simpa only [d729, d683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8098 (p : Pattern) (guard : d1240 p = 1) : d730 p ≤ (0 : Int) + d684 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d730, d684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8092 p hg
    simpa only [d730, d684, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d730, d684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8097 p hg
    simpa only [d730, d684, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8099 (p : Pattern) (guard : d1240 p = 1) : d731 p ≤ (0 : Int) + d685 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d731, d685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8089 p hg
    simpa only [d731, d685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d731, d685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8098 p hg
    simpa only [d731, d685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8100 (p : Pattern) (guard : d1240 p = 1) : d732 p ≤ (0 : Int) + d686 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d732, d686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8086 p hg
    simpa only [d732, d686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d732, d686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8099 p hg
    simpa only [d732, d686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8101 (p : Pattern) (guard : d1240 p = 1) : d733 p ≤ (0 : Int) + d687 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d733, d687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8078 p hg
    simpa only [d733, d687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d733, d687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8084 p hg
    simpa only [d733, d687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8102 (p : Pattern) (guard : d1240 p = 1) : d734 p ≤ (0 : Int) + d688 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d734, d688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8072 p hg
    simpa only [d734, d688, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d734, d688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8101 p hg
    simpa only [d734, d688, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8103 (p : Pattern) (guard : d1240 p = 1) : d735 p ≤ (0 : Int) + d689 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d735, d689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8074 p hg
    simpa only [d735, d689, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d735, d689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8073 p hg
    simpa only [d735, d689, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8104 (p : Pattern) (guard : d1240 p = 1) : d736 p ≤ (0 : Int) + d690 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d736, d690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8088 p hg
    simpa only [d736, d690, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d736, d690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8103 p hg
    simpa only [d736, d690, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8105 (p : Pattern) (guard : d1240 p = 1) : d737 p ≤ (0 : Int) + d691 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d737, d691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8078 p hg
    simpa only [d737, d691, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d737, d691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8083 p hg
    simpa only [d737, d691, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8106 (p : Pattern) (guard : d1240 p = 1) : d738 p ≤ (0 : Int) + d692 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d738, d692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8096 p hg
    simpa only [d738, d692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d738, d692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3436 p hg
    simpa only [d738, d692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8107 (p : Pattern) (guard : d1240 p = 1) : d739 p ≤ (0 : Int) + d693 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d739, d693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8105 p hg
    simpa only [d739, d693, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d739, d693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8106 p hg
    simpa only [d739, d693, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8108 (p : Pattern) (guard : d1240 p = 1) : d740 p ≤ (0 : Int) + d694 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d740, d694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8104 p hg
    simpa only [d740, d694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d740, d694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8107 p hg
    simpa only [d740, d694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8109 (p : Pattern) (guard : d1240 p = 1) : d741 p ≤ (0 : Int) + d695 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d741, d695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8102 p hg
    simpa only [d741, d695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d741, d695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8108 p hg
    simpa only [d741, d695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8110 (p : Pattern) (guard : d1240 p = 1) : d742 p ≤ (0 : Int) + d696 p := by
  cases selected : p 80 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d742, d696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8100 p hg
    simpa only [d742, d696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d742, d696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8109 p hg
    simpa only [d742, d696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8111 (p : Pattern) (guard : d0 p = 1) : d5 p ≤ (2 : Int) + d4 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8112 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (2 : Int) + d3 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8113 (p : Pattern) (guard : d917 p = 1) : d5 p ≤ (2 : Int) + d4 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d917, d5, d4, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4307 p hg
    simpa only [d917, d5, d4, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d917, d5, d4, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8112 p hg
    simpa only [d917, d5, d4, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8114 (p : Pattern) (guard : d1505 p = 1) : d5 p ≤ (2 : Int) + d4 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8111 p hg
    simpa only [d1505, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d1505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8113 p hg
    simpa only [d1505, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8115 (p : Pattern) (guard : d0 p = 1) : d37 p ≤ (2 : Int) + d4 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8116 (p : Pattern) (guard : d1506 p = 1) : d697 p ≤ (2 : Int) + d4 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1505 p = 1 := by simpa only [d1506, d697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8114 p hg
    simpa only [d1506, d697, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1506, d697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8115 p hg
    simpa only [d1506, d697, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8117 (p : Pattern) (guard : d0 p = 1) : d11 p ≤ (2 : Int) + d10 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8118 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (2 : Int) + d9 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8119 (p : Pattern) (guard : d917 p = 1) : d11 p ≤ (2 : Int) + d10 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d917, d11, d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4316 p hg
    simpa only [d917, d11, d10, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d917, d11, d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8118 p hg
    simpa only [d917, d11, d10, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban32Refined
