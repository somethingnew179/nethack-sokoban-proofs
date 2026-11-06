/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons156
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c21980 (pattern : Twelve) (guard : d1 pattern = 1) : d1342 pattern ≤ (18 : Int) + d1300 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1342, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21979 pattern childGuard
    simpa only [d1342, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1342, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21564 pattern childGuard
    simpa only [d1342, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21981 (pattern : Twelve) (guard : d1 pattern = 1) : d1347 pattern ≤ (18 : Int) + d1672 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1347, d1672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21977 pattern childGuard
    simpa only [d1347, d1672, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1347, d1672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21980 pattern childGuard
    simpa only [d1347, d1672, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21982 (pattern : Twelve) (guard : d1 pattern = 1) : d1330 pattern ≤ (18 : Int) + d128 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1330, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21919 pattern childGuard
    simpa only [d1330, d128, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1330, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21564 pattern childGuard
    simpa only [d1330, d128, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21983 (pattern : Twelve) (guard : d1 pattern = 1) : d1331 pattern ≤ (18 : Int) + d183 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1331, d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21934 pattern childGuard
    simpa only [d1331, d183, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1331, d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21564 pattern childGuard
    simpa only [d1331, d183, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21984 (pattern : Twelve) (guard : d1 pattern = 1) : d1337 pattern ≤ (18 : Int) + d1667 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1337, d1667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21982 pattern childGuard
    simpa only [d1337, d1667, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1337, d1667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21983 pattern childGuard
    simpa only [d1337, d1667, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21985 (pattern : Twelve) (guard : d1 pattern = 1) : d1343 pattern ≤ (18 : Int) + d1670 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1343, d1670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21811 pattern childGuard
    simpa only [d1343, d1670, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1343, d1670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21984 pattern childGuard
    simpa only [d1343, d1670, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21986 (pattern : Twelve) (guard : d1 pattern = 1) : d1332 pattern ≤ (18 : Int) + d822 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1332, d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21634 pattern childGuard
    simpa only [d1332, d822, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1332, d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21587 pattern childGuard
    simpa only [d1332, d822, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21987 (pattern : Twelve) (guard : d1 pattern = 1) : d1338 pattern ≤ (18 : Int) + d1252 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1338, d1252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21986 pattern childGuard
    simpa only [d1338, d1252, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1338, d1252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21730 pattern childGuard
    simpa only [d1338, d1252, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21988 (pattern : Twelve) (guard : d1 pattern = 1) : d1344 pattern ≤ (18 : Int) + d1626 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1344, d1626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21987 pattern childGuard
    simpa only [d1344, d1626, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1344, d1626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21564 pattern childGuard
    simpa only [d1344, d1626, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21989 (pattern : Twelve) (guard : d1 pattern = 1) : d1348 pattern ≤ (18 : Int) + d1673 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1348, d1673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21985 pattern childGuard
    simpa only [d1348, d1673, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1348, d1673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21988 pattern childGuard
    simpa only [d1348, d1673, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21990 (pattern : Twelve) (guard : d1 pattern = 1) : d1350 pattern ≤ (18 : Int) + d1675 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1350, d1675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21981 pattern childGuard
    simpa only [d1350, d1675, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1350, d1675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21989 pattern childGuard
    simpa only [d1350, d1675, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21991 (pattern : Twelve) (guard : d1 pattern = 1) : d1351 pattern ≤ (18 : Int) + d1662 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1351, d1662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21973 pattern childGuard
    simpa only [d1351, d1662, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1351, d1662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21564 pattern childGuard
    simpa only [d1351, d1662, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21992 (pattern : Twelve) (guard : d1 pattern = 1) : d1352 pattern ≤ (18 : Int) + d1676 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1352, d1676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21990 pattern childGuard
    simpa only [d1352, d1676, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1352, d1676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21991 pattern childGuard
    simpa only [d1352, d1676, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21993 (pattern : Twelve) (guard : d1 pattern = 1) : d1353 pattern ≤ (18 : Int) + d1677 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1353, d1677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21974 pattern childGuard
    simpa only [d1353, d1677, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1353, d1677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21992 pattern childGuard
    simpa only [d1353, d1677, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21994 (pattern : Twelve) (guard : d1 pattern = 1) : d1616 pattern ≤ (18 : Int) + d20 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21919 pattern childGuard
    simpa only [d1616, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21868 pattern childGuard
    simpa only [d1616, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21995 (pattern : Twelve) (guard : d1 pattern = 1) : d1619 pattern ≤ (18 : Int) + d20 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21994 pattern childGuard
    simpa only [d1619, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21868 pattern childGuard
    simpa only [d1619, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21996 (pattern : Twelve) (guard : d1 pattern = 1) : d1622 pattern ≤ (18 : Int) + d1814 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1622, d1814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21591 pattern childGuard
    simpa only [d1622, d1814, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1622, d1814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21995 pattern childGuard
    simpa only [d1622, d1814, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21997 (pattern : Twelve) (guard : d1 pattern = 1) : d1617 pattern ≤ (18 : Int) + d21 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21634 pattern childGuard
    simpa only [d1617, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21630 pattern childGuard
    simpa only [d1617, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21998 (pattern : Twelve) (guard : d1 pattern = 1) : d1623 pattern ≤ (18 : Int) + d1815 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1623, d1815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21997 pattern childGuard
    simpa only [d1623, d1815, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1623, d1815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21564 pattern childGuard
    simpa only [d1623, d1815, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21999 (pattern : Twelve) (guard : d1 pattern = 1) : d1627 pattern ≤ (18 : Int) + d1818 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1627, d1818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21996 pattern childGuard
    simpa only [d1627, d1818, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1627, d1818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21998 pattern childGuard
    simpa only [d1627, d1818, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22000 (pattern : Twelve) (guard : d1 pattern = 1) : d1630 pattern ≤ (18 : Int) + d1821 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1630, d1821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21999 pattern childGuard
    simpa only [d1630, d1821, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1630, d1821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21958 pattern childGuard
    simpa only [d1630, d1821, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22001 (pattern : Twelve) (guard : d1 pattern = 1) : d1618 pattern ≤ (18 : Int) + d1646 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1618, d1646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21868 pattern childGuard
    simpa only [d1618, d1646, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1618, d1646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21718 pattern childGuard
    simpa only [d1618, d1646, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22002 (pattern : Twelve) (guard : d1 pattern = 1) : d1620 pattern ≤ (18 : Int) + d1646 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21935 pattern childGuard
    simpa only [d1620, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22001 pattern childGuard
    simpa only [d1620, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22003 (pattern : Twelve) (guard : d1 pattern = 1) : d1624 pattern ≤ (18 : Int) + d1816 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1624, d1816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21631 pattern childGuard
    simpa only [d1624, d1816, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1624, d1816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22002 pattern childGuard
    simpa only [d1624, d1816, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22004 (pattern : Twelve) (guard : d1 pattern = 1) : d1628 pattern ≤ (18 : Int) + d1819 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1628, d1819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22003 pattern childGuard
    simpa only [d1628, d1819, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1628, d1819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21957 pattern childGuard
    simpa only [d1628, d1819, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22005 (pattern : Twelve) (guard : d1 pattern = 1) : d182 pattern ≤ (18 : Int) + d183 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d182, d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21718 pattern childGuard
    simpa only [d182, d183, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d182, d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21564 pattern childGuard
    simpa only [d182, d183, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22006 (pattern : Twelve) (guard : d1 pattern = 1) : d1621 pattern ≤ (18 : Int) + d183 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21983 pattern childGuard
    simpa only [d1621, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22005 pattern childGuard
    simpa only [d1621, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22007 (pattern : Twelve) (guard : d1 pattern = 1) : d1625 pattern ≤ (18 : Int) + d1817 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1625, d1817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21677 pattern childGuard
    simpa only [d1625, d1817, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1625, d1817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22006 pattern childGuard
    simpa only [d1625, d1817, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22008 (pattern : Twelve) (guard : d1 pattern = 1) : d1626 pattern ≤ (18 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21904 pattern childGuard
    simpa only [d1626, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21564 pattern childGuard
    simpa only [d1626, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22009 (pattern : Twelve) (guard : d1 pattern = 1) : d1629 pattern ≤ (18 : Int) + d1820 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1629, d1820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22007 pattern childGuard
    simpa only [d1629, d1820, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1629, d1820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22008 pattern childGuard
    simpa only [d1629, d1820, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22010 (pattern : Twelve) (guard : d1 pattern = 1) : d1631 pattern ≤ (18 : Int) + d1822 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1631, d1822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22004 pattern childGuard
    simpa only [d1631, d1822, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1631, d1822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22009 pattern childGuard
    simpa only [d1631, d1822, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22011 (pattern : Twelve) (guard : d1 pattern = 1) : d1632 pattern ≤ (18 : Int) + d1823 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1632, d1823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21958 pattern childGuard
    simpa only [d1632, d1823, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1632, d1823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21564 pattern childGuard
    simpa only [d1632, d1823, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22012 (pattern : Twelve) (guard : d1 pattern = 1) : d1633 pattern ≤ (18 : Int) + d1824 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1633, d1824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22010 pattern childGuard
    simpa only [d1633, d1824, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1633, d1824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22011 pattern childGuard
    simpa only [d1633, d1824, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22013 (pattern : Twelve) (guard : d1 pattern = 1) : d1634 pattern ≤ (18 : Int) + d1825 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1634, d1825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22000 pattern childGuard
    simpa only [d1634, d1825, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1634, d1825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22012 pattern childGuard
    simpa only [d1634, d1825, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22014 (pattern : Twelve) (guard : d1 pattern = 1) : d1635 pattern ≤ (18 : Int) + d1826 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1635, d1826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21993 pattern childGuard
    simpa only [d1635, d1826, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1635, d1826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22013 pattern childGuard
    simpa only [d1635, d1826, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22015 (pattern : Twelve) (guard : d1 pattern = 1) : d1636 pattern ≤ (18 : Int) + d1827 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1636, d1827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21963 pattern childGuard
    simpa only [d1636, d1827, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1636, d1827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22014 pattern childGuard
    simpa only [d1636, d1827, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22016 (pattern : Twelve) (guard : d1 pattern = 1) : d1324 pattern ≤ (18 : Int) + d6 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21780 pattern childGuard
    simpa only [d1324, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21782 pattern childGuard
    simpa only [d1324, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22017 (pattern : Twelve) (guard : d1 pattern = 1) : d1649 pattern ≤ (18 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21781 pattern childGuard
    simpa only [d1649, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22016 pattern childGuard
    simpa only [d1649, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22018 (pattern : Twelve) (guard : d1 pattern = 1) : d1650 pattern ≤ (18 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21783 pattern childGuard
    simpa only [d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21564 pattern childGuard
    simpa only [d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22019 (pattern : Twelve) (guard : d1 pattern = 1) : d1656 pattern ≤ (18 : Int) + d6 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22017 pattern childGuard
    simpa only [d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22018 pattern childGuard
    simpa only [d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22020 (pattern : Twelve) (guard : d1 pattern = 1) : d29 pattern ≤ (18 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21781 pattern childGuard
    simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21564 pattern childGuard
    simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22021 (pattern : Twelve) (guard : d1 pattern = 1) : d1286 pattern ≤ (18 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21784 pattern childGuard
    simpa only [d1286, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22020 pattern childGuard
    simpa only [d1286, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22022 (pattern : Twelve) (guard : d1 pattern = 1) : d1644 pattern ≤ (18 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22016 pattern childGuard
    simpa only [d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21575 pattern childGuard
    simpa only [d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22023 (pattern : Twelve) (guard : d1 pattern = 1) : d1645 pattern ≤ (18 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22016 pattern childGuard
    simpa only [d1645, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21564 pattern childGuard
    simpa only [d1645, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22024 (pattern : Twelve) (guard : d1 pattern = 1) : d1647 pattern ≤ (18 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22022 pattern childGuard
    simpa only [d1647, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22023 pattern childGuard
    simpa only [d1647, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22025 (pattern : Twelve) (guard : d1 pattern = 1) : d1651 pattern ≤ (18 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22021 pattern childGuard
    simpa only [d1651, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22024 pattern childGuard
    simpa only [d1651, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22026 (pattern : Twelve) (guard : d1 pattern = 1) : d1289 pattern ≤ (18 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21812 pattern childGuard
    simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21785 pattern childGuard
    simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22027 (pattern : Twelve) (guard : d1 pattern = 1) : d1300 pattern ≤ (18 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22026 pattern childGuard
    simpa only [d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21564 pattern childGuard
    simpa only [d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22028 (pattern : Twelve) (guard : d1 pattern = 1) : d1657 pattern ≤ (18 : Int) + d6 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22025 pattern childGuard
    simpa only [d1657, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22027 pattern childGuard
    simpa only [d1657, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22029 (pattern : Twelve) (guard : d1 pattern = 1) : d1660 pattern ≤ (18 : Int) + d6 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22019 pattern childGuard
    simpa only [d1660, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22028 pattern childGuard
    simpa only [d1660, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22030 (pattern : Twelve) (guard : d1 pattern = 1) : d1652 pattern ≤ (18 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21784 pattern childGuard
    simpa only [d1652, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22022 pattern childGuard
    simpa only [d1652, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22031 (pattern : Twelve) (guard : d1 pattern = 1) : d1653 pattern ≤ (18 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21812 pattern childGuard
    simpa only [d1653, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21564 pattern childGuard
    simpa only [d1653, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22032 (pattern : Twelve) (guard : d1 pattern = 1) : d1658 pattern ≤ (18 : Int) + d6 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22030 pattern childGuard
    simpa only [d1658, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22031 pattern childGuard
    simpa only [d1658, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22033 (pattern : Twelve) (guard : d1 pattern = 1) : d1646 pattern ≤ (18 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21575 pattern childGuard
    simpa only [d1646, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21587 pattern childGuard
    simpa only [d1646, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22034 (pattern : Twelve) (guard : d1 pattern = 1) : d1648 pattern ≤ (18 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22033 pattern childGuard
    simpa only [d1648, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21730 pattern childGuard
    simpa only [d1648, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22035 (pattern : Twelve) (guard : d1 pattern = 1) : d1654 pattern ≤ (18 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22026 pattern childGuard
    simpa only [d1654, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22034 pattern childGuard
    simpa only [d1654, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22036 (pattern : Twelve) (guard : d1 pattern = 1) : d1655 pattern ≤ (18 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21813 pattern childGuard
    simpa only [d1655, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21564 pattern childGuard
    simpa only [d1655, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22037 (pattern : Twelve) (guard : d1 pattern = 1) : d1659 pattern ≤ (18 : Int) + d6 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22035 pattern childGuard
    simpa only [d1659, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22036 pattern childGuard
    simpa only [d1659, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22038 (pattern : Twelve) (guard : d1 pattern = 1) : d1661 pattern ≤ (18 : Int) + d6 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22032 pattern childGuard
    simpa only [d1661, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22037 pattern childGuard
    simpa only [d1661, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22039 (pattern : Twelve) (guard : d1 pattern = 1) : d1662 pattern ≤ (18 : Int) + d6 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22028 pattern childGuard
    simpa only [d1662, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21564 pattern childGuard
    simpa only [d1662, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22040 (pattern : Twelve) (guard : d1 pattern = 1) : d1663 pattern ≤ (18 : Int) + d6 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22038 pattern childGuard
    simpa only [d1663, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22039 pattern childGuard
    simpa only [d1663, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22041 (pattern : Twelve) (guard : d1 pattern = 1) : d1664 pattern ≤ (18 : Int) + d6 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22029 pattern childGuard
    simpa only [d1664, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22040 pattern childGuard
    simpa only [d1664, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22042 (pattern : Twelve) (guard : d1 pattern = 1) : d1668 pattern ≤ (18 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21781 pattern childGuard
    simpa only [d1668, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22022 pattern childGuard
    simpa only [d1668, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22043 (pattern : Twelve) (guard : d1 pattern = 1) : d1671 pattern ≤ (18 : Int) + d6 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22042 pattern childGuard
    simpa only [d1671, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22018 pattern childGuard
    simpa only [d1671, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22044 (pattern : Twelve) (guard : d1 pattern = 1) : d1674 pattern ≤ (18 : Int) + d6 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22043 pattern childGuard
    simpa only [d1674, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22028 pattern childGuard
    simpa only [d1674, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22045 (pattern : Twelve) (guard : d1 pattern = 1) : d1665 pattern ≤ (18 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22016 pattern childGuard
    simpa only [d1665, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21587 pattern childGuard
    simpa only [d1665, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22046 (pattern : Twelve) (guard : d1 pattern = 1) : d1666 pattern ≤ (18 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22022 pattern childGuard
    simpa only [d1666, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22045 pattern childGuard
    simpa only [d1666, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22047 (pattern : Twelve) (guard : d1 pattern = 1) : d1669 pattern ≤ (18 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21784 pattern childGuard
    simpa only [d1669, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22046 pattern childGuard
    simpa only [d1669, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22048 (pattern : Twelve) (guard : d1 pattern = 1) : d1672 pattern ≤ (18 : Int) + d6 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22047 pattern childGuard
    simpa only [d1672, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22027 pattern childGuard
    simpa only [d1672, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22049 (pattern : Twelve) (guard : d1 pattern = 1) : d183 pattern ≤ (18 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21587 pattern childGuard
    simpa only [d183, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21564 pattern childGuard
    simpa only [d183, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22050 (pattern : Twelve) (guard : d1 pattern = 1) : d1667 pattern ≤ (18 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21730 pattern childGuard
    simpa only [d1667, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22049 pattern childGuard
    simpa only [d1667, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22051 (pattern : Twelve) (guard : d1 pattern = 1) : d1670 pattern ≤ (18 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22026 pattern childGuard
    simpa only [d1670, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22050 pattern childGuard
    simpa only [d1670, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22052 (pattern : Twelve) (guard : d1 pattern = 1) : d1673 pattern ≤ (18 : Int) + d6 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22051 pattern childGuard
    simpa only [d1673, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22008 pattern childGuard
    simpa only [d1673, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22053 (pattern : Twelve) (guard : d1 pattern = 1) : d1675 pattern ≤ (18 : Int) + d6 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22048 pattern childGuard
    simpa only [d1675, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22052 pattern childGuard
    simpa only [d1675, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22054 (pattern : Twelve) (guard : d1 pattern = 1) : d1676 pattern ≤ (18 : Int) + d6 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22053 pattern childGuard
    simpa only [d1676, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22039 pattern childGuard
    simpa only [d1676, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22055 (pattern : Twelve) (guard : d1 pattern = 1) : d1677 pattern ≤ (18 : Int) + d6 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22044 pattern childGuard
    simpa only [d1677, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22054 pattern childGuard
    simpa only [d1677, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22056 (pattern : Twelve) (guard : d1 pattern = 1) : d1814 pattern ≤ (18 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21783 pattern childGuard
    simpa only [d1814, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21575 pattern childGuard
    simpa only [d1814, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22057 (pattern : Twelve) (guard : d1 pattern = 1) : d1815 pattern ≤ (18 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21583 pattern childGuard
    simpa only [d1815, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21564 pattern childGuard
    simpa only [d1815, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22058 (pattern : Twelve) (guard : d1 pattern = 1) : d1818 pattern ≤ (18 : Int) + d6 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22056 pattern childGuard
    simpa only [d1818, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22057 pattern childGuard
    simpa only [d1818, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22059 (pattern : Twelve) (guard : d1 pattern = 1) : d1821 pattern ≤ (18 : Int) + d6 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22058 pattern childGuard
    simpa only [d1821, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22037 pattern childGuard
    simpa only [d1821, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22060 (pattern : Twelve) (guard : d1 pattern = 1) : d1816 pattern ≤ (18 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21812 pattern childGuard
    simpa only [d1816, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22033 pattern childGuard
    simpa only [d1816, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22061 (pattern : Twelve) (guard : d1 pattern = 1) : d1819 pattern ≤ (18 : Int) + d6 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22060 pattern childGuard
    simpa only [d1819, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22036 pattern childGuard
    simpa only [d1819, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22062 (pattern : Twelve) (guard : d1 pattern = 1) : d1817 pattern ≤ (18 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21813 pattern childGuard
    simpa only [d1817, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22049 pattern childGuard
    simpa only [d1817, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22063 (pattern : Twelve) (guard : d1 pattern = 1) : d1820 pattern ≤ (18 : Int) + d6 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22062 pattern childGuard
    simpa only [d1820, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21564 pattern childGuard
    simpa only [d1820, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22064 (pattern : Twelve) (guard : d1 pattern = 1) : d1822 pattern ≤ (18 : Int) + d6 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22061 pattern childGuard
    simpa only [d1822, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22063 pattern childGuard
    simpa only [d1822, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22065 (pattern : Twelve) (guard : d1 pattern = 1) : d1823 pattern ≤ (18 : Int) + d6 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22037 pattern childGuard
    simpa only [d1823, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21564 pattern childGuard
    simpa only [d1823, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22066 (pattern : Twelve) (guard : d1 pattern = 1) : d1824 pattern ≤ (18 : Int) + d6 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22064 pattern childGuard
    simpa only [d1824, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22065 pattern childGuard
    simpa only [d1824, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22067 (pattern : Twelve) (guard : d1 pattern = 1) : d1825 pattern ≤ (18 : Int) + d6 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22059 pattern childGuard
    simpa only [d1825, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22066 pattern childGuard
    simpa only [d1825, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22068 (pattern : Twelve) (guard : d1 pattern = 1) : d1826 pattern ≤ (18 : Int) + d6 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22055 pattern childGuard
    simpa only [d1826, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22067 pattern childGuard
    simpa only [d1826, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22069 (pattern : Twelve) (guard : d1 pattern = 1) : d1827 pattern ≤ (18 : Int) + d6 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22041 pattern childGuard
    simpa only [d1827, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22068 pattern childGuard
    simpa only [d1827, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22070 (pattern : Twelve) (guard : d1 pattern = 1) : d806 pattern ≤ (1 : Int) + d806 pattern := by
  omega
theorem c22071 (pattern : Twelve) (guard : d1 pattern = 1) : d1267 pattern ≤ (1 : Int) + d1267 pattern := by
  omega
theorem c22072 (pattern : Twelve) (guard : d1 pattern = 1) : d1636 pattern ≤ (1 : Int) + d1636 pattern := by
  omega
theorem c22073 (pattern : Twelve) (guard : d1 pattern = 1) : d1827 pattern ≤ (1 : Int) + d1827 pattern := by
  omega
theorem c22074 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (19 : Int) + d0 pattern := by
  omega
theorem c22075 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (19 : Int) + d1 pattern := by
  change (0 : Int) ≤ (19 : Int) + 1
  decide
theorem c22076 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (19 : Int) + d7 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22074 pattern childGuard
    simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22075 pattern childGuard
    simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22077 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (19 : Int) + d17 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22074 pattern childGuard
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22076 pattern childGuard
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22078 (pattern : Twelve) (guard : d1 pattern = 1) : d1 pattern ≤ (19 : Int) + d1 pattern := by
  omega
theorem c22079 (pattern : Twelve) (guard : d1 pattern = 1) : d26 pattern ≤ (19 : Int) + d27 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d26, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22077 pattern childGuard
    simpa only [d26, d27, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d26, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22078 pattern childGuard
    simpa only [d26, d27, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22080 (pattern : Twelve) (guard : d1 pattern = 1) : d7 pattern ≤ (19 : Int) + d1 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22075 pattern childGuard
    simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22078 pattern childGuard
    simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22081 (pattern : Twelve) (guard : d1 pattern = 1) : d17 pattern ≤ (19 : Int) + d814 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22076 pattern childGuard
    simpa only [d17, d814, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22080 pattern childGuard
    simpa only [d17, d814, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22082 (pattern : Twelve) (guard : d1 pattern = 1) : d27 pattern ≤ (19 : Int) + d816 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d27, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22081 pattern childGuard
    simpa only [d27, d816, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d27, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22078 pattern childGuard
    simpa only [d27, d816, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22083 (pattern : Twelve) (guard : d1 pattern = 1) : d50 pattern ≤ (19 : Int) + d824 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d50, d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22079 pattern childGuard
    simpa only [d50, d824, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d50, d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22082 pattern childGuard
    simpa only [d50, d824, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22084 (pattern : Twelve) (guard : d1 pattern = 1) : d72 pattern ≤ (19 : Int) + d838 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d72, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22074 pattern childGuard
    simpa only [d72, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d72, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22083 pattern childGuard
    simpa only [d72, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22085 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (19 : Int) + d2 pattern := by
  change (0 : Int) ≤ (19 : Int) + 2
  decide
theorem c22086 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (19 : Int) + d10 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22074 pattern childGuard
    simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22085 pattern childGuard
    simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22087 (pattern : Twelve) (guard : d1 pattern = 1) : d1 pattern ≤ (19 : Int) + d3 pattern := by
  change (1 : Int) ≤ (19 : Int) + 3
  decide
theorem c22088 (pattern : Twelve) (guard : d1 pattern = 1) : d7 pattern ≤ (19 : Int) + d11 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22075 pattern childGuard
    simpa only [d7, d11, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22087 pattern childGuard
    simpa only [d7, d11, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22089 (pattern : Twelve) (guard : d1 pattern = 1) : d17 pattern ≤ (19 : Int) + d19 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22086 pattern childGuard
    simpa only [d17, d19, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22088 pattern childGuard
    simpa only [d17, d19, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22090 (pattern : Twelve) (guard : d1 pattern = 1) : d1 pattern ≤ (19 : Int) + d2 pattern := by
  change (1 : Int) ≤ (19 : Int) + 2
  decide
theorem c22091 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (19 : Int) + d4 pattern := by
  change (2 : Int) ≤ (19 : Int) + 4
  decide
theorem c22092 (pattern : Twelve) (guard : d1 pattern = 1) : d8 pattern ≤ (19 : Int) + d16 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d8, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22090 pattern childGuard
    simpa only [d8, d16, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d8, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22091 pattern childGuard
    simpa only [d8, d16, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22093 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (19 : Int) + d3 pattern := by
  change (2 : Int) ≤ (19 : Int) + 3
  decide
theorem c22094 (pattern : Twelve) (guard : d1 pattern = 1) : d3 pattern ≤ (19 : Int) + d5 pattern := by
  change (3 : Int) ≤ (19 : Int) + 5
  decide
theorem c22095 (pattern : Twelve) (guard : d1 pattern = 1) : d9 pattern ≤ (19 : Int) + d12 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22093 pattern childGuard
    simpa only [d9, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22094 pattern childGuard
    simpa only [d9, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22096 (pattern : Twelve) (guard : d1 pattern = 1) : d18 pattern ≤ (19 : Int) + d25 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d18, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22092 pattern childGuard
    simpa only [d18, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d18, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22095 pattern childGuard
    simpa only [d18, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22097 (pattern : Twelve) (guard : d1 pattern = 1) : d28 pattern ≤ (19 : Int) + d817 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d28, d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22089 pattern childGuard
    simpa only [d28, d817, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d28, d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22096 pattern childGuard
    simpa only [d28, d817, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22098 (pattern : Twelve) (guard : d1 pattern = 1) : d10 pattern ≤ (19 : Int) + d16 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d10, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22085 pattern childGuard
    simpa only [d10, d16, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d10, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22091 pattern childGuard
    simpa only [d10, d16, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22099 (pattern : Twelve) (guard : d1 pattern = 1) : d11 pattern ≤ (19 : Int) + d12 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22087 pattern childGuard
    simpa only [d11, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22094 pattern childGuard
    simpa only [d11, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22100 (pattern : Twelve) (guard : d1 pattern = 1) : d19 pattern ≤ (19 : Int) + d25 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d19, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22098 pattern childGuard
    simpa only [d19, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d19, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22099 pattern childGuard
    simpa only [d19, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22101 (pattern : Twelve) (guard : d1 pattern = 1) : d6 pattern ≤ (19 : Int) + d6 pattern := by
  omega
theorem c22102 (pattern : Twelve) (guard : d1 pattern = 1) : d29 pattern ≤ (19 : Int) + d42 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d29, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22100 pattern childGuard
    simpa only [d29, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d29, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22101 pattern childGuard
    simpa only [d29, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22103 (pattern : Twelve) (guard : d1 pattern = 1) : d51 pattern ≤ (19 : Int) + d825 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d51, d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22097 pattern childGuard
    simpa only [d51, d825, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d51, d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22102 pattern childGuard
    simpa only [d51, d825, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22104 (pattern : Twelve) (guard : d1 pattern = 1) : d73 pattern ≤ (19 : Int) + d839 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d73, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22077 pattern childGuard
    simpa only [d73, d839, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d73, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22103 pattern childGuard
    simpa only [d73, d839, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22105 (pattern : Twelve) (guard : d1 pattern = 1) : d91 pattern ≤ (19 : Int) + d853 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d91, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22084 pattern childGuard
    simpa only [d91, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d91, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22104 pattern childGuard
    simpa only [d91, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22106 (pattern : Twelve) (guard : d1 pattern = 1) : d30 pattern ≤ (19 : Int) + d30 pattern := by
  omega
theorem c22107 (pattern : Twelve) (guard : d1 pattern = 1) : d3 pattern ≤ (19 : Int) + d6 pattern := by
  change (3 : Int) ≤ (19 : Int) + 6
  decide
theorem c22108 (pattern : Twelve) (guard : d1 pattern = 1) : d5 pattern ≤ (19 : Int) + d6 pattern := by
  change (5 : Int) ≤ (19 : Int) + 6
  decide
theorem c22109 (pattern : Twelve) (guard : d1 pattern = 1) : d12 pattern ≤ (19 : Int) + d6 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22107 pattern childGuard
    simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22108 pattern childGuard
    simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22110 (pattern : Twelve) (guard : d1 pattern = 1) : d4 pattern ≤ (19 : Int) + d6 pattern := by
  change (4 : Int) ≤ (19 : Int) + 6
  decide
theorem c22111 (pattern : Twelve) (guard : d1 pattern = 1) : d13 pattern ≤ (19 : Int) + d6 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22110 pattern childGuard
    simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22101 pattern childGuard
    simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22112 (pattern : Twelve) (guard : d1 pattern = 1) : d20 pattern ≤ (19 : Int) + d6 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22109 pattern childGuard
    simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22111 pattern childGuard
    simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22113 (pattern : Twelve) (guard : d1 pattern = 1) : d31 pattern ≤ (19 : Int) + d35 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d31, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22074 pattern childGuard
    simpa only [d31, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d31, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22112 pattern childGuard
    simpa only [d31, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22114 (pattern : Twelve) (guard : d1 pattern = 1) : d52 pattern ≤ (19 : Int) + d56 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d52, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22106 pattern childGuard
    simpa only [d52, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d52, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22113 pattern childGuard
    simpa only [d52, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22115 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (19 : Int) + d2 pattern := by
  omega
theorem c22116 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (19 : Int) + d9 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22115 pattern childGuard
    simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22093 pattern childGuard
    simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22117 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (19 : Int) + d23 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22115 pattern childGuard
    simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22116 pattern childGuard
    simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22118 (pattern : Twelve) (guard : d1 pattern = 1) : d30 pattern ≤ (19 : Int) + d34 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d30, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22077 pattern childGuard
    simpa only [d30, d34, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d30, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22117 pattern childGuard
    simpa only [d30, d34, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22119 (pattern : Twelve) (guard : d1 pattern = 1) : d14 pattern ≤ (19 : Int) + d6 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22108 pattern childGuard
    simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22101 pattern childGuard
    simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
