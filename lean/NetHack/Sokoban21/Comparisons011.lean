/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons010
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c1540 (pattern : Twelve) (guard : d1849 pattern = 1) : d1696 pattern ≤ (0 : Int) + d1717 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1696, d1717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1494 pattern childGuard
    simpa only [d1696, d1717, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1696, d1717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1539 pattern childGuard
    simpa only [d1696, d1717, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1541 (pattern : Twelve) (guard : d1848 pattern = 1) : d822 pattern ≤ (0 : Int) + d822 pattern := by
  omega
theorem c1542 (pattern : Twelve) (guard : d1849 pattern = 1) : d1252 pattern ≤ (0 : Int) + d822 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d1252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1541 pattern childGuard
    simpa only [d1849, d1252, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d1252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c999 pattern childGuard
    simpa only [d1849, d1252, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1543 (pattern : Twelve) (guard : d1849 pattern = 1) : d1626 pattern ≤ (0 : Int) + d1655 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1626, d1655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1542 pattern childGuard
    simpa only [d1626, d1655, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1626, d1655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1350 pattern childGuard
    simpa only [d1626, d1655, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1544 (pattern : Twelve) (guard : d1849 pattern = 1) : d1699 pattern ≤ (0 : Int) + d1720 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1699, d1720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1540 pattern childGuard
    simpa only [d1699, d1720, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1699, d1720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1543 pattern childGuard
    simpa only [d1699, d1720, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1545 (pattern : Twelve) (guard : d1849 pattern = 1) : d1701 pattern ≤ (0 : Int) + d1722 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1701, d1722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1534 pattern childGuard
    simpa only [d1701, d1722, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1701, d1722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1544 pattern childGuard
    simpa only [d1701, d1722, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1546 (pattern : Twelve) (guard : d1849 pattern = 1) : d1702 pattern ≤ (0 : Int) + d1723 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1702, d1723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1534 pattern childGuard
    simpa only [d1702, d1723, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1702, d1723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1350 pattern childGuard
    simpa only [d1702, d1723, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1547 (pattern : Twelve) (guard : d1849 pattern = 1) : d1703 pattern ≤ (0 : Int) + d1725 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1703, d1725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1545 pattern childGuard
    simpa only [d1703, d1725, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1703, d1725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1546 pattern childGuard
    simpa only [d1703, d1725, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1548 (pattern : Twelve) (guard : d1849 pattern = 1) : d1704 pattern ≤ (0 : Int) + d1727 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1704, d1727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1535 pattern childGuard
    simpa only [d1704, d1727, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1704, d1727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1547 pattern childGuard
    simpa only [d1704, d1727, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1549 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d183 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1550 (pattern : Twelve) (guard : d1849 pattern = 1) : d1692 pattern ≤ (0 : Int) + d1667 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d1692, d1667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1538 pattern childGuard
    simpa only [d1849, d1692, d1667, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d1692, d1667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1549 pattern childGuard
    simpa only [d1849, d1692, d1667, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1551 (pattern : Twelve) (guard : d1849 pattern = 1) : d1696 pattern ≤ (0 : Int) + d1718 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1696, d1718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1494 pattern childGuard
    simpa only [d1696, d1718, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1696, d1718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1550 pattern childGuard
    simpa only [d1696, d1718, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1552 (pattern : Twelve) (guard : d1849 pattern = 1) : d1626 pattern ≤ (0 : Int) + d1626 pattern := by
  omega
theorem c1553 (pattern : Twelve) (guard : d1849 pattern = 1) : d1699 pattern ≤ (0 : Int) + d1721 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1699, d1721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1551 pattern childGuard
    simpa only [d1699, d1721, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1699, d1721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1552 pattern childGuard
    simpa only [d1699, d1721, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1554 (pattern : Twelve) (guard : d1849 pattern = 1) : d1701 pattern ≤ (0 : Int) + d1724 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1701, d1724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1534 pattern childGuard
    simpa only [d1701, d1724, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1701, d1724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1553 pattern childGuard
    simpa only [d1701, d1724, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1555 (pattern : Twelve) (guard : d1849 pattern = 1) : d1703 pattern ≤ (0 : Int) + d1726 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1703, d1726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1554 pattern childGuard
    simpa only [d1703, d1726, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1703, d1726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1546 pattern childGuard
    simpa only [d1703, d1726, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1556 (pattern : Twelve) (guard : d1849 pattern = 1) : d1704 pattern ≤ (0 : Int) + d1728 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1704, d1728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1535 pattern childGuard
    simpa only [d1704, d1728, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1704, d1728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1555 pattern childGuard
    simpa only [d1704, d1728, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1557 (pattern : Twelve) (guard : d1849 pattern = 1) : d1704 pattern ≤ (0 : Int) + d1729 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1548 pattern childGuard
    simpa only [d1729, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1556 pattern childGuard
    simpa only [d1729, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1558 (pattern : Twelve) (guard : d0 pattern = 1) : d236 pattern ≤ (0 : Int) + d185 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1559 (pattern : Twelve) (guard : d1853 pattern = 1) : d256 pattern ≤ (0 : Int) + d425 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1853, d256, d425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c811 pattern childGuard
    simpa only [d1853, d256, d425, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1853, d256, d425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1558 pattern childGuard
    simpa only [d1853, d256, d425, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1560 (pattern : Twelve) (guard : d1848 pattern = 1) : d0 pattern ≤ (0 : Int) + d0 pattern := by
  omega
theorem c1561 (pattern : Twelve) (guard : d1849 pattern = 1) : d237 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1560 pattern childGuard
    simpa only [d1849, d237, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c815 pattern childGuard
    simpa only [d1849, d237, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1562 (pattern : Twelve) (guard : d0 pattern = 1) : d238 pattern ≤ (0 : Int) + d186 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1563 (pattern : Twelve) (guard : d1854 pattern = 1) : d257 pattern ≤ (0 : Int) + d426 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1854, d257, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1561 pattern childGuard
    simpa only [d1854, d257, d426, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1854, d257, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1562 pattern childGuard
    simpa only [d1854, d257, d426, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1564 (pattern : Twelve) (guard : d1855 pattern = 1) : d272 pattern ≤ (0 : Int) + d444 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1853 pattern = 1 := by simpa only [d1855, d272, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1559 pattern childGuard
    simpa only [d1855, d272, d444, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1854 pattern = 1 := by simpa only [d1855, d272, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1563 pattern childGuard
    simpa only [d1855, d272, d444, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1565 (pattern : Twelve) (guard : d0 pattern = 1) : d240 pattern ≤ (0 : Int) + d188 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1566 (pattern : Twelve) (guard : d1853 pattern = 1) : d258 pattern ≤ (0 : Int) + d427 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1853, d258, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c822 pattern childGuard
    simpa only [d1853, d258, d427, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1853, d258, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1565 pattern childGuard
    simpa only [d1853, d258, d427, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1567 (pattern : Twelve) (guard : d1848 pattern = 1) : d30 pattern ≤ (0 : Int) + d30 pattern := by
  omega
theorem c1568 (pattern : Twelve) (guard : d1849 pattern = 1) : d240 pattern ≤ (0 : Int) + d54 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d240, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1567 pattern childGuard
    simpa only [d1849, d240, d54, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d240, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c826 pattern childGuard
    simpa only [d1849, d240, d54, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1569 (pattern : Twelve) (guard : d0 pattern = 1) : d241 pattern ≤ (0 : Int) + d189 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1570 (pattern : Twelve) (guard : d1854 pattern = 1) : d259 pattern ≤ (0 : Int) + d428 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1854, d259, d428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1568 pattern childGuard
    simpa only [d1854, d259, d428, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1854, d259, d428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1569 pattern childGuard
    simpa only [d1854, d259, d428, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1571 (pattern : Twelve) (guard : d1855 pattern = 1) : d273 pattern ≤ (0 : Int) + d445 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1853 pattern = 1 := by simpa only [d1855, d273, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1566 pattern childGuard
    simpa only [d1855, d273, d445, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1854 pattern = 1 := by simpa only [d1855, d273, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1570 pattern childGuard
    simpa only [d1855, d273, d445, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1572 (pattern : Twelve) (guard : d1855 pattern = 1) : d284 pattern ≤ (0 : Int) + d455 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d284, d455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1564 pattern childGuard
    simpa only [d284, d455, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d284, d455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1571 pattern childGuard
    simpa only [d284, d455, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1573 (pattern : Twelve) (guard : d0 pattern = 1) : d243 pattern ≤ (0 : Int) + d188 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1574 (pattern : Twelve) (guard : d1853 pattern = 1) : d260 pattern ≤ (0 : Int) + d429 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1853, d260, d429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c834 pattern childGuard
    simpa only [d1853, d260, d429, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1853, d260, d429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1573 pattern childGuard
    simpa only [d1853, d260, d429, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1575 (pattern : Twelve) (guard : d1849 pattern = 1) : d244 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1560 pattern childGuard
    simpa only [d1849, d244, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c838 pattern childGuard
    simpa only [d1849, d244, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1576 (pattern : Twelve) (guard : d1854 pattern = 1) : d261 pattern ≤ (0 : Int) + d430 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1854, d261, d430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1575 pattern childGuard
    simpa only [d1854, d261, d430, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1854, d261, d430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1569 pattern childGuard
    simpa only [d1854, d261, d430, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1577 (pattern : Twelve) (guard : d1855 pattern = 1) : d274 pattern ≤ (0 : Int) + d446 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1853 pattern = 1 := by simpa only [d1855, d274, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1574 pattern childGuard
    simpa only [d1855, d274, d446, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1854 pattern = 1 := by simpa only [d1855, d274, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1576 pattern childGuard
    simpa only [d1855, d274, d446, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1578 (pattern : Twelve) (guard : d0 pattern = 1) : d246 pattern ≤ (0 : Int) + d191 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1579 (pattern : Twelve) (guard : d1853 pattern = 1) : d262 pattern ≤ (0 : Int) + d431 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1853, d262, d431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c843 pattern childGuard
    simpa only [d1853, d262, d431, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1853, d262, d431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1578 pattern childGuard
    simpa only [d1853, d262, d431, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1580 (pattern : Twelve) (guard : d1849 pattern = 1) : d246 pattern ≤ (0 : Int) + d56 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d246, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1567 pattern childGuard
    simpa only [d1849, d246, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d246, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c847 pattern childGuard
    simpa only [d1849, d246, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1581 (pattern : Twelve) (guard : d0 pattern = 1) : d241 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1582 (pattern : Twelve) (guard : d1854 pattern = 1) : d263 pattern ≤ (0 : Int) + d432 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1854, d263, d432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1580 pattern childGuard
    simpa only [d1854, d263, d432, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1854, d263, d432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1581 pattern childGuard
    simpa only [d1854, d263, d432, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1583 (pattern : Twelve) (guard : d1855 pattern = 1) : d275 pattern ≤ (0 : Int) + d447 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1853 pattern = 1 := by simpa only [d1855, d275, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1579 pattern childGuard
    simpa only [d1855, d275, d447, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1854 pattern = 1 := by simpa only [d1855, d275, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1582 pattern childGuard
    simpa only [d1855, d275, d447, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1584 (pattern : Twelve) (guard : d1855 pattern = 1) : d285 pattern ≤ (0 : Int) + d456 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d285, d456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1577 pattern childGuard
    simpa only [d285, d456, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d285, d456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1583 pattern childGuard
    simpa only [d285, d456, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1585 (pattern : Twelve) (guard : d1855 pattern = 1) : d293 pattern ≤ (0 : Int) + d465 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d293, d465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1572 pattern childGuard
    simpa only [d293, d465, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d293, d465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1584 pattern childGuard
    simpa only [d293, d465, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1586 (pattern : Twelve) (guard : d0 pattern = 1) : d248 pattern ≤ (0 : Int) + d193 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1587 (pattern : Twelve) (guard : d1853 pattern = 1) : d264 pattern ≤ (0 : Int) + d433 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1853, d264, d433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c854 pattern childGuard
    simpa only [d1853, d264, d433, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1853, d264, d433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1586 pattern childGuard
    simpa only [d1853, d264, d433, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1588 (pattern : Twelve) (guard : d1849 pattern = 1) : d248 pattern ≤ (0 : Int) + d30 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1567 pattern childGuard
    simpa only [d1849, d248, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c858 pattern childGuard
    simpa only [d1849, d248, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1589 (pattern : Twelve) (guard : d0 pattern = 1) : d241 pattern ≤ (0 : Int) + d194 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1590 (pattern : Twelve) (guard : d1854 pattern = 1) : d265 pattern ≤ (0 : Int) + d434 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1854, d265, d434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1588 pattern childGuard
    simpa only [d1854, d265, d434, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1854, d265, d434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1589 pattern childGuard
    simpa only [d1854, d265, d434, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1591 (pattern : Twelve) (guard : d1855 pattern = 1) : d276 pattern ≤ (0 : Int) + d448 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1853 pattern = 1 := by simpa only [d1855, d276, d448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1587 pattern childGuard
    simpa only [d1855, d276, d448, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1854 pattern = 1 := by simpa only [d1855, d276, d448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1590 pattern childGuard
    simpa only [d1855, d276, d448, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1592 (pattern : Twelve) (guard : d0 pattern = 1) : d250 pattern ≤ (0 : Int) + d196 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1593 (pattern : Twelve) (guard : d1853 pattern = 1) : d266 pattern ≤ (0 : Int) + d435 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1853, d266, d435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c863 pattern childGuard
    simpa only [d1853, d266, d435, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1853, d266, d435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1592 pattern childGuard
    simpa only [d1853, d266, d435, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1594 (pattern : Twelve) (guard : d1848 pattern = 1) : d38 pattern ≤ (0 : Int) + d38 pattern := by
  omega
theorem c1595 (pattern : Twelve) (guard : d1849 pattern = 1) : d250 pattern ≤ (0 : Int) + d59 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d250, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1594 pattern childGuard
    simpa only [d1849, d250, d59, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d250, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c867 pattern childGuard
    simpa only [d1849, d250, d59, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1596 (pattern : Twelve) (guard : d0 pattern = 1) : d251 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1597 (pattern : Twelve) (guard : d1854 pattern = 1) : d267 pattern ≤ (0 : Int) + d436 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1854, d267, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1595 pattern childGuard
    simpa only [d1854, d267, d436, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1854, d267, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1596 pattern childGuard
    simpa only [d1854, d267, d436, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1598 (pattern : Twelve) (guard : d1855 pattern = 1) : d277 pattern ≤ (0 : Int) + d449 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1853 pattern = 1 := by simpa only [d1855, d277, d449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1593 pattern childGuard
    simpa only [d1855, d277, d449, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1854 pattern = 1 := by simpa only [d1855, d277, d449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1597 pattern childGuard
    simpa only [d1855, d277, d449, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1599 (pattern : Twelve) (guard : d1855 pattern = 1) : d286 pattern ≤ (0 : Int) + d457 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d286, d457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1591 pattern childGuard
    simpa only [d286, d457, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d286, d457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1598 pattern childGuard
    simpa only [d286, d457, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1600 (pattern : Twelve) (guard : d0 pattern = 1) : d246 pattern ≤ (0 : Int) + d196 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1601 (pattern : Twelve) (guard : d1853 pattern = 1) : d268 pattern ≤ (0 : Int) + d437 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1853, d268, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c875 pattern childGuard
    simpa only [d1853, d268, d437, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1853, d268, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1600 pattern childGuard
    simpa only [d1853, d268, d437, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1602 (pattern : Twelve) (guard : d1855 pattern = 1) : d278 pattern ≤ (0 : Int) + d450 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1853 pattern = 1 := by simpa only [d1855, d278, d450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1601 pattern childGuard
    simpa only [d1855, d278, d450, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1854 pattern = 1 := by simpa only [d1855, d278, d450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1582 pattern childGuard
    simpa only [d1855, d278, d450, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1603 (pattern : Twelve) (guard : d1855 pattern = 1) : d6 pattern ≤ (0 : Int) + d6 pattern := by
  omega
theorem c1604 (pattern : Twelve) (guard : d1855 pattern = 1) : d287 pattern ≤ (0 : Int) + d458 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d287, d458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1602 pattern childGuard
    simpa only [d287, d458, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d287, d458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1603 pattern childGuard
    simpa only [d287, d458, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1605 (pattern : Twelve) (guard : d1855 pattern = 1) : d294 pattern ≤ (0 : Int) + d466 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d294, d466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1599 pattern childGuard
    simpa only [d294, d466, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d294, d466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1604 pattern childGuard
    simpa only [d294, d466, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1606 (pattern : Twelve) (guard : d1855 pattern = 1) : d297 pattern ≤ (0 : Int) + d471 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d297, d471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1585 pattern childGuard
    simpa only [d297, d471, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d297, d471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1605 pattern childGuard
    simpa only [d297, d471, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1607 (pattern : Twelve) (guard : d0 pattern = 1) : d254 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1608 (pattern : Twelve) (guard : d1853 pattern = 1) : d269 pattern ≤ (0 : Int) + d438 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1853, d269, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c882 pattern childGuard
    simpa only [d1853, d269, d438, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1853, d269, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1607 pattern childGuard
    simpa only [d1853, d269, d438, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1609 (pattern : Twelve) (guard : d0 pattern = 1) : d2 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1610 (pattern : Twelve) (guard : d1848 pattern = 1) : d30 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1848, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1609 pattern childGuard
    simpa only [d1848, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1611 (pattern : Twelve) (guard : d1849 pattern = 1) : d246 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1610 pattern childGuard
    simpa only [d1849, d246, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c881 pattern childGuard
    simpa only [d1849, d246, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1612 (pattern : Twelve) (guard : d1854 pattern = 1) : d263 pattern ≤ (0 : Int) + d438 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1854, d263, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1611 pattern childGuard
    simpa only [d1854, d263, d438, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1854, d263, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1581 pattern childGuard
    simpa only [d1854, d263, d438, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1613 (pattern : Twelve) (guard : d1855 pattern = 1) : d279 pattern ≤ (0 : Int) + d438 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1853 pattern = 1 := by simpa only [d1855, d279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1608 pattern childGuard
    simpa only [d1855, d279, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1854 pattern = 1 := by simpa only [d1855, d279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1612 pattern childGuard
    simpa only [d1855, d279, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1614 (pattern : Twelve) (guard : d0 pattern = 1) : d246 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1615 (pattern : Twelve) (guard : d1853 pattern = 1) : d246 pattern ≤ (0 : Int) + d439 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1853, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c891 pattern childGuard
    simpa only [d1853, d439, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1853, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1614 pattern childGuard
    simpa only [d1853, d439, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1616 (pattern : Twelve) (guard : d1849 pattern = 1) : d246 pattern ≤ (0 : Int) + d54 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d246, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1567 pattern childGuard
    simpa only [d1849, d246, d54, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d246, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c936 pattern childGuard
    simpa only [d1849, d246, d54, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1617 (pattern : Twelve) (guard : d1854 pattern = 1) : d263 pattern ≤ (0 : Int) + d440 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1854, d263, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1616 pattern childGuard
    simpa only [d1854, d263, d440, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1854, d263, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1581 pattern childGuard
    simpa only [d1854, d263, d440, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1618 (pattern : Twelve) (guard : d1855 pattern = 1) : d280 pattern ≤ (0 : Int) + d451 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1853 pattern = 1 := by simpa only [d1855, d280, d451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1615 pattern childGuard
    simpa only [d1855, d280, d451, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1854 pattern = 1 := by simpa only [d1855, d280, d451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1617 pattern childGuard
    simpa only [d1855, d280, d451, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1619 (pattern : Twelve) (guard : d1855 pattern = 1) : d288 pattern ≤ (0 : Int) + d459 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d288, d459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1613 pattern childGuard
    simpa only [d288, d459, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d288, d459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1618 pattern childGuard
    simpa only [d288, d459, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1620 (pattern : Twelve) (guard : d1853 pattern = 1) : d246 pattern ≤ (0 : Int) + d432 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1853, d432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c848 pattern childGuard
    simpa only [d1853, d432, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1853, d432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1614 pattern childGuard
    simpa only [d1853, d432, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1621 (pattern : Twelve) (guard : d1855 pattern = 1) : d280 pattern ≤ (0 : Int) + d432 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1853 pattern = 1 := by simpa only [d1855, d280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1620 pattern childGuard
    simpa only [d1855, d280, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1854 pattern = 1 := by simpa only [d1855, d280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1582 pattern childGuard
    simpa only [d1855, d280, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1622 (pattern : Twelve) (guard : d1855 pattern = 1) : d288 pattern ≤ (0 : Int) + d460 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d288, d460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1613 pattern childGuard
    simpa only [d288, d460, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d288, d460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1621 pattern childGuard
    simpa only [d288, d460, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1623 (pattern : Twelve) (guard : d1855 pattern = 1) : d288 pattern ≤ (0 : Int) + d467 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1619 pattern childGuard
    simpa only [d467, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1622 pattern childGuard
    simpa only [d467, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1624 (pattern : Twelve) (guard : d1853 pattern = 1) : d246 pattern ≤ (0 : Int) + d441 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1853, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c887 pattern childGuard
    simpa only [d1853, d441, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1853, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1614 pattern childGuard
    simpa only [d1853, d441, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1625 (pattern : Twelve) (guard : d1849 pattern = 1) : d246 pattern ≤ (0 : Int) + d30 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1567 pattern childGuard
    simpa only [d1849, d246, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c886 pattern childGuard
    simpa only [d1849, d246, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1626 (pattern : Twelve) (guard : d1854 pattern = 1) : d263 pattern ≤ (0 : Int) + d441 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1854, d263, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1625 pattern childGuard
    simpa only [d1854, d263, d441, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1854, d263, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1581 pattern childGuard
    simpa only [d1854, d263, d441, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1627 (pattern : Twelve) (guard : d1855 pattern = 1) : d280 pattern ≤ (0 : Int) + d441 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1853 pattern = 1 := by simpa only [d1855, d280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1624 pattern childGuard
    simpa only [d1855, d280, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1854 pattern = 1 := by simpa only [d1855, d280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1626 pattern childGuard
    simpa only [d1855, d280, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1628 (pattern : Twelve) (guard : d0 pattern = 1) : d250 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1629 (pattern : Twelve) (guard : d1853 pattern = 1) : d250 pattern ≤ (0 : Int) + d436 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1853, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c868 pattern childGuard
    simpa only [d1853, d436, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1853, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1628 pattern childGuard
    simpa only [d1853, d436, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1630 (pattern : Twelve) (guard : d1855 pattern = 1) : d281 pattern ≤ (0 : Int) + d436 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1853 pattern = 1 := by simpa only [d1855, d281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1629 pattern childGuard
    simpa only [d1855, d281, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1854 pattern = 1 := by simpa only [d1855, d281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1597 pattern childGuard
    simpa only [d1855, d281, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1631 (pattern : Twelve) (guard : d1855 pattern = 1) : d289 pattern ≤ (0 : Int) + d461 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d289, d461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1627 pattern childGuard
    simpa only [d289, d461, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d289, d461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1630 pattern childGuard
    simpa only [d289, d461, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1632 (pattern : Twelve) (guard : d1855 pattern = 1) : d290 pattern ≤ (0 : Int) + d462 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d290, d462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1621 pattern childGuard
    simpa only [d290, d462, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d290, d462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1603 pattern childGuard
    simpa only [d290, d462, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1633 (pattern : Twelve) (guard : d1855 pattern = 1) : d295 pattern ≤ (0 : Int) + d468 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d295, d468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1631 pattern childGuard
    simpa only [d295, d468, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d295, d468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1632 pattern childGuard
    simpa only [d295, d468, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1634 (pattern : Twelve) (guard : d1855 pattern = 1) : d298 pattern ≤ (0 : Int) + d472 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d298, d472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1623 pattern childGuard
    simpa only [d298, d472, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d298, d472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1633 pattern childGuard
    simpa only [d298, d472, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1635 (pattern : Twelve) (guard : d1855 pattern = 1) : d300 pattern ≤ (0 : Int) + d474 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d300, d474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1606 pattern childGuard
    simpa only [d300, d474, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d300, d474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1634 pattern childGuard
    simpa only [d300, d474, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1636 (pattern : Twelve) (guard : d1849 pattern = 1) : d253 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1560 pattern childGuard
    simpa only [d1849, d253, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c881 pattern childGuard
    simpa only [d1849, d253, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1637 (pattern : Twelve) (guard : d0 pattern = 1) : d255 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1638 (pattern : Twelve) (guard : d1854 pattern = 1) : d270 pattern ≤ (0 : Int) + d438 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1854, d270, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1636 pattern childGuard
    simpa only [d1854, d270, d438, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1854, d270, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1637 pattern childGuard
    simpa only [d1854, d270, d438, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1639 (pattern : Twelve) (guard : d1855 pattern = 1) : d282 pattern ≤ (0 : Int) + d438 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1853 pattern = 1 := by simpa only [d1855, d282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1608 pattern childGuard
    simpa only [d1855, d282, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1854 pattern = 1 := by simpa only [d1855, d282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1638 pattern childGuard
    simpa only [d1855, d282, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1640 (pattern : Twelve) (guard : d1855 pattern = 1) : d291 pattern ≤ (0 : Int) + d459 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d291, d459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1639 pattern childGuard
    simpa only [d291, d459, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d291, d459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1618 pattern childGuard
    simpa only [d291, d459, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1641 (pattern : Twelve) (guard : d1854 pattern = 1) : d271 pattern ≤ (0 : Int) + d438 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1854, d271, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1636 pattern childGuard
    simpa only [d1854, d271, d438, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1854, d271, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1581 pattern childGuard
    simpa only [d1854, d271, d438, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1642 (pattern : Twelve) (guard : d1855 pattern = 1) : d283 pattern ≤ (0 : Int) + d438 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1853 pattern = 1 := by simpa only [d1855, d283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1608 pattern childGuard
    simpa only [d1855, d283, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1854 pattern = 1 := by simpa only [d1855, d283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1641 pattern childGuard
    simpa only [d1855, d283, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1643 (pattern : Twelve) (guard : d1855 pattern = 1) : d292 pattern ≤ (0 : Int) + d460 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d292, d460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1642 pattern childGuard
    simpa only [d292, d460, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d292, d460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1621 pattern childGuard
    simpa only [d292, d460, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1644 (pattern : Twelve) (guard : d1855 pattern = 1) : d296 pattern ≤ (0 : Int) + d467 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d296, d467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1640 pattern childGuard
    simpa only [d296, d467, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d296, d467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1643 pattern childGuard
    simpa only [d296, d467, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1645 (pattern : Twelve) (guard : d1855 pattern = 1) : d299 pattern ≤ (0 : Int) + d472 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d299, d472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1644 pattern childGuard
    simpa only [d299, d472, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d299, d472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1633 pattern childGuard
    simpa only [d299, d472, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1646 (pattern : Twelve) (guard : d1855 pattern = 1) : d301 pattern ≤ (0 : Int) + d472 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1645 pattern childGuard
    simpa only [d301, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1634 pattern childGuard
    simpa only [d301, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1647 (pattern : Twelve) (guard : d1855 pattern = 1) : d302 pattern ≤ (0 : Int) + d475 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d302, d475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1635 pattern childGuard
    simpa only [d302, d475, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d302, d475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1646 pattern childGuard
    simpa only [d302, d475, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1648 (pattern : Twelve) (guard : d1855 pattern = 1) : d280 pattern ≤ (0 : Int) + d452 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1853 pattern = 1 := by simpa only [d1855, d280, d452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1615 pattern childGuard
    simpa only [d1855, d280, d452, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1854 pattern = 1 := by simpa only [d1855, d280, d452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1582 pattern childGuard
    simpa only [d1855, d280, d452, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1649 (pattern : Twelve) (guard : d1855 pattern = 1) : d291 pattern ≤ (0 : Int) + d463 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d291, d463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1639 pattern childGuard
    simpa only [d291, d463, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d291, d463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1648 pattern childGuard
    simpa only [d291, d463, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1650 (pattern : Twelve) (guard : d1855 pattern = 1) : d296 pattern ≤ (0 : Int) + d469 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d296, d469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1649 pattern childGuard
    simpa only [d296, d469, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d296, d469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1643 pattern childGuard
    simpa only [d296, d469, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1651 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d123 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1652 (pattern : Twelve) (guard : d1849 pattern = 1) : d246 pattern ≤ (0 : Int) + d132 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d246, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1567 pattern childGuard
    simpa only [d1849, d246, d132, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d246, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1651 pattern childGuard
    simpa only [d1849, d246, d132, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1653 (pattern : Twelve) (guard : d1854 pattern = 1) : d263 pattern ≤ (0 : Int) + d442 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1854, d263, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1652 pattern childGuard
    simpa only [d1854, d263, d442, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1854, d263, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1581 pattern childGuard
    simpa only [d1854, d263, d442, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1654 (pattern : Twelve) (guard : d1855 pattern = 1) : d280 pattern ≤ (0 : Int) + d453 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1853 pattern = 1 := by simpa only [d1855, d280, d453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1624 pattern childGuard
    simpa only [d1855, d280, d453, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1854 pattern = 1 := by simpa only [d1855, d280, d453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1653 pattern childGuard
    simpa only [d1855, d280, d453, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1655 (pattern : Twelve) (guard : d0 pattern = 1) : d4 pattern ≤ (0 : Int) + d5 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1656 (pattern : Twelve) (guard : d1848 pattern = 1) : d38 pattern ≤ (0 : Int) + d126 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d38, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1333 pattern childGuard
    simpa only [d1848, d38, d126, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d38, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1655 pattern childGuard
    simpa only [d1848, d38, d126, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1657 (pattern : Twelve) (guard : d1849 pattern = 1) : d250 pattern ≤ (0 : Int) + d134 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d250, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1656 pattern childGuard
    simpa only [d1849, d250, d134, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d250, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c916 pattern childGuard
    simpa only [d1849, d250, d134, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1658 (pattern : Twelve) (guard : d1854 pattern = 1) : d267 pattern ≤ (0 : Int) + d443 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1854, d267, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1657 pattern childGuard
    simpa only [d1854, d267, d443, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1854, d267, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1596 pattern childGuard
    simpa only [d1854, d267, d443, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1659 (pattern : Twelve) (guard : d1855 pattern = 1) : d281 pattern ≤ (0 : Int) + d454 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1853 pattern = 1 := by simpa only [d1855, d281, d454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1629 pattern childGuard
    simpa only [d1855, d281, d454, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1854 pattern = 1 := by simpa only [d1855, d281, d454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1658 pattern childGuard
    simpa only [d1855, d281, d454, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1660 (pattern : Twelve) (guard : d1855 pattern = 1) : d289 pattern ≤ (0 : Int) + d464 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d289, d464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1654 pattern childGuard
    simpa only [d289, d464, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d289, d464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1659 pattern childGuard
    simpa only [d289, d464, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1661 (pattern : Twelve) (guard : d1855 pattern = 1) : d295 pattern ≤ (0 : Int) + d470 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d295, d470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1660 pattern childGuard
    simpa only [d295, d470, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d295, d470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1632 pattern childGuard
    simpa only [d295, d470, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1662 (pattern : Twelve) (guard : d1855 pattern = 1) : d299 pattern ≤ (0 : Int) + d473 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d299, d473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1650 pattern childGuard
    simpa only [d299, d473, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d299, d473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1661 pattern childGuard
    simpa only [d299, d473, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1663 (pattern : Twelve) (guard : d1855 pattern = 1) : d288 pattern ≤ (0 : Int) + d463 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d288, d463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1613 pattern childGuard
    simpa only [d288, d463, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d288, d463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1648 pattern childGuard
    simpa only [d288, d463, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1664 (pattern : Twelve) (guard : d1855 pattern = 1) : d288 pattern ≤ (0 : Int) + d469 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1663 pattern childGuard
    simpa only [d469, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1622 pattern childGuard
    simpa only [d469, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1665 (pattern : Twelve) (guard : d1855 pattern = 1) : d298 pattern ≤ (0 : Int) + d473 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d298, d473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1664 pattern childGuard
    simpa only [d298, d473, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d298, d473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1661 pattern childGuard
    simpa only [d298, d473, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1666 (pattern : Twelve) (guard : d1855 pattern = 1) : d301 pattern ≤ (0 : Int) + d473 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1662 pattern childGuard
    simpa only [d301, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1665 pattern childGuard
    simpa only [d301, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1667 (pattern : Twelve) (guard : d1855 pattern = 1) : d303 pattern ≤ (0 : Int) + d476 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d303, d476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1647 pattern childGuard
    simpa only [d303, d476, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d303, d476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1666 pattern childGuard
    simpa only [d303, d476, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1668 (pattern : Twelve) (guard : d0 pattern = 1) : d940 pattern ≤ (0 : Int) + d186 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1669 (pattern : Twelve) (guard : d1853 pattern = 1) : d947 pattern ≤ (0 : Int) + d426 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1853, d947, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c816 pattern childGuard
    simpa only [d1853, d947, d426, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1853, d947, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1668 pattern childGuard
    simpa only [d1853, d947, d426, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1670 (pattern : Twelve) (guard : d1848 pattern = 1) : d17 pattern ≤ (0 : Int) + d17 pattern := by
  omega
theorem c1671 (pattern : Twelve) (guard : d1849 pattern = 1) : d941 pattern ≤ (0 : Int) + d17 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1670 pattern childGuard
    simpa only [d1849, d941, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c963 pattern childGuard
    simpa only [d1849, d941, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1672 (pattern : Twelve) (guard : d0 pattern = 1) : d942 pattern ≤ (0 : Int) + d908 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1673 (pattern : Twelve) (guard : d1854 pattern = 1) : d948 pattern ≤ (0 : Int) + d1070 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1854, d948, d1070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1671 pattern childGuard
    simpa only [d1854, d948, d1070, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1854, d948, d1070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1672 pattern childGuard
    simpa only [d1854, d948, d1070, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1674 (pattern : Twelve) (guard : d1855 pattern = 1) : d955 pattern ≤ (0 : Int) + d1078 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1853 pattern = 1 := by simpa only [d1855, d955, d1078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1669 pattern childGuard
    simpa only [d1855, d955, d1078, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1854 pattern = 1 := by simpa only [d1855, d955, d1078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1673 pattern childGuard
    simpa only [d1855, d955, d1078, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1675 (pattern : Twelve) (guard : d1853 pattern = 1) : d259 pattern ≤ (0 : Int) + d1071 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1853, d259, d1071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c969 pattern childGuard
    simpa only [d1853, d259, d1071, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1853, d259, d1071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1569 pattern childGuard
    simpa only [d1853, d259, d1071, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1676 (pattern : Twelve) (guard : d1848 pattern = 1) : d34 pattern ≤ (0 : Int) + d34 pattern := by
  omega
theorem c1677 (pattern : Twelve) (guard : d1849 pattern = 1) : d241 pattern ≤ (0 : Int) + d827 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d241, d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1676 pattern childGuard
    simpa only [d1849, d241, d827, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d241, d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c844 pattern childGuard
    simpa only [d1849, d241, d827, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1678 (pattern : Twelve) (guard : d0 pattern = 1) : d942 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1679 (pattern : Twelve) (guard : d1854 pattern = 1) : d949 pattern ≤ (0 : Int) + d1072 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1854, d949, d1072, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1677 pattern childGuard
    simpa only [d1854, d949, d1072, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1854, d949, d1072, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1678 pattern childGuard
    simpa only [d1854, d949, d1072, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
