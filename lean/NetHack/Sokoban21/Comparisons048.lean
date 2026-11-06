/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons047
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c6720 (pattern : Twelve) (guard : d1870 pattern = 1) : d1732 pattern ≤ (0 : Int) + d1719 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1732, d1719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6718 pattern childGuard
    simpa only [d1732, d1719, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1732, d1719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6719 pattern childGuard
    simpa only [d1732, d1719, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6721 (pattern : Twelve) (guard : d1870 pattern = 1) : d1300 pattern ≤ (0 : Int) + d1717 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1870, d1300, d1717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2807 pattern childGuard
    simpa only [d1870, d1300, d1717, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1870, d1300, d1717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1121 pattern childGuard
    simpa only [d1870, d1300, d1717, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6722 (pattern : Twelve) (guard : d1870 pattern = 1) : d1733 pattern ≤ (0 : Int) + d1720 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1733, d1720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6721 pattern childGuard
    simpa only [d1733, d1720, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1733, d1720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5464 pattern childGuard
    simpa only [d1733, d1720, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6723 (pattern : Twelve) (guard : d1870 pattern = 1) : d1737 pattern ≤ (0 : Int) + d1722 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1737, d1722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6720 pattern childGuard
    simpa only [d1737, d1722, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1737, d1722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6722 pattern childGuard
    simpa only [d1737, d1722, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6724 (pattern : Twelve) (guard : d1870 pattern = 1) : d1738 pattern ≤ (0 : Int) + d1723 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1738, d1723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6716 pattern childGuard
    simpa only [d1738, d1723, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1738, d1723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5294 pattern childGuard
    simpa only [d1738, d1723, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6725 (pattern : Twelve) (guard : d1870 pattern = 1) : d1740 pattern ≤ (0 : Int) + d1725 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1740, d1725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6723 pattern childGuard
    simpa only [d1740, d1725, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1740, d1725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6724 pattern childGuard
    simpa only [d1740, d1725, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6726 (pattern : Twelve) (guard : d1870 pattern = 1) : d1742 pattern ≤ (0 : Int) + d1727 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1742, d1727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6717 pattern childGuard
    simpa only [d1742, d1727, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1742, d1727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6725 pattern childGuard
    simpa only [d1742, d1727, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6727 (pattern : Twelve) (guard : d1870 pattern = 1) : d1734 pattern ≤ (0 : Int) + d1719 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1734, d1719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6718 pattern childGuard
    simpa only [d1734, d1719, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1734, d1719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6690 pattern childGuard
    simpa only [d1734, d1719, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6728 (pattern : Twelve) (guard : d1870 pattern = 1) : d1300 pattern ≤ (0 : Int) + d1718 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1870, d1300, d1718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2807 pattern childGuard
    simpa only [d1870, d1300, d1718, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1870, d1300, d1718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6523 pattern childGuard
    simpa only [d1870, d1300, d1718, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6729 (pattern : Twelve) (guard : d1870 pattern = 1) : d1735 pattern ≤ (0 : Int) + d1721 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1735, d1721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6728 pattern childGuard
    simpa only [d1735, d1721, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1735, d1721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5473 pattern childGuard
    simpa only [d1735, d1721, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6730 (pattern : Twelve) (guard : d1870 pattern = 1) : d1739 pattern ≤ (0 : Int) + d1724 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1739, d1724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6727 pattern childGuard
    simpa only [d1739, d1724, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1739, d1724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6729 pattern childGuard
    simpa only [d1739, d1724, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6731 (pattern : Twelve) (guard : d1870 pattern = 1) : d1741 pattern ≤ (0 : Int) + d1726 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1741, d1726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6730 pattern childGuard
    simpa only [d1741, d1726, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1741, d1726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6724 pattern childGuard
    simpa only [d1741, d1726, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6732 (pattern : Twelve) (guard : d1870 pattern = 1) : d1743 pattern ≤ (0 : Int) + d1728 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1743, d1728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6717 pattern childGuard
    simpa only [d1743, d1728, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1743, d1728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6731 pattern childGuard
    simpa only [d1743, d1728, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6733 (pattern : Twelve) (guard : d1870 pattern = 1) : d1744 pattern ≤ (0 : Int) + d1729 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1744, d1729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6726 pattern childGuard
    simpa only [d1744, d1729, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1744, d1729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6732 pattern childGuard
    simpa only [d1744, d1729, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6734 (pattern : Twelve) (guard : d0 pattern = 1) : d185 pattern ≤ (0 : Int) + d236 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6735 (pattern : Twelve) (guard : d1853 pattern = 1) : d425 pattern ≤ (0 : Int) + d256 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1853, d425, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c80 pattern childGuard
    simpa only [d1853, d425, d256, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1853, d425, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6734 pattern childGuard
    simpa only [d1853, d425, d256, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6736 (pattern : Twelve) (guard : d0 pattern = 1) : d186 pattern ≤ (0 : Int) + d238 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6737 (pattern : Twelve) (guard : d1854 pattern = 1) : d426 pattern ≤ (0 : Int) + d257 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1854, d426, d257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4387 pattern childGuard
    simpa only [d1854, d426, d257, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1854, d426, d257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6736 pattern childGuard
    simpa only [d1854, d426, d257, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6738 (pattern : Twelve) (guard : d1855 pattern = 1) : d444 pattern ≤ (0 : Int) + d272 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1853 pattern = 1 := by simpa only [d1855, d444, d272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6735 pattern childGuard
    simpa only [d1855, d444, d272, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1854 pattern = 1 := by simpa only [d1855, d444, d272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6737 pattern childGuard
    simpa only [d1855, d444, d272, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6739 (pattern : Twelve) (guard : d0 pattern = 1) : d188 pattern ≤ (0 : Int) + d240 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6740 (pattern : Twelve) (guard : d1853 pattern = 1) : d427 pattern ≤ (0 : Int) + d258 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1853, d427, d258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c94 pattern childGuard
    simpa only [d1853, d427, d258, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1853, d427, d258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6739 pattern childGuard
    simpa only [d1853, d427, d258, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6741 (pattern : Twelve) (guard : d1849 pattern = 1) : d54 pattern ≤ (0 : Int) + d240 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d54, d240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1567 pattern childGuard
    simpa only [d1849, d54, d240, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d54, d240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c98 pattern childGuard
    simpa only [d1849, d54, d240, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6742 (pattern : Twelve) (guard : d0 pattern = 1) : d189 pattern ≤ (0 : Int) + d241 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6743 (pattern : Twelve) (guard : d1854 pattern = 1) : d428 pattern ≤ (0 : Int) + d259 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1854, d428, d259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6741 pattern childGuard
    simpa only [d1854, d428, d259, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1854, d428, d259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6742 pattern childGuard
    simpa only [d1854, d428, d259, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6744 (pattern : Twelve) (guard : d1855 pattern = 1) : d445 pattern ≤ (0 : Int) + d273 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1853 pattern = 1 := by simpa only [d1855, d445, d273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6740 pattern childGuard
    simpa only [d1855, d445, d273, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1854 pattern = 1 := by simpa only [d1855, d445, d273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6743 pattern childGuard
    simpa only [d1855, d445, d273, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6745 (pattern : Twelve) (guard : d1855 pattern = 1) : d455 pattern ≤ (0 : Int) + d284 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d455, d284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6738 pattern childGuard
    simpa only [d455, d284, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d455, d284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6744 pattern childGuard
    simpa only [d455, d284, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6746 (pattern : Twelve) (guard : d0 pattern = 1) : d188 pattern ≤ (0 : Int) + d243 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6747 (pattern : Twelve) (guard : d1853 pattern = 1) : d429 pattern ≤ (0 : Int) + d260 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1853, d429, d260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c107 pattern childGuard
    simpa only [d1853, d429, d260, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1853, d429, d260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6746 pattern childGuard
    simpa only [d1853, d429, d260, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6748 (pattern : Twelve) (guard : d1854 pattern = 1) : d430 pattern ≤ (0 : Int) + d261 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1854, d430, d261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4396 pattern childGuard
    simpa only [d1854, d430, d261, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1854, d430, d261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6742 pattern childGuard
    simpa only [d1854, d430, d261, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6749 (pattern : Twelve) (guard : d1855 pattern = 1) : d446 pattern ≤ (0 : Int) + d274 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1853 pattern = 1 := by simpa only [d1855, d446, d274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6747 pattern childGuard
    simpa only [d1855, d446, d274, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1854 pattern = 1 := by simpa only [d1855, d446, d274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6748 pattern childGuard
    simpa only [d1855, d446, d274, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6750 (pattern : Twelve) (guard : d0 pattern = 1) : d191 pattern ≤ (0 : Int) + d246 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6751 (pattern : Twelve) (guard : d1853 pattern = 1) : d431 pattern ≤ (0 : Int) + d262 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1853, d431, d262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c116 pattern childGuard
    simpa only [d1853, d431, d262, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1853, d431, d262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6750 pattern childGuard
    simpa only [d1853, d431, d262, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6752 (pattern : Twelve) (guard : d1849 pattern = 1) : d56 pattern ≤ (0 : Int) + d246 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d56, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1567 pattern childGuard
    simpa only [d1849, d56, d246, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d56, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c120 pattern childGuard
    simpa only [d1849, d56, d246, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6753 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d241 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6754 (pattern : Twelve) (guard : d1854 pattern = 1) : d432 pattern ≤ (0 : Int) + d263 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1854, d432, d263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6752 pattern childGuard
    simpa only [d1854, d432, d263, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1854, d432, d263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6753 pattern childGuard
    simpa only [d1854, d432, d263, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6755 (pattern : Twelve) (guard : d1855 pattern = 1) : d447 pattern ≤ (0 : Int) + d275 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1853 pattern = 1 := by simpa only [d1855, d447, d275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6751 pattern childGuard
    simpa only [d1855, d447, d275, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1854 pattern = 1 := by simpa only [d1855, d447, d275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6754 pattern childGuard
    simpa only [d1855, d447, d275, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6756 (pattern : Twelve) (guard : d1855 pattern = 1) : d456 pattern ≤ (0 : Int) + d285 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d456, d285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6749 pattern childGuard
    simpa only [d456, d285, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d456, d285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6755 pattern childGuard
    simpa only [d456, d285, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6757 (pattern : Twelve) (guard : d1855 pattern = 1) : d465 pattern ≤ (0 : Int) + d293 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d465, d293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6745 pattern childGuard
    simpa only [d465, d293, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d465, d293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6756 pattern childGuard
    simpa only [d465, d293, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6758 (pattern : Twelve) (guard : d0 pattern = 1) : d193 pattern ≤ (0 : Int) + d248 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6759 (pattern : Twelve) (guard : d1853 pattern = 1) : d433 pattern ≤ (0 : Int) + d264 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1853, d433, d264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c127 pattern childGuard
    simpa only [d1853, d433, d264, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1853, d433, d264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6758 pattern childGuard
    simpa only [d1853, d433, d264, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6760 (pattern : Twelve) (guard : d1849 pattern = 1) : d30 pattern ≤ (0 : Int) + d248 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1567 pattern childGuard
    simpa only [d1849, d248, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c131 pattern childGuard
    simpa only [d1849, d248, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6761 (pattern : Twelve) (guard : d0 pattern = 1) : d194 pattern ≤ (0 : Int) + d241 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6762 (pattern : Twelve) (guard : d1854 pattern = 1) : d434 pattern ≤ (0 : Int) + d265 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1854, d434, d265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6760 pattern childGuard
    simpa only [d1854, d434, d265, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1854, d434, d265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6761 pattern childGuard
    simpa only [d1854, d434, d265, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6763 (pattern : Twelve) (guard : d1855 pattern = 1) : d448 pattern ≤ (0 : Int) + d276 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1853 pattern = 1 := by simpa only [d1855, d448, d276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6759 pattern childGuard
    simpa only [d1855, d448, d276, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1854 pattern = 1 := by simpa only [d1855, d448, d276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6762 pattern childGuard
    simpa only [d1855, d448, d276, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6764 (pattern : Twelve) (guard : d0 pattern = 1) : d196 pattern ≤ (0 : Int) + d250 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6765 (pattern : Twelve) (guard : d1853 pattern = 1) : d435 pattern ≤ (0 : Int) + d266 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1853, d435, d266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c137 pattern childGuard
    simpa only [d1853, d435, d266, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1853, d435, d266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6764 pattern childGuard
    simpa only [d1853, d435, d266, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6766 (pattern : Twelve) (guard : d1849 pattern = 1) : d59 pattern ≤ (0 : Int) + d250 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d59, d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1594 pattern childGuard
    simpa only [d1849, d59, d250, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d59, d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c141 pattern childGuard
    simpa only [d1849, d59, d250, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6767 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d251 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6768 (pattern : Twelve) (guard : d1854 pattern = 1) : d436 pattern ≤ (0 : Int) + d267 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1854, d436, d267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6766 pattern childGuard
    simpa only [d1854, d436, d267, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1854, d436, d267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6767 pattern childGuard
    simpa only [d1854, d436, d267, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6769 (pattern : Twelve) (guard : d1855 pattern = 1) : d449 pattern ≤ (0 : Int) + d277 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1853 pattern = 1 := by simpa only [d1855, d449, d277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6765 pattern childGuard
    simpa only [d1855, d449, d277, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1854 pattern = 1 := by simpa only [d1855, d449, d277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6768 pattern childGuard
    simpa only [d1855, d449, d277, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6770 (pattern : Twelve) (guard : d1855 pattern = 1) : d457 pattern ≤ (0 : Int) + d286 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d457, d286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6763 pattern childGuard
    simpa only [d457, d286, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d457, d286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6769 pattern childGuard
    simpa only [d457, d286, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6771 (pattern : Twelve) (guard : d0 pattern = 1) : d196 pattern ≤ (0 : Int) + d246 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6772 (pattern : Twelve) (guard : d1853 pattern = 1) : d437 pattern ≤ (0 : Int) + d268 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1853, d437, d268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c150 pattern childGuard
    simpa only [d1853, d437, d268, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1853, d437, d268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6771 pattern childGuard
    simpa only [d1853, d437, d268, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6773 (pattern : Twelve) (guard : d1855 pattern = 1) : d450 pattern ≤ (0 : Int) + d278 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1853 pattern = 1 := by simpa only [d1855, d450, d278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6772 pattern childGuard
    simpa only [d1855, d450, d278, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1854 pattern = 1 := by simpa only [d1855, d450, d278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6754 pattern childGuard
    simpa only [d1855, d450, d278, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6774 (pattern : Twelve) (guard : d1855 pattern = 1) : d458 pattern ≤ (0 : Int) + d287 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d458, d287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6773 pattern childGuard
    simpa only [d458, d287, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d458, d287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1603 pattern childGuard
    simpa only [d458, d287, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6775 (pattern : Twelve) (guard : d1855 pattern = 1) : d466 pattern ≤ (0 : Int) + d294 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d466, d294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6770 pattern childGuard
    simpa only [d466, d294, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d466, d294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6774 pattern childGuard
    simpa only [d466, d294, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6776 (pattern : Twelve) (guard : d1855 pattern = 1) : d471 pattern ≤ (0 : Int) + d297 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d471, d297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6757 pattern childGuard
    simpa only [d471, d297, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d471, d297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6775 pattern childGuard
    simpa only [d471, d297, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6777 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d254 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6778 (pattern : Twelve) (guard : d1853 pattern = 1) : d438 pattern ≤ (0 : Int) + d269 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1853, d438, d269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c158 pattern childGuard
    simpa only [d1853, d438, d269, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1853, d438, d269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6777 pattern childGuard
    simpa only [d1853, d438, d269, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6779 (pattern : Twelve) (guard : d1854 pattern = 1) : d438 pattern ≤ (0 : Int) + d263 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1854, d438, d263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4424 pattern childGuard
    simpa only [d1854, d438, d263, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1854, d438, d263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6753 pattern childGuard
    simpa only [d1854, d438, d263, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6780 (pattern : Twelve) (guard : d1855 pattern = 1) : d438 pattern ≤ (0 : Int) + d279 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1853 pattern = 1 := by simpa only [d1855, d279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6778 pattern childGuard
    simpa only [d1855, d279, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1854 pattern = 1 := by simpa only [d1855, d279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6779 pattern childGuard
    simpa only [d1855, d279, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6781 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d246 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6782 (pattern : Twelve) (guard : d1853 pattern = 1) : d439 pattern ≤ (0 : Int) + d246 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1853, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c167 pattern childGuard
    simpa only [d1853, d439, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1853, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6781 pattern childGuard
    simpa only [d1853, d439, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6783 (pattern : Twelve) (guard : d1849 pattern = 1) : d54 pattern ≤ (0 : Int) + d246 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d54, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1567 pattern childGuard
    simpa only [d1849, d54, d246, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d54, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c212 pattern childGuard
    simpa only [d1849, d54, d246, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6784 (pattern : Twelve) (guard : d1854 pattern = 1) : d440 pattern ≤ (0 : Int) + d263 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1854, d440, d263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6783 pattern childGuard
    simpa only [d1854, d440, d263, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1854, d440, d263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6753 pattern childGuard
    simpa only [d1854, d440, d263, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6785 (pattern : Twelve) (guard : d1855 pattern = 1) : d451 pattern ≤ (0 : Int) + d280 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1853 pattern = 1 := by simpa only [d1855, d451, d280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6782 pattern childGuard
    simpa only [d1855, d451, d280, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1854 pattern = 1 := by simpa only [d1855, d451, d280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6784 pattern childGuard
    simpa only [d1855, d451, d280, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6786 (pattern : Twelve) (guard : d1855 pattern = 1) : d459 pattern ≤ (0 : Int) + d288 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d459, d288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6780 pattern childGuard
    simpa only [d459, d288, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d459, d288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6785 pattern childGuard
    simpa only [d459, d288, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6787 (pattern : Twelve) (guard : d1853 pattern = 1) : d432 pattern ≤ (0 : Int) + d246 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1853, d432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c121 pattern childGuard
    simpa only [d1853, d432, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1853, d432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6781 pattern childGuard
    simpa only [d1853, d432, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6788 (pattern : Twelve) (guard : d1855 pattern = 1) : d432 pattern ≤ (0 : Int) + d280 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1853 pattern = 1 := by simpa only [d1855, d280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6787 pattern childGuard
    simpa only [d1855, d280, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1854 pattern = 1 := by simpa only [d1855, d280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6754 pattern childGuard
    simpa only [d1855, d280, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6789 (pattern : Twelve) (guard : d1855 pattern = 1) : d460 pattern ≤ (0 : Int) + d288 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d460, d288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6780 pattern childGuard
    simpa only [d460, d288, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d460, d288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6788 pattern childGuard
    simpa only [d460, d288, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6790 (pattern : Twelve) (guard : d1855 pattern = 1) : d467 pattern ≤ (0 : Int) + d288 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6786 pattern childGuard
    simpa only [d467, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6789 pattern childGuard
    simpa only [d467, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6791 (pattern : Twelve) (guard : d1853 pattern = 1) : d441 pattern ≤ (0 : Int) + d246 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1853, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c163 pattern childGuard
    simpa only [d1853, d441, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1853, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6781 pattern childGuard
    simpa only [d1853, d441, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6792 (pattern : Twelve) (guard : d1854 pattern = 1) : d441 pattern ≤ (0 : Int) + d263 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1854, d441, d263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4433 pattern childGuard
    simpa only [d1854, d441, d263, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1854, d441, d263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6753 pattern childGuard
    simpa only [d1854, d441, d263, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6793 (pattern : Twelve) (guard : d1855 pattern = 1) : d441 pattern ≤ (0 : Int) + d280 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1853 pattern = 1 := by simpa only [d1855, d280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6791 pattern childGuard
    simpa only [d1855, d280, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1854 pattern = 1 := by simpa only [d1855, d280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6792 pattern childGuard
    simpa only [d1855, d280, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6794 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d250 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6795 (pattern : Twelve) (guard : d1853 pattern = 1) : d436 pattern ≤ (0 : Int) + d250 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1853, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c142 pattern childGuard
    simpa only [d1853, d436, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1853, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6794 pattern childGuard
    simpa only [d1853, d436, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6796 (pattern : Twelve) (guard : d1855 pattern = 1) : d436 pattern ≤ (0 : Int) + d281 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1853 pattern = 1 := by simpa only [d1855, d281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6795 pattern childGuard
    simpa only [d1855, d281, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1854 pattern = 1 := by simpa only [d1855, d281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6768 pattern childGuard
    simpa only [d1855, d281, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6797 (pattern : Twelve) (guard : d1855 pattern = 1) : d461 pattern ≤ (0 : Int) + d289 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d461, d289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6793 pattern childGuard
    simpa only [d461, d289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d461, d289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6796 pattern childGuard
    simpa only [d461, d289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6798 (pattern : Twelve) (guard : d1855 pattern = 1) : d462 pattern ≤ (0 : Int) + d290 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d462, d290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6788 pattern childGuard
    simpa only [d462, d290, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d462, d290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1603 pattern childGuard
    simpa only [d462, d290, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6799 (pattern : Twelve) (guard : d1855 pattern = 1) : d468 pattern ≤ (0 : Int) + d295 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d468, d295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6797 pattern childGuard
    simpa only [d468, d295, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d468, d295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6798 pattern childGuard
    simpa only [d468, d295, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6800 (pattern : Twelve) (guard : d1855 pattern = 1) : d472 pattern ≤ (0 : Int) + d298 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d472, d298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6790 pattern childGuard
    simpa only [d472, d298, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d472, d298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6799 pattern childGuard
    simpa only [d472, d298, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6801 (pattern : Twelve) (guard : d1855 pattern = 1) : d474 pattern ≤ (0 : Int) + d300 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d474, d300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6776 pattern childGuard
    simpa only [d474, d300, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d474, d300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6800 pattern childGuard
    simpa only [d474, d300, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6802 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d255 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6803 (pattern : Twelve) (guard : d1854 pattern = 1) : d438 pattern ≤ (0 : Int) + d270 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1854, d438, d270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4430 pattern childGuard
    simpa only [d1854, d438, d270, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1854, d438, d270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6802 pattern childGuard
    simpa only [d1854, d438, d270, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6804 (pattern : Twelve) (guard : d1855 pattern = 1) : d438 pattern ≤ (0 : Int) + d282 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1853 pattern = 1 := by simpa only [d1855, d282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6778 pattern childGuard
    simpa only [d1855, d282, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1854 pattern = 1 := by simpa only [d1855, d282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6803 pattern childGuard
    simpa only [d1855, d282, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6805 (pattern : Twelve) (guard : d1855 pattern = 1) : d459 pattern ≤ (0 : Int) + d291 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d459, d291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6804 pattern childGuard
    simpa only [d459, d291, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d459, d291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6785 pattern childGuard
    simpa only [d459, d291, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6806 (pattern : Twelve) (guard : d1854 pattern = 1) : d438 pattern ≤ (0 : Int) + d271 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1854, d438, d271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4430 pattern childGuard
    simpa only [d1854, d438, d271, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1854, d438, d271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6753 pattern childGuard
    simpa only [d1854, d438, d271, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6807 (pattern : Twelve) (guard : d1855 pattern = 1) : d438 pattern ≤ (0 : Int) + d283 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1853 pattern = 1 := by simpa only [d1855, d283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6778 pattern childGuard
    simpa only [d1855, d283, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1854 pattern = 1 := by simpa only [d1855, d283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6806 pattern childGuard
    simpa only [d1855, d283, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6808 (pattern : Twelve) (guard : d1855 pattern = 1) : d460 pattern ≤ (0 : Int) + d292 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d460, d292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6807 pattern childGuard
    simpa only [d460, d292, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d460, d292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6788 pattern childGuard
    simpa only [d460, d292, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6809 (pattern : Twelve) (guard : d1855 pattern = 1) : d467 pattern ≤ (0 : Int) + d296 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d467, d296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6805 pattern childGuard
    simpa only [d467, d296, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d467, d296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6808 pattern childGuard
    simpa only [d467, d296, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6810 (pattern : Twelve) (guard : d1855 pattern = 1) : d472 pattern ≤ (0 : Int) + d299 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d472, d299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6809 pattern childGuard
    simpa only [d472, d299, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d472, d299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6799 pattern childGuard
    simpa only [d472, d299, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6811 (pattern : Twelve) (guard : d1855 pattern = 1) : d472 pattern ≤ (0 : Int) + d301 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6810 pattern childGuard
    simpa only [d301, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6800 pattern childGuard
    simpa only [d301, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6812 (pattern : Twelve) (guard : d1855 pattern = 1) : d475 pattern ≤ (0 : Int) + d302 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d475, d302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6801 pattern childGuard
    simpa only [d475, d302, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d475, d302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6811 pattern childGuard
    simpa only [d475, d302, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6813 (pattern : Twelve) (guard : d1855 pattern = 1) : d452 pattern ≤ (0 : Int) + d280 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1853 pattern = 1 := by simpa only [d1855, d452, d280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6782 pattern childGuard
    simpa only [d1855, d452, d280, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1854 pattern = 1 := by simpa only [d1855, d452, d280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6754 pattern childGuard
    simpa only [d1855, d452, d280, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6814 (pattern : Twelve) (guard : d1855 pattern = 1) : d463 pattern ≤ (0 : Int) + d291 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d463, d291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6804 pattern childGuard
    simpa only [d463, d291, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d463, d291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6813 pattern childGuard
    simpa only [d463, d291, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6815 (pattern : Twelve) (guard : d1855 pattern = 1) : d469 pattern ≤ (0 : Int) + d296 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d469, d296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6814 pattern childGuard
    simpa only [d469, d296, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d469, d296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6808 pattern childGuard
    simpa only [d469, d296, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6816 (pattern : Twelve) (guard : d0 pattern = 1) : d123 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6817 (pattern : Twelve) (guard : d1849 pattern = 1) : d132 pattern ≤ (0 : Int) + d246 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d132, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1567 pattern childGuard
    simpa only [d1849, d132, d246, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d132, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6816 pattern childGuard
    simpa only [d1849, d132, d246, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6818 (pattern : Twelve) (guard : d1854 pattern = 1) : d442 pattern ≤ (0 : Int) + d263 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1854, d442, d263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6817 pattern childGuard
    simpa only [d1854, d442, d263, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1854, d442, d263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6753 pattern childGuard
    simpa only [d1854, d442, d263, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6819 (pattern : Twelve) (guard : d1855 pattern = 1) : d453 pattern ≤ (0 : Int) + d280 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1853 pattern = 1 := by simpa only [d1855, d453, d280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6791 pattern childGuard
    simpa only [d1855, d453, d280, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1854 pattern = 1 := by simpa only [d1855, d453, d280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6818 pattern childGuard
    simpa only [d1855, d453, d280, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6820 (pattern : Twelve) (guard : d0 pattern = 1) : d5 pattern ≤ (0 : Int) + d4 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6821 (pattern : Twelve) (guard : d1848 pattern = 1) : d126 pattern ≤ (0 : Int) + d38 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d126, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1333 pattern childGuard
    simpa only [d1848, d126, d38, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d126, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6820 pattern childGuard
    simpa only [d1848, d126, d38, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6822 (pattern : Twelve) (guard : d1849 pattern = 1) : d134 pattern ≤ (0 : Int) + d250 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d134, d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6821 pattern childGuard
    simpa only [d1849, d134, d250, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d134, d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c192 pattern childGuard
    simpa only [d1849, d134, d250, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6823 (pattern : Twelve) (guard : d1854 pattern = 1) : d443 pattern ≤ (0 : Int) + d267 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1854, d443, d267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6822 pattern childGuard
    simpa only [d1854, d443, d267, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1854, d443, d267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6767 pattern childGuard
    simpa only [d1854, d443, d267, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6824 (pattern : Twelve) (guard : d1855 pattern = 1) : d454 pattern ≤ (0 : Int) + d281 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1853 pattern = 1 := by simpa only [d1855, d454, d281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6795 pattern childGuard
    simpa only [d1855, d454, d281, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1854 pattern = 1 := by simpa only [d1855, d454, d281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6823 pattern childGuard
    simpa only [d1855, d454, d281, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6825 (pattern : Twelve) (guard : d1855 pattern = 1) : d464 pattern ≤ (0 : Int) + d289 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d464, d289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6819 pattern childGuard
    simpa only [d464, d289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d464, d289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6824 pattern childGuard
    simpa only [d464, d289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6826 (pattern : Twelve) (guard : d1855 pattern = 1) : d470 pattern ≤ (0 : Int) + d295 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d470, d295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6825 pattern childGuard
    simpa only [d470, d295, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d470, d295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6798 pattern childGuard
    simpa only [d470, d295, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6827 (pattern : Twelve) (guard : d1855 pattern = 1) : d473 pattern ≤ (0 : Int) + d299 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d473, d299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6815 pattern childGuard
    simpa only [d473, d299, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d473, d299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6826 pattern childGuard
    simpa only [d473, d299, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6828 (pattern : Twelve) (guard : d1855 pattern = 1) : d463 pattern ≤ (0 : Int) + d288 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d463, d288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6780 pattern childGuard
    simpa only [d463, d288, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d463, d288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6813 pattern childGuard
    simpa only [d463, d288, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6829 (pattern : Twelve) (guard : d1855 pattern = 1) : d469 pattern ≤ (0 : Int) + d288 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6828 pattern childGuard
    simpa only [d469, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6789 pattern childGuard
    simpa only [d469, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6830 (pattern : Twelve) (guard : d1855 pattern = 1) : d473 pattern ≤ (0 : Int) + d298 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d473, d298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6829 pattern childGuard
    simpa only [d473, d298, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d473, d298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6826 pattern childGuard
    simpa only [d473, d298, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6831 (pattern : Twelve) (guard : d1855 pattern = 1) : d473 pattern ≤ (0 : Int) + d301 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6827 pattern childGuard
    simpa only [d301, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6830 pattern childGuard
    simpa only [d301, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6832 (pattern : Twelve) (guard : d1855 pattern = 1) : d476 pattern ≤ (0 : Int) + d303 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d476, d303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6812 pattern childGuard
    simpa only [d476, d303, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d476, d303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6831 pattern childGuard
    simpa only [d476, d303, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6833 (pattern : Twelve) (guard : d0 pattern = 1) : d186 pattern ≤ (0 : Int) + d940 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6834 (pattern : Twelve) (guard : d1853 pattern = 1) : d426 pattern ≤ (0 : Int) + d947 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1853, d426, d947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c86 pattern childGuard
    simpa only [d1853, d426, d947, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1853, d426, d947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6833 pattern childGuard
    simpa only [d1853, d426, d947, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6835 (pattern : Twelve) (guard : d0 pattern = 1) : d908 pattern ≤ (0 : Int) + d942 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6836 (pattern : Twelve) (guard : d1854 pattern = 1) : d1070 pattern ≤ (0 : Int) + d948 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1854, d1070, d948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4466 pattern childGuard
    simpa only [d1854, d1070, d948, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1854, d1070, d948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6835 pattern childGuard
    simpa only [d1854, d1070, d948, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6837 (pattern : Twelve) (guard : d1855 pattern = 1) : d1078 pattern ≤ (0 : Int) + d955 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1853 pattern = 1 := by simpa only [d1855, d1078, d955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6834 pattern childGuard
    simpa only [d1855, d1078, d955, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1854 pattern = 1 := by simpa only [d1855, d1078, d955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6836 pattern childGuard
    simpa only [d1855, d1078, d955, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6838 (pattern : Twelve) (guard : d1853 pattern = 1) : d1071 pattern ≤ (0 : Int) + d259 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1853, d1071, d259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c248 pattern childGuard
    simpa only [d1853, d1071, d259, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1853, d1071, d259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6742 pattern childGuard
    simpa only [d1853, d1071, d259, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6839 (pattern : Twelve) (guard : d1849 pattern = 1) : d827 pattern ≤ (0 : Int) + d241 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d827, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1676 pattern childGuard
    simpa only [d1849, d827, d241, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d827, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c117 pattern childGuard
    simpa only [d1849, d827, d241, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6840 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d942 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6841 (pattern : Twelve) (guard : d1854 pattern = 1) : d1072 pattern ≤ (0 : Int) + d949 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1854, d1072, d949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6839 pattern childGuard
    simpa only [d1854, d1072, d949, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1854, d1072, d949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6840 pattern childGuard
    simpa only [d1854, d1072, d949, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6842 (pattern : Twelve) (guard : d1855 pattern = 1) : d1079 pattern ≤ (0 : Int) + d956 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1853 pattern = 1 := by simpa only [d1855, d1079, d956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6838 pattern childGuard
    simpa only [d1855, d1079, d956, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1854 pattern = 1 := by simpa only [d1855, d1079, d956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6841 pattern childGuard
    simpa only [d1855, d1079, d956, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6843 (pattern : Twelve) (guard : d1855 pattern = 1) : d1088 pattern ≤ (0 : Int) + d963 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1088, d963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6837 pattern childGuard
    simpa only [d1088, d963, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1088, d963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6842 pattern childGuard
    simpa only [d1088, d963, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6844 (pattern : Twelve) (guard : d0 pattern = 1) : d189 pattern ≤ (0 : Int) + d943 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6845 (pattern : Twelve) (guard : d1853 pattern = 1) : d430 pattern ≤ (0 : Int) + d950 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1853, d430, d950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c112 pattern childGuard
    simpa only [d1853, d430, d950, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1853, d430, d950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6844 pattern childGuard
    simpa only [d1853, d430, d950, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6846 (pattern : Twelve) (guard : d1854 pattern = 1) : d1073 pattern ≤ (0 : Int) + d951 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1854, d1073, d951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4474 pattern childGuard
    simpa only [d1854, d1073, d951, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1854, d1073, d951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6840 pattern childGuard
    simpa only [d1854, d1073, d951, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6847 (pattern : Twelve) (guard : d1855 pattern = 1) : d1080 pattern ≤ (0 : Int) + d957 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1853 pattern = 1 := by simpa only [d1855, d1080, d957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6845 pattern childGuard
    simpa only [d1855, d1080, d957, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1854 pattern = 1 := by simpa only [d1855, d1080, d957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6846 pattern childGuard
    simpa only [d1855, d1080, d957, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6848 (pattern : Twelve) (guard : d1853 pattern = 1) : d432 pattern ≤ (0 : Int) + d263 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1853, d432, d263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c121 pattern childGuard
    simpa only [d1853, d432, d263, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1853, d432, d263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6753 pattern childGuard
    simpa only [d1853, d432, d263, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6849 (pattern : Twelve) (guard : d1855 pattern = 1) : d1081 pattern ≤ (0 : Int) + d958 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1853 pattern = 1 := by simpa only [d1855, d1081, d958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6848 pattern childGuard
    simpa only [d1855, d1081, d958, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1854 pattern = 1 := by simpa only [d1855, d1081, d958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6841 pattern childGuard
    simpa only [d1855, d1081, d958, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6850 (pattern : Twelve) (guard : d1855 pattern = 1) : d1089 pattern ≤ (0 : Int) + d964 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1089, d964, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6847 pattern childGuard
    simpa only [d1089, d964, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1089, d964, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6849 pattern childGuard
    simpa only [d1089, d964, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6851 (pattern : Twelve) (guard : d1855 pattern = 1) : d1095 pattern ≤ (0 : Int) + d970 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1095, d970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6843 pattern childGuard
    simpa only [d1095, d970, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1095, d970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6850 pattern childGuard
    simpa only [d1095, d970, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6852 (pattern : Twelve) (guard : d1853 pattern = 1) : d434 pattern ≤ (0 : Int) + d265 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1853, d434, d265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c132 pattern childGuard
    simpa only [d1853, d434, d265, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1853, d434, d265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6761 pattern childGuard
    simpa only [d1853, d434, d265, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6853 (pattern : Twelve) (guard : d1849 pattern = 1) : d34 pattern ≤ (0 : Int) + d241 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1676 pattern childGuard
    simpa only [d1849, d241, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c270 pattern childGuard
    simpa only [d1849, d241, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6854 (pattern : Twelve) (guard : d1854 pattern = 1) : d1074 pattern ≤ (0 : Int) + d949 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1854, d1074, d949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6853 pattern childGuard
    simpa only [d1854, d1074, d949, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1854, d1074, d949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6840 pattern childGuard
    simpa only [d1854, d1074, d949, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6855 (pattern : Twelve) (guard : d1855 pattern = 1) : d1082 pattern ≤ (0 : Int) + d959 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1853 pattern = 1 := by simpa only [d1855, d1082, d959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6852 pattern childGuard
    simpa only [d1855, d1082, d959, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1854 pattern = 1 := by simpa only [d1855, d1082, d959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6854 pattern childGuard
    simpa only [d1855, d1082, d959, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6856 (pattern : Twelve) (guard : d1853 pattern = 1) : d436 pattern ≤ (0 : Int) + d267 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1853, d436, d267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c142 pattern childGuard
    simpa only [d1853, d436, d267, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1853, d436, d267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6767 pattern childGuard
    simpa only [d1853, d436, d267, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6857 (pattern : Twelve) (guard : d1849 pattern = 1) : d830 pattern ≤ (0 : Int) + d251 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d830, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1696 pattern childGuard
    simpa only [d1849, d830, d251, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d830, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c138 pattern childGuard
    simpa only [d1849, d830, d251, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6858 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d945 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6859 (pattern : Twelve) (guard : d1854 pattern = 1) : d1075 pattern ≤ (0 : Int) + d952 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1854, d1075, d952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6857 pattern childGuard
    simpa only [d1854, d1075, d952, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1854, d1075, d952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6858 pattern childGuard
    simpa only [d1854, d1075, d952, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
