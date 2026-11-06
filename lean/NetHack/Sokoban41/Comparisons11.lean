/- Staged soko4-1 certificate. No result until all kernel checks pass. -/
import NetHack.Sokoban41.Comparisons10
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban41.Diagram
theorem c1760 (pattern : Ten) (guard : d171 pattern = 1) : d190 pattern ≤ (1 : Int) + d410 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d171 pattern = 1 := by simpa only [d190, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1755 pattern childGuard
    simpa only [d190, d410, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d171 pattern = 1 := by simpa only [d190, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1759 pattern childGuard
    simpa only [d190, d410, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1761 (pattern : Ten) (guard : d171 pattern = 1) : d191 pattern ≤ (1 : Int) + d233 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d171 pattern = 1 := by simpa only [d191, d233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1759 pattern childGuard
    simpa only [d191, d233, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d171 pattern = 1 := by simpa only [d191, d233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1739 pattern childGuard
    simpa only [d191, d233, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1762 (pattern : Ten) (guard : d171 pattern = 1) : d192 pattern ≤ (1 : Int) + d411 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d171 pattern = 1 := by simpa only [d192, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1760 pattern childGuard
    simpa only [d192, d411, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d171 pattern = 1 := by simpa only [d192, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1761 pattern childGuard
    simpa only [d192, d411, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1763 (pattern : Ten) (guard : d356 pattern = 1) : d10 pattern ≤ (1 : Int) + d9 pattern := by
  change (10 : Int) ≤ (1 : Int) + 9
  decide
theorem c1764 (pattern : Ten) (guard : d406 pattern = 1) : d11 pattern ≤ (1 : Int) + d9 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d406, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1712 pattern childGuard
    simpa only [d406, d11, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d356 pattern = 1 := by simpa only [d406, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1763 pattern childGuard
    simpa only [d406, d11, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1765 (pattern : Ten) (guard : d407 pattern = 1) : d11 pattern ≤ (1 : Int) + d9 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d406 pattern = 1 := by simpa only [d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1764 pattern childGuard
    simpa only [d407, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1715 pattern childGuard
    simpa only [d407, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1766 (pattern : Ten) (guard : d407 pattern = 1) : d13 pattern ≤ (1 : Int) + d67 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d407 pattern = 1 := by simpa only [d13, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1654 pattern childGuard
    simpa only [d13, d67, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d407 pattern = 1 := by simpa only [d13, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1765 pattern childGuard
    simpa only [d13, d67, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1767 (pattern : Ten) (guard : d407 pattern = 1) : d14 pattern ≤ (1 : Int) + d68 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d407 pattern = 1 := by simpa only [d14, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1765 pattern childGuard
    simpa only [d14, d68, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d407 pattern = 1 := by simpa only [d14, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1661 pattern childGuard
    simpa only [d14, d68, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1768 (pattern : Ten) (guard : d407 pattern = 1) : d19 pattern ≤ (1 : Int) + d69 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d407 pattern = 1 := by simpa only [d19, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1766 pattern childGuard
    simpa only [d19, d69, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d407 pattern = 1 := by simpa only [d19, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1767 pattern childGuard
    simpa only [d19, d69, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1769 (pattern : Ten) (guard : d407 pattern = 1) : d20 pattern ≤ (1 : Int) + d70 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d407 pattern = 1 := by simpa only [d20, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1767 pattern childGuard
    simpa only [d20, d70, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d407 pattern = 1 := by simpa only [d20, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1661 pattern childGuard
    simpa only [d20, d70, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1770 (pattern : Ten) (guard : d407 pattern = 1) : d24 pattern ≤ (1 : Int) + d71 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d407 pattern = 1 := by simpa only [d24, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1768 pattern childGuard
    simpa only [d24, d71, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d407 pattern = 1 := by simpa only [d24, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1769 pattern childGuard
    simpa only [d24, d71, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1771 (pattern : Ten) (guard : d407 pattern = 1) : d29 pattern ≤ (1 : Int) + d73 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d407 pattern = 1 := by simpa only [d29, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1653 pattern childGuard
    simpa only [d29, d73, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d407 pattern = 1 := by simpa only [d29, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1770 pattern childGuard
    simpa only [d29, d73, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1772 (pattern : Ten) (guard : d407 pattern = 1) : d30 pattern ≤ (1 : Int) + d74 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d407 pattern = 1 := by simpa only [d30, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1667 pattern childGuard
    simpa only [d30, d74, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d407 pattern = 1 := by simpa only [d30, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1770 pattern childGuard
    simpa only [d30, d74, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1773 (pattern : Ten) (guard : d407 pattern = 1) : d33 pattern ≤ (1 : Int) + d77 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d407 pattern = 1 := by simpa only [d33, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1771 pattern childGuard
    simpa only [d33, d77, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d407 pattern = 1 := by simpa only [d33, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1772 pattern childGuard
    simpa only [d33, d77, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1774 (pattern : Ten) (guard : d407 pattern = 1) : d27 pattern ≤ (1 : Int) + d72 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d407 pattern = 1 := by simpa only [d27, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1769 pattern childGuard
    simpa only [d27, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d407 pattern = 1 := by simpa only [d27, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1661 pattern childGuard
    simpa only [d27, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1775 (pattern : Ten) (guard : d407 pattern = 1) : d31 pattern ≤ (1 : Int) + d75 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d407 pattern = 1 := by simpa only [d31, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1670 pattern childGuard
    simpa only [d31, d75, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d407 pattern = 1 := by simpa only [d31, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1774 pattern childGuard
    simpa only [d31, d75, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1776 (pattern : Ten) (guard : d407 pattern = 1) : d32 pattern ≤ (1 : Int) + d76 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d407 pattern = 1 := by simpa only [d32, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1673 pattern childGuard
    simpa only [d32, d76, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d407 pattern = 1 := by simpa only [d32, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1774 pattern childGuard
    simpa only [d32, d76, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1777 (pattern : Ten) (guard : d407 pattern = 1) : d34 pattern ≤ (1 : Int) + d78 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d407 pattern = 1 := by simpa only [d34, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1775 pattern childGuard
    simpa only [d34, d78, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d407 pattern = 1 := by simpa only [d34, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1776 pattern childGuard
    simpa only [d34, d78, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1778 (pattern : Ten) (guard : d407 pattern = 1) : d35 pattern ≤ (1 : Int) + d79 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d407 pattern = 1 := by simpa only [d35, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1773 pattern childGuard
    simpa only [d35, d79, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d407 pattern = 1 := by simpa only [d35, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1777 pattern childGuard
    simpa only [d35, d79, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1779 (pattern : Ten) (guard : d407 pattern = 1) : d36 pattern ≤ (1 : Int) + d80 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d407 pattern = 1 := by simpa only [d36, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1777 pattern childGuard
    simpa only [d36, d80, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d407 pattern = 1 := by simpa only [d36, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1661 pattern childGuard
    simpa only [d36, d80, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1780 (pattern : Ten) (guard : d407 pattern = 1) : d37 pattern ≤ (1 : Int) + d81 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d407 pattern = 1 := by simpa only [d37, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1778 pattern childGuard
    simpa only [d37, d81, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d407 pattern = 1 := by simpa only [d37, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1779 pattern childGuard
    simpa only [d37, d81, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1781 (pattern : Ten) (guard : d356 pattern = 1) : d1 pattern ≤ (1 : Int) + d0 pattern := by
  change (1 : Int) ≤ (1 : Int) + 0
  decide
theorem c1782 (pattern : Ten) (guard : d406 pattern = 1) : d171 pattern ≤ (1 : Int) + d0 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d406, d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1736 pattern childGuard
    simpa only [d406, d171, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d356 pattern = 1 := by simpa only [d406, d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1781 pattern childGuard
    simpa only [d406, d171, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1783 (pattern : Ten) (guard : d406 pattern = 1) : d173 pattern ≤ (1 : Int) + d12 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d406 pattern = 1 := by simpa only [d173, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1782 pattern childGuard
    simpa only [d173, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d406 pattern = 1 := by simpa only [d173, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1686 pattern childGuard
    simpa only [d173, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1784 (pattern : Ten) (guard : d406 pattern = 1) : d176 pattern ≤ (1 : Int) + d17 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d406 pattern = 1 := by simpa only [d176, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1782 pattern childGuard
    simpa only [d176, d17, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d406 pattern = 1 := by simpa only [d176, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1783 pattern childGuard
    simpa only [d176, d17, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1785 (pattern : Ten) (guard : d406 pattern = 1) : d177 pattern ≤ (1 : Int) + d18 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d406 pattern = 1 := by simpa only [d177, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1783 pattern childGuard
    simpa only [d177, d18, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d406 pattern = 1 := by simpa only [d177, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1686 pattern childGuard
    simpa only [d177, d18, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1786 (pattern : Ten) (guard : d406 pattern = 1) : d180 pattern ≤ (1 : Int) + d23 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d406 pattern = 1 := by simpa only [d180, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1784 pattern childGuard
    simpa only [d180, d23, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d406 pattern = 1 := by simpa only [d180, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1785 pattern childGuard
    simpa only [d180, d23, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1787 (pattern : Ten) (guard : d406 pattern = 1) : d181 pattern ≤ (1 : Int) + d26 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d406 pattern = 1 := by simpa only [d181, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1785 pattern childGuard
    simpa only [d181, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d406 pattern = 1 := by simpa only [d181, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1686 pattern childGuard
    simpa only [d181, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1788 (pattern : Ten) (guard : d406 pattern = 1) : d184 pattern ≤ (1 : Int) + d408 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d406 pattern = 1 := by simpa only [d184, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1786 pattern childGuard
    simpa only [d184, d408, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d406 pattern = 1 := by simpa only [d184, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1787 pattern childGuard
    simpa only [d184, d408, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1789 (pattern : Ten) (guard : d356 pattern = 1) : d3 pattern ≤ (1 : Int) + d2 pattern := by
  change (3 : Int) ≤ (1 : Int) + 2
  decide
theorem c1790 (pattern : Ten) (guard : d406 pattern = 1) : d172 pattern ≤ (1 : Int) + d2 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d406, d172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1746 pattern childGuard
    simpa only [d406, d172, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d356 pattern = 1 := by simpa only [d406, d172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1789 pattern childGuard
    simpa only [d406, d172, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1791 (pattern : Ten) (guard : d406 pattern = 1) : d174 pattern ≤ (1 : Int) + d15 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d406 pattern = 1 := by simpa only [d174, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1782 pattern childGuard
    simpa only [d174, d15, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d406 pattern = 1 := by simpa only [d174, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1790 pattern childGuard
    simpa only [d174, d15, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1792 (pattern : Ten) (guard : d406 pattern = 1) : d175 pattern ≤ (1 : Int) + d16 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d406 pattern = 1 := by simpa only [d175, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1790 pattern childGuard
    simpa only [d175, d16, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d406 pattern = 1 := by simpa only [d175, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1686 pattern childGuard
    simpa only [d175, d16, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1793 (pattern : Ten) (guard : d406 pattern = 1) : d178 pattern ≤ (1 : Int) + d21 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d406 pattern = 1 := by simpa only [d178, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1791 pattern childGuard
    simpa only [d178, d21, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d406 pattern = 1 := by simpa only [d178, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1792 pattern childGuard
    simpa only [d178, d21, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1794 (pattern : Ten) (guard : d406 pattern = 1) : d179 pattern ≤ (1 : Int) + d22 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d406 pattern = 1 := by simpa only [d179, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1792 pattern childGuard
    simpa only [d179, d22, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d406 pattern = 1 := by simpa only [d179, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1686 pattern childGuard
    simpa only [d179, d22, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1795 (pattern : Ten) (guard : d406 pattern = 1) : d182 pattern ≤ (1 : Int) + d25 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d406 pattern = 1 := by simpa only [d182, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1793 pattern childGuard
    simpa only [d182, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d406 pattern = 1 := by simpa only [d182, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1794 pattern childGuard
    simpa only [d182, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1796 (pattern : Ten) (guard : d406 pattern = 1) : d185 pattern ≤ (1 : Int) + d227 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d406 pattern = 1 := by simpa only [d185, d227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1795 pattern childGuard
    simpa only [d185, d227, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d406 pattern = 1 := by simpa only [d185, d227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1787 pattern childGuard
    simpa only [d185, d227, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1797 (pattern : Ten) (guard : d406 pattern = 1) : d188 pattern ≤ (1 : Int) + d409 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d406 pattern = 1 := by simpa only [d188, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1788 pattern childGuard
    simpa only [d188, d409, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d406 pattern = 1 := by simpa only [d188, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1796 pattern childGuard
    simpa only [d188, d409, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1798 (pattern : Ten) (guard : d406 pattern = 1) : d186 pattern ≤ (1 : Int) + d228 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d406 pattern = 1 := by simpa only [d186, d228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1787 pattern childGuard
    simpa only [d186, d228, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d406 pattern = 1 := by simpa only [d186, d228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1686 pattern childGuard
    simpa only [d186, d228, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1799 (pattern : Ten) (guard : d406 pattern = 1) : d183 pattern ≤ (1 : Int) + d28 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d406 pattern = 1 := by simpa only [d183, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1794 pattern childGuard
    simpa only [d183, d28, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d406 pattern = 1 := by simpa only [d183, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1686 pattern childGuard
    simpa only [d183, d28, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1800 (pattern : Ten) (guard : d406 pattern = 1) : d187 pattern ≤ (1 : Int) + d229 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d406 pattern = 1 := by simpa only [d187, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1799 pattern childGuard
    simpa only [d187, d229, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d406 pattern = 1 := by simpa only [d187, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1686 pattern childGuard
    simpa only [d187, d229, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1801 (pattern : Ten) (guard : d406 pattern = 1) : d189 pattern ≤ (1 : Int) + d231 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d406 pattern = 1 := by simpa only [d189, d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1798 pattern childGuard
    simpa only [d189, d231, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d406 pattern = 1 := by simpa only [d189, d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1800 pattern childGuard
    simpa only [d189, d231, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1802 (pattern : Ten) (guard : d406 pattern = 1) : d190 pattern ≤ (1 : Int) + d410 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d406 pattern = 1 := by simpa only [d190, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1797 pattern childGuard
    simpa only [d190, d410, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d406 pattern = 1 := by simpa only [d190, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1801 pattern childGuard
    simpa only [d190, d410, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1803 (pattern : Ten) (guard : d406 pattern = 1) : d191 pattern ≤ (1 : Int) + d233 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d406 pattern = 1 := by simpa only [d191, d233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1801 pattern childGuard
    simpa only [d191, d233, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d406 pattern = 1 := by simpa only [d191, d233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1686 pattern childGuard
    simpa only [d191, d233, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1804 (pattern : Ten) (guard : d406 pattern = 1) : d192 pattern ≤ (1 : Int) + d411 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d406 pattern = 1 := by simpa only [d192, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1802 pattern childGuard
    simpa only [d192, d411, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d406 pattern = 1 := by simpa only [d192, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1803 pattern childGuard
    simpa only [d192, d411, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1805 (pattern : Ten) (guard : d1 pattern = 1) : d10 pattern ≤ (1 : Int) + d10 pattern := by
  omega
theorem c1806 (pattern : Ten) (guard : d171 pattern = 1) : d11 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d171, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1655 pattern childGuard
    simpa only [d171, d11, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d171, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1805 pattern childGuard
    simpa only [d171, d11, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1807 (pattern : Ten) (guard : d292 pattern = 1) : d11 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d171 pattern = 1 := by simpa only [d292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1806 pattern childGuard
    simpa only [d292, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1658 pattern childGuard
    simpa only [d292, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1808 (pattern : Ten) (guard : d292 pattern = 1) : d13 pattern ≤ (1 : Int) + d12 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d292 pattern = 1 := by simpa only [d13, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1711 pattern childGuard
    simpa only [d13, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d292 pattern = 1 := by simpa only [d13, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1807 pattern childGuard
    simpa only [d13, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1809 (pattern : Ten) (guard : d292 pattern = 1) : d14 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d292 pattern = 1 := by simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1807 pattern childGuard
    simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d292 pattern = 1 := by simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1718 pattern childGuard
    simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1810 (pattern : Ten) (guard : d292 pattern = 1) : d19 pattern ≤ (1 : Int) + d18 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d292 pattern = 1 := by simpa only [d19, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1808 pattern childGuard
    simpa only [d19, d18, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d292 pattern = 1 := by simpa only [d19, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1809 pattern childGuard
    simpa only [d19, d18, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1811 (pattern : Ten) (guard : d292 pattern = 1) : d20 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d292 pattern = 1 := by simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1809 pattern childGuard
    simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d292 pattern = 1 := by simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1718 pattern childGuard
    simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1812 (pattern : Ten) (guard : d292 pattern = 1) : d24 pattern ≤ (1 : Int) + d26 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d292 pattern = 1 := by simpa only [d24, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1810 pattern childGuard
    simpa only [d24, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d292 pattern = 1 := by simpa only [d24, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1811 pattern childGuard
    simpa only [d24, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1813 (pattern : Ten) (guard : d292 pattern = 1) : d29 pattern ≤ (1 : Int) + d408 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d292 pattern = 1 := by simpa only [d29, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1710 pattern childGuard
    simpa only [d29, d408, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d292 pattern = 1 := by simpa only [d29, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1812 pattern childGuard
    simpa only [d29, d408, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1814 (pattern : Ten) (guard : d292 pattern = 1) : d30 pattern ≤ (1 : Int) + d227 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d292 pattern = 1 := by simpa only [d30, d227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1724 pattern childGuard
    simpa only [d30, d227, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d292 pattern = 1 := by simpa only [d30, d227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1812 pattern childGuard
    simpa only [d30, d227, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1815 (pattern : Ten) (guard : d292 pattern = 1) : d33 pattern ≤ (1 : Int) + d409 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d292 pattern = 1 := by simpa only [d33, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1813 pattern childGuard
    simpa only [d33, d409, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d292 pattern = 1 := by simpa only [d33, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1814 pattern childGuard
    simpa only [d33, d409, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1816 (pattern : Ten) (guard : d292 pattern = 1) : d27 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d292 pattern = 1 := by simpa only [d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1811 pattern childGuard
    simpa only [d27, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d292 pattern = 1 := by simpa only [d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1718 pattern childGuard
    simpa only [d27, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1817 (pattern : Ten) (guard : d292 pattern = 1) : d31 pattern ≤ (1 : Int) + d228 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d292 pattern = 1 := by simpa only [d31, d228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1727 pattern childGuard
    simpa only [d31, d228, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d292 pattern = 1 := by simpa only [d31, d228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1816 pattern childGuard
    simpa only [d31, d228, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1818 (pattern : Ten) (guard : d292 pattern = 1) : d32 pattern ≤ (1 : Int) + d229 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d292 pattern = 1 := by simpa only [d32, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1730 pattern childGuard
    simpa only [d32, d229, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d292 pattern = 1 := by simpa only [d32, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1816 pattern childGuard
    simpa only [d32, d229, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1819 (pattern : Ten) (guard : d292 pattern = 1) : d34 pattern ≤ (1 : Int) + d231 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d292 pattern = 1 := by simpa only [d34, d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1817 pattern childGuard
    simpa only [d34, d231, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d292 pattern = 1 := by simpa only [d34, d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1818 pattern childGuard
    simpa only [d34, d231, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1820 (pattern : Ten) (guard : d292 pattern = 1) : d35 pattern ≤ (1 : Int) + d410 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d292 pattern = 1 := by simpa only [d35, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1815 pattern childGuard
    simpa only [d35, d410, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d292 pattern = 1 := by simpa only [d35, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1819 pattern childGuard
    simpa only [d35, d410, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1821 (pattern : Ten) (guard : d292 pattern = 1) : d36 pattern ≤ (1 : Int) + d233 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d292 pattern = 1 := by simpa only [d36, d233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1819 pattern childGuard
    simpa only [d36, d233, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d292 pattern = 1 := by simpa only [d36, d233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1718 pattern childGuard
    simpa only [d36, d233, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1822 (pattern : Ten) (guard : d292 pattern = 1) : d37 pattern ≤ (1 : Int) + d411 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d292 pattern = 1 := by simpa only [d37, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1820 pattern childGuard
    simpa only [d37, d411, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d292 pattern = 1 := by simpa only [d37, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1821 pattern childGuard
    simpa only [d37, d411, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1823 (pattern : Ten) (guard : d1 pattern = 1) : d1 pattern ≤ (1 : Int) + d10 pattern := by
  change (1 : Int) ≤ (1 : Int) + 10
  decide
theorem c1824 (pattern : Ten) (guard : d171 pattern = 1) : d171 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1682 pattern childGuard
    simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1823 pattern childGuard
    simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1825 (pattern : Ten) (guard : d171 pattern = 1) : d173 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d171 pattern = 1 := by simpa only [d173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1824 pattern childGuard
    simpa only [d173, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d171 pattern = 1 := by simpa only [d173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1739 pattern childGuard
    simpa only [d173, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1826 (pattern : Ten) (guard : d171 pattern = 1) : d176 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d171 pattern = 1 := by simpa only [d176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1824 pattern childGuard
    simpa only [d176, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d171 pattern = 1 := by simpa only [d176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1825 pattern childGuard
    simpa only [d176, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1827 (pattern : Ten) (guard : d171 pattern = 1) : d177 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d171 pattern = 1 := by simpa only [d177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1825 pattern childGuard
    simpa only [d177, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d171 pattern = 1 := by simpa only [d177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1739 pattern childGuard
    simpa only [d177, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1828 (pattern : Ten) (guard : d171 pattern = 1) : d180 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d171 pattern = 1 := by simpa only [d180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1826 pattern childGuard
    simpa only [d180, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d171 pattern = 1 := by simpa only [d180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1827 pattern childGuard
    simpa only [d180, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1829 (pattern : Ten) (guard : d171 pattern = 1) : d181 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d171 pattern = 1 := by simpa only [d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1827 pattern childGuard
    simpa only [d181, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d171 pattern = 1 := by simpa only [d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1739 pattern childGuard
    simpa only [d181, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1830 (pattern : Ten) (guard : d171 pattern = 1) : d184 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d171 pattern = 1 := by simpa only [d184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1828 pattern childGuard
    simpa only [d184, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d171 pattern = 1 := by simpa only [d184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1829 pattern childGuard
    simpa only [d184, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1831 (pattern : Ten) (guard : d1 pattern = 1) : d3 pattern ≤ (1 : Int) + d10 pattern := by
  change (3 : Int) ≤ (1 : Int) + 10
  decide
theorem c1832 (pattern : Ten) (guard : d171 pattern = 1) : d172 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d171, d172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1693 pattern childGuard
    simpa only [d171, d172, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d171, d172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1831 pattern childGuard
    simpa only [d171, d172, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1833 (pattern : Ten) (guard : d171 pattern = 1) : d174 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d171 pattern = 1 := by simpa only [d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1824 pattern childGuard
    simpa only [d174, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d171 pattern = 1 := by simpa only [d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1832 pattern childGuard
    simpa only [d174, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1834 (pattern : Ten) (guard : d171 pattern = 1) : d175 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d171 pattern = 1 := by simpa only [d175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1832 pattern childGuard
    simpa only [d175, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d171 pattern = 1 := by simpa only [d175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1739 pattern childGuard
    simpa only [d175, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1835 (pattern : Ten) (guard : d171 pattern = 1) : d178 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d171 pattern = 1 := by simpa only [d178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1833 pattern childGuard
    simpa only [d178, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d171 pattern = 1 := by simpa only [d178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1834 pattern childGuard
    simpa only [d178, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1836 (pattern : Ten) (guard : d171 pattern = 1) : d179 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d171 pattern = 1 := by simpa only [d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1834 pattern childGuard
    simpa only [d179, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d171 pattern = 1 := by simpa only [d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1739 pattern childGuard
    simpa only [d179, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1837 (pattern : Ten) (guard : d171 pattern = 1) : d182 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d171 pattern = 1 := by simpa only [d182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1835 pattern childGuard
    simpa only [d182, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d171 pattern = 1 := by simpa only [d182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1836 pattern childGuard
    simpa only [d182, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1838 (pattern : Ten) (guard : d171 pattern = 1) : d185 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d171 pattern = 1 := by simpa only [d185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1837 pattern childGuard
    simpa only [d185, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d171 pattern = 1 := by simpa only [d185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1829 pattern childGuard
    simpa only [d185, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1839 (pattern : Ten) (guard : d171 pattern = 1) : d188 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d171 pattern = 1 := by simpa only [d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1830 pattern childGuard
    simpa only [d188, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d171 pattern = 1 := by simpa only [d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1838 pattern childGuard
    simpa only [d188, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1840 (pattern : Ten) (guard : d171 pattern = 1) : d186 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d171 pattern = 1 := by simpa only [d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1829 pattern childGuard
    simpa only [d186, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d171 pattern = 1 := by simpa only [d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1739 pattern childGuard
    simpa only [d186, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1841 (pattern : Ten) (guard : d171 pattern = 1) : d183 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d171 pattern = 1 := by simpa only [d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1836 pattern childGuard
    simpa only [d183, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d171 pattern = 1 := by simpa only [d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1739 pattern childGuard
    simpa only [d183, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1842 (pattern : Ten) (guard : d171 pattern = 1) : d187 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d171 pattern = 1 := by simpa only [d187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1841 pattern childGuard
    simpa only [d187, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d171 pattern = 1 := by simpa only [d187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1739 pattern childGuard
    simpa only [d187, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1843 (pattern : Ten) (guard : d171 pattern = 1) : d189 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d171 pattern = 1 := by simpa only [d189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1840 pattern childGuard
    simpa only [d189, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d171 pattern = 1 := by simpa only [d189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1842 pattern childGuard
    simpa only [d189, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1844 (pattern : Ten) (guard : d171 pattern = 1) : d190 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d171 pattern = 1 := by simpa only [d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1839 pattern childGuard
    simpa only [d190, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d171 pattern = 1 := by simpa only [d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1843 pattern childGuard
    simpa only [d190, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1845 (pattern : Ten) (guard : d171 pattern = 1) : d191 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d171 pattern = 1 := by simpa only [d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1843 pattern childGuard
    simpa only [d191, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d171 pattern = 1 := by simpa only [d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1739 pattern childGuard
    simpa only [d191, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1846 (pattern : Ten) (guard : d171 pattern = 1) : d192 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d171 pattern = 1 := by simpa only [d192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1844 pattern childGuard
    simpa only [d192, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d171 pattern = 1 := by simpa only [d192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1845 pattern childGuard
    simpa only [d192, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1847 (pattern : Ten) (guard : d1 pattern = 1) : d0 pattern ≤ (1 : Int) + d0 pattern := by
  omega
theorem c1848 (pattern : Ten) (guard : d1 pattern = 1) : d0 pattern ≤ (1 : Int) + d1 pattern := by
  change (0 : Int) ≤ (1 : Int) + 1
  decide
theorem c1849 (pattern : Ten) (guard : d1 pattern = 1) : d0 pattern ≤ (1 : Int) + d171 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1847 pattern childGuard
    simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1848 pattern childGuard
    simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1850 (pattern : Ten) (guard : d0 pattern = 1) : d0 pattern ≤ (1 : Int) + d171 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1851 (pattern : Ten) (guard : d350 pattern = 1) : d0 pattern ≤ (1 : Int) + d171 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1849 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1850 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1852 (pattern : Ten) (guard : d350 pattern = 1) : d10 pattern ≤ (1 : Int) + d10 pattern := by
  omega
theorem c1853 (pattern : Ten) (guard : d350 pattern = 1) : d12 pattern ≤ (1 : Int) + d173 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d12, d173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1851 pattern childGuard
    simpa only [d12, d173, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d12, d173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1852 pattern childGuard
    simpa only [d12, d173, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1854 (pattern : Ten) (guard : d350 pattern = 1) : d17 pattern ≤ (1 : Int) + d176 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d17, d176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1851 pattern childGuard
    simpa only [d17, d176, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d17, d176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1853 pattern childGuard
    simpa only [d17, d176, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1855 (pattern : Ten) (guard : d350 pattern = 1) : d18 pattern ≤ (1 : Int) + d177 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d18, d177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1853 pattern childGuard
    simpa only [d18, d177, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d18, d177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1852 pattern childGuard
    simpa only [d18, d177, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1856 (pattern : Ten) (guard : d350 pattern = 1) : d23 pattern ≤ (1 : Int) + d180 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d23, d180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1854 pattern childGuard
    simpa only [d23, d180, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d23, d180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1855 pattern childGuard
    simpa only [d23, d180, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1857 (pattern : Ten) (guard : d1 pattern = 1) : d9 pattern ≤ (1 : Int) + d10 pattern := by
  change (9 : Int) ≤ (1 : Int) + 10
  decide
theorem c1858 (pattern : Ten) (guard : d1 pattern = 1) : d11 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1857 pattern childGuard
    simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1805 pattern childGuard
    simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1859 (pattern : Ten) (guard : d350 pattern = 1) : d11 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1858 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1658 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1860 (pattern : Ten) (guard : d350 pattern = 1) : d13 pattern ≤ (1 : Int) + d173 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d13, d173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1851 pattern childGuard
    simpa only [d13, d173, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d13, d173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1859 pattern childGuard
    simpa only [d13, d173, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1861 (pattern : Ten) (guard : d350 pattern = 1) : d14 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1859 pattern childGuard
    simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1852 pattern childGuard
    simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1862 (pattern : Ten) (guard : d350 pattern = 1) : d19 pattern ≤ (1 : Int) + d177 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d19, d177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1860 pattern childGuard
    simpa only [d19, d177, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d19, d177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1861 pattern childGuard
    simpa only [d19, d177, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1863 (pattern : Ten) (guard : d350 pattern = 1) : d20 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1861 pattern childGuard
    simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1852 pattern childGuard
    simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1864 (pattern : Ten) (guard : d350 pattern = 1) : d24 pattern ≤ (1 : Int) + d181 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d24, d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1862 pattern childGuard
    simpa only [d24, d181, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d24, d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1863 pattern childGuard
    simpa only [d24, d181, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1865 (pattern : Ten) (guard : d350 pattern = 1) : d29 pattern ≤ (1 : Int) + d184 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d29, d184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1856 pattern childGuard
    simpa only [d29, d184, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d29, d184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1864 pattern childGuard
    simpa only [d29, d184, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1866 (pattern : Ten) (guard : d1 pattern = 1) : d2 pattern ≤ (1 : Int) + d2 pattern := by
  omega
theorem c1867 (pattern : Ten) (guard : d1 pattern = 1) : d2 pattern ≤ (1 : Int) + d3 pattern := by
  change (2 : Int) ≤ (1 : Int) + 3
  decide
theorem c1868 (pattern : Ten) (guard : d1 pattern = 1) : d2 pattern ≤ (1 : Int) + d172 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1866 pattern childGuard
    simpa only [d172, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1867 pattern childGuard
    simpa only [d172, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1869 (pattern : Ten) (guard : d0 pattern = 1) : d2 pattern ≤ (1 : Int) + d172 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1870 (pattern : Ten) (guard : d350 pattern = 1) : d2 pattern ≤ (1 : Int) + d172 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1868 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1869 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1871 (pattern : Ten) (guard : d350 pattern = 1) : d15 pattern ≤ (1 : Int) + d174 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d15, d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1851 pattern childGuard
    simpa only [d15, d174, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d15, d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1870 pattern childGuard
    simpa only [d15, d174, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1872 (pattern : Ten) (guard : d350 pattern = 1) : d16 pattern ≤ (1 : Int) + d175 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d16, d175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1870 pattern childGuard
    simpa only [d16, d175, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d16, d175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1852 pattern childGuard
    simpa only [d16, d175, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1873 (pattern : Ten) (guard : d350 pattern = 1) : d21 pattern ≤ (1 : Int) + d178 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d21, d178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1871 pattern childGuard
    simpa only [d21, d178, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d21, d178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1872 pattern childGuard
    simpa only [d21, d178, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1874 (pattern : Ten) (guard : d350 pattern = 1) : d22 pattern ≤ (1 : Int) + d179 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d22, d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1872 pattern childGuard
    simpa only [d22, d179, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d22, d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1852 pattern childGuard
    simpa only [d22, d179, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1875 (pattern : Ten) (guard : d350 pattern = 1) : d25 pattern ≤ (1 : Int) + d182 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d25, d182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1873 pattern childGuard
    simpa only [d25, d182, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d25, d182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1874 pattern childGuard
    simpa only [d25, d182, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1876 (pattern : Ten) (guard : d350 pattern = 1) : d30 pattern ≤ (1 : Int) + d185 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d30, d185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1875 pattern childGuard
    simpa only [d30, d185, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d30, d185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1864 pattern childGuard
    simpa only [d30, d185, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1877 (pattern : Ten) (guard : d350 pattern = 1) : d33 pattern ≤ (1 : Int) + d188 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d33, d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1865 pattern childGuard
    simpa only [d33, d188, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d33, d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1876 pattern childGuard
    simpa only [d33, d188, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1878 (pattern : Ten) (guard : d350 pattern = 1) : d26 pattern ≤ (1 : Int) + d181 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d26, d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1855 pattern childGuard
    simpa only [d26, d181, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d26, d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1852 pattern childGuard
    simpa only [d26, d181, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1879 (pattern : Ten) (guard : d350 pattern = 1) : d27 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1863 pattern childGuard
    simpa only [d27, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1852 pattern childGuard
    simpa only [d27, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1880 (pattern : Ten) (guard : d350 pattern = 1) : d31 pattern ≤ (1 : Int) + d186 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d31, d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1878 pattern childGuard
    simpa only [d31, d186, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d31, d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1879 pattern childGuard
    simpa only [d31, d186, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1881 (pattern : Ten) (guard : d350 pattern = 1) : d28 pattern ≤ (1 : Int) + d183 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d28, d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1874 pattern childGuard
    simpa only [d28, d183, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d28, d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1852 pattern childGuard
    simpa only [d28, d183, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1882 (pattern : Ten) (guard : d350 pattern = 1) : d32 pattern ≤ (1 : Int) + d187 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d32, d187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1881 pattern childGuard
    simpa only [d32, d187, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d32, d187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1879 pattern childGuard
    simpa only [d32, d187, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1883 (pattern : Ten) (guard : d350 pattern = 1) : d34 pattern ≤ (1 : Int) + d189 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d34, d189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1880 pattern childGuard
    simpa only [d34, d189, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d34, d189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1882 pattern childGuard
    simpa only [d34, d189, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1884 (pattern : Ten) (guard : d350 pattern = 1) : d35 pattern ≤ (1 : Int) + d190 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d35, d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1877 pattern childGuard
    simpa only [d35, d190, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d35, d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1883 pattern childGuard
    simpa only [d35, d190, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1885 (pattern : Ten) (guard : d350 pattern = 1) : d36 pattern ≤ (1 : Int) + d191 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d36, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1883 pattern childGuard
    simpa only [d36, d191, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d36, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1852 pattern childGuard
    simpa only [d36, d191, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1886 (pattern : Ten) (guard : d350 pattern = 1) : d37 pattern ≤ (1 : Int) + d192 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d37, d192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1884 pattern childGuard
    simpa only [d37, d192, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d37, d192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1885 pattern childGuard
    simpa only [d37, d192, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1887 (pattern : Ten) (guard : d1 pattern = 1) : d0 pattern ≤ (1 : Int) + d10 pattern := by
  change (0 : Int) ≤ (1 : Int) + 10
  decide
theorem c1888 (pattern : Ten) (guard : d1 pattern = 1) : d171 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1887 pattern childGuard
    simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1823 pattern childGuard
    simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1889 (pattern : Ten) (guard : d1 pattern = 1) : d173 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1888 pattern childGuard
    simpa only [d173, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1805 pattern childGuard
    simpa only [d173, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1890 (pattern : Ten) (guard : d1 pattern = 1) : d176 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1888 pattern childGuard
    simpa only [d176, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1889 pattern childGuard
    simpa only [d176, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1891 (pattern : Ten) (guard : d1 pattern = 1) : d177 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1889 pattern childGuard
    simpa only [d177, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1805 pattern childGuard
    simpa only [d177, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1892 (pattern : Ten) (guard : d1 pattern = 1) : d180 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1890 pattern childGuard
    simpa only [d180, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1891 pattern childGuard
    simpa only [d180, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1893 (pattern : Ten) (guard : d1 pattern = 1) : d181 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1891 pattern childGuard
    simpa only [d181, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1805 pattern childGuard
    simpa only [d181, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1894 (pattern : Ten) (guard : d1 pattern = 1) : d184 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1892 pattern childGuard
    simpa only [d184, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1893 pattern childGuard
    simpa only [d184, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1895 (pattern : Ten) (guard : d1 pattern = 1) : d2 pattern ≤ (1 : Int) + d10 pattern := by
  change (2 : Int) ≤ (1 : Int) + 10
  decide
theorem c1896 (pattern : Ten) (guard : d1 pattern = 1) : d172 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1895 pattern childGuard
    simpa only [d172, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1831 pattern childGuard
    simpa only [d172, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1897 (pattern : Ten) (guard : d1 pattern = 1) : d174 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1888 pattern childGuard
    simpa only [d174, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1896 pattern childGuard
    simpa only [d174, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1898 (pattern : Ten) (guard : d1 pattern = 1) : d175 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1896 pattern childGuard
    simpa only [d175, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1805 pattern childGuard
    simpa only [d175, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1899 (pattern : Ten) (guard : d1 pattern = 1) : d178 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1897 pattern childGuard
    simpa only [d178, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1898 pattern childGuard
    simpa only [d178, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1900 (pattern : Ten) (guard : d1 pattern = 1) : d179 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1898 pattern childGuard
    simpa only [d179, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1805 pattern childGuard
    simpa only [d179, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1901 (pattern : Ten) (guard : d1 pattern = 1) : d182 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1899 pattern childGuard
    simpa only [d182, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1900 pattern childGuard
    simpa only [d182, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1902 (pattern : Ten) (guard : d1 pattern = 1) : d185 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1901 pattern childGuard
    simpa only [d185, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1893 pattern childGuard
    simpa only [d185, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1903 (pattern : Ten) (guard : d1 pattern = 1) : d188 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1894 pattern childGuard
    simpa only [d188, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1902 pattern childGuard
    simpa only [d188, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1904 (pattern : Ten) (guard : d1 pattern = 1) : d186 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1893 pattern childGuard
    simpa only [d186, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1805 pattern childGuard
    simpa only [d186, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1905 (pattern : Ten) (guard : d1 pattern = 1) : d183 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1900 pattern childGuard
    simpa only [d183, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1805 pattern childGuard
    simpa only [d183, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1906 (pattern : Ten) (guard : d1 pattern = 1) : d187 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1905 pattern childGuard
    simpa only [d187, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1805 pattern childGuard
    simpa only [d187, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1907 (pattern : Ten) (guard : d1 pattern = 1) : d189 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1904 pattern childGuard
    simpa only [d189, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1906 pattern childGuard
    simpa only [d189, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1908 (pattern : Ten) (guard : d1 pattern = 1) : d190 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1903 pattern childGuard
    simpa only [d190, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1907 pattern childGuard
    simpa only [d190, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1909 (pattern : Ten) (guard : d1 pattern = 1) : d191 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1907 pattern childGuard
    simpa only [d191, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1805 pattern childGuard
    simpa only [d191, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1910 (pattern : Ten) (guard : d1 pattern = 1) : d192 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1908 pattern childGuard
    simpa only [d192, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1909 pattern childGuard
    simpa only [d192, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1911 (pattern : Ten) (guard : d352 pattern = 1) : d23 pattern ≤ (1 : Int) + d23 pattern := by
  omega
theorem c1912 (pattern : Ten) (guard : d352 pattern = 1) : d0 pattern ≤ (1 : Int) + d0 pattern := by
  omega
theorem c1913 (pattern : Ten) (guard : d0 pattern = 1) : d10 pattern ≤ (1 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1914 (pattern : Ten) (guard : d351 pattern = 1) : d11 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d351, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1857 pattern childGuard
    simpa only [d351, d11, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d351, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1913 pattern childGuard
    simpa only [d351, d11, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1915 (pattern : Ten) (guard : d352 pattern = 1) : d11 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d351 pattern = 1 := by simpa only [d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1914 pattern childGuard
    simpa only [d352, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1658 pattern childGuard
    simpa only [d352, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1916 (pattern : Ten) (guard : d352 pattern = 1) : d13 pattern ≤ (1 : Int) + d12 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d352 pattern = 1 := by simpa only [d13, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1912 pattern childGuard
    simpa only [d13, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d352 pattern = 1 := by simpa only [d13, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1915 pattern childGuard
    simpa only [d13, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1917 (pattern : Ten) (guard : d352 pattern = 1) : d10 pattern ≤ (1 : Int) + d10 pattern := by
  omega
theorem c1918 (pattern : Ten) (guard : d352 pattern = 1) : d14 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d352 pattern = 1 := by simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1915 pattern childGuard
    simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d352 pattern = 1 := by simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1917 pattern childGuard
    simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1919 (pattern : Ten) (guard : d352 pattern = 1) : d19 pattern ≤ (1 : Int) + d18 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d352 pattern = 1 := by simpa only [d19, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1916 pattern childGuard
    simpa only [d19, d18, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d352 pattern = 1 := by simpa only [d19, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1918 pattern childGuard
    simpa only [d19, d18, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban41.Diagram
