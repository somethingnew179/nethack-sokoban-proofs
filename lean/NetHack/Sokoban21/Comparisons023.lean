/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons022
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c3220 (pattern : Twelve) (guard : d1865 pattern = 1) : d1648 pattern ≤ (0 : Int) + d1750 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1648, d1750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3219 pattern childGuard
    simpa only [d1648, d1750, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1648, d1750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3031 pattern childGuard
    simpa only [d1648, d1750, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3221 (pattern : Twelve) (guard : d1865 pattern = 1) : d1654 pattern ≤ (0 : Int) + d1758 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1654, d1758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3164 pattern childGuard
    simpa only [d1654, d1758, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1654, d1758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3220 pattern childGuard
    simpa only [d1654, d1758, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3222 (pattern : Twelve) (guard : d1865 pattern = 1) : d1655 pattern ≤ (0 : Int) + d1759 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1655, d1759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3079 pattern childGuard
    simpa only [d1655, d1759, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1655, d1759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2853 pattern childGuard
    simpa only [d1655, d1759, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3223 (pattern : Twelve) (guard : d1865 pattern = 1) : d1659 pattern ≤ (0 : Int) + d1766 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1659, d1766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3221 pattern childGuard
    simpa only [d1659, d1766, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1659, d1766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3222 pattern childGuard
    simpa only [d1659, d1766, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3224 (pattern : Twelve) (guard : d1865 pattern = 1) : d1661 pattern ≤ (0 : Int) + d1771 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1661, d1771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3218 pattern childGuard
    simpa only [d1661, d1771, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1661, d1771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3223 pattern childGuard
    simpa only [d1661, d1771, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3225 (pattern : Twelve) (guard : d1865 pattern = 1) : d1662 pattern ≤ (0 : Int) + d1772 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1662, d1772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3214 pattern childGuard
    simpa only [d1662, d1772, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1662, d1772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2853 pattern childGuard
    simpa only [d1662, d1772, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3226 (pattern : Twelve) (guard : d1865 pattern = 1) : d1663 pattern ≤ (0 : Int) + d1775 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1663, d1775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3224 pattern childGuard
    simpa only [d1663, d1775, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1663, d1775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3225 pattern childGuard
    simpa only [d1663, d1775, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3227 (pattern : Twelve) (guard : d1865 pattern = 1) : d1664 pattern ≤ (0 : Int) + d1777 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1664, d1777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3215 pattern childGuard
    simpa only [d1664, d1777, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1664, d1777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3226 pattern childGuard
    simpa only [d1664, d1777, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3228 (pattern : Twelve) (guard : d1865 pattern = 1) : d1668 pattern ≤ (0 : Int) + d1760 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1668, d1760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2852 pattern childGuard
    simpa only [d1668, d1760, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1668, d1760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3210 pattern childGuard
    simpa only [d1668, d1760, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3229 (pattern : Twelve) (guard : d1865 pattern = 1) : d1671 pattern ≤ (0 : Int) + d1767 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1671, d1767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3228 pattern childGuard
    simpa only [d1671, d1767, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1671, d1767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3208 pattern childGuard
    simpa only [d1671, d1767, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3230 (pattern : Twelve) (guard : d1865 pattern = 1) : d1674 pattern ≤ (0 : Int) + d1773 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1674, d1773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3229 pattern childGuard
    simpa only [d1674, d1773, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1674, d1773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3214 pattern childGuard
    simpa only [d1674, d1773, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3231 (pattern : Twelve) (guard : d1865 pattern = 1) : d1665 pattern ≤ (0 : Int) + d1748 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1665, d1748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3176 pattern childGuard
    simpa only [d1665, d1748, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1665, d1748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2880 pattern childGuard
    simpa only [d1665, d1748, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3232 (pattern : Twelve) (guard : d1865 pattern = 1) : d1666 pattern ≤ (0 : Int) + d1751 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1666, d1751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3210 pattern childGuard
    simpa only [d1666, d1751, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1666, d1751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3231 pattern childGuard
    simpa only [d1666, d1751, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3233 (pattern : Twelve) (guard : d1865 pattern = 1) : d1669 pattern ≤ (0 : Int) + d1761 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1669, d1761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3047 pattern childGuard
    simpa only [d1669, d1761, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1669, d1761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3232 pattern childGuard
    simpa only [d1669, d1761, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3234 (pattern : Twelve) (guard : d1865 pattern = 1) : d1672 pattern ≤ (0 : Int) + d1768 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1672, d1768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3233 pattern childGuard
    simpa only [d1672, d1768, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1672, d1768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3165 pattern childGuard
    simpa only [d1672, d1768, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3235 (pattern : Twelve) (guard : d1865 pattern = 1) : d183 pattern ≤ (0 : Int) + d183 pattern := by
  omega
theorem c3236 (pattern : Twelve) (guard : d1865 pattern = 1) : d1667 pattern ≤ (0 : Int) + d1752 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1667, d1752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3031 pattern childGuard
    simpa only [d1667, d1752, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1667, d1752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3235 pattern childGuard
    simpa only [d1667, d1752, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3237 (pattern : Twelve) (guard : d1865 pattern = 1) : d1670 pattern ≤ (0 : Int) + d1762 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1670, d1762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3164 pattern childGuard
    simpa only [d1670, d1762, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1670, d1762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3236 pattern childGuard
    simpa only [d1670, d1762, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3238 (pattern : Twelve) (guard : d1865 pattern = 1) : d1252 pattern ≤ (0 : Int) + d191 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1252, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3079 pattern childGuard
    simpa only [d1252, d191, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1252, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2853 pattern childGuard
    simpa only [d1252, d191, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3239 (pattern : Twelve) (guard : d1865 pattern = 1) : d1626 pattern ≤ (0 : Int) + d202 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1626, d202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3238 pattern childGuard
    simpa only [d1626, d202, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1626, d202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2853 pattern childGuard
    simpa only [d1626, d202, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3240 (pattern : Twelve) (guard : d1865 pattern = 1) : d1673 pattern ≤ (0 : Int) + d1769 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1673, d1769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3237 pattern childGuard
    simpa only [d1673, d1769, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1673, d1769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3239 pattern childGuard
    simpa only [d1673, d1769, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3241 (pattern : Twelve) (guard : d1865 pattern = 1) : d1675 pattern ≤ (0 : Int) + d1774 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1675, d1774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3234 pattern childGuard
    simpa only [d1675, d1774, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1675, d1774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3240 pattern childGuard
    simpa only [d1675, d1774, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3242 (pattern : Twelve) (guard : d1865 pattern = 1) : d1676 pattern ≤ (0 : Int) + d1776 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1676, d1776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3241 pattern childGuard
    simpa only [d1676, d1776, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1676, d1776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3225 pattern childGuard
    simpa only [d1676, d1776, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3243 (pattern : Twelve) (guard : d1865 pattern = 1) : d1677 pattern ≤ (0 : Int) + d1778 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1677, d1778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3230 pattern childGuard
    simpa only [d1677, d1778, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1677, d1778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3242 pattern childGuard
    simpa only [d1677, d1778, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3244 (pattern : Twelve) (guard : d1865 pattern = 1) : d1678 pattern ≤ (0 : Int) + d1779 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1678, d1779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3227 pattern childGuard
    simpa only [d1678, d1779, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1678, d1779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3243 pattern childGuard
    simpa only [d1678, d1779, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3245 (pattern : Twelve) (guard : d1867 pattern = 1) : d0 pattern ≤ (0 : Int) + d0 pattern := by
  omega
theorem c3246 (pattern : Twelve) (guard : d1866 pattern = 1) : d0 pattern ≤ (0 : Int) + d7 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1866, d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1866, d7, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1866, d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1262 pattern childGuard
    simpa only [d1866, d7, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3247 (pattern : Twelve) (guard : d0 pattern = 1) : d0 pattern ≤ (0 : Int) + d7 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3248 (pattern : Twelve) (guard : d1867 pattern = 1) : d0 pattern ≤ (0 : Int) + d7 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3246 pattern childGuard
    simpa only [d1867, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3247 pattern childGuard
    simpa only [d1867, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3249 (pattern : Twelve) (guard : d1867 pattern = 1) : d0 pattern ≤ (0 : Int) + d646 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3245 pattern childGuard
    simpa only [d646, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3248 pattern childGuard
    simpa only [d646, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3250 (pattern : Twelve) (guard : d1867 pattern = 1) : d0 pattern ≤ (0 : Int) + d634 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3246 pattern childGuard
    simpa only [d1867, d634, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2841 pattern childGuard
    simpa only [d1867, d634, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3251 (pattern : Twelve) (guard : d1867 pattern = 1) : d0 pattern ≤ (0 : Int) + d647 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3245 pattern childGuard
    simpa only [d647, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3250 pattern childGuard
    simpa only [d647, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3252 (pattern : Twelve) (guard : d1867 pattern = 1) : d0 pattern ≤ (0 : Int) + d680 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3249 pattern childGuard
    simpa only [d680, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3251 pattern childGuard
    simpa only [d680, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3253 (pattern : Twelve) (guard : d1866 pattern = 1) : d1 pattern ≤ (0 : Int) + d1 pattern := by
  omega
theorem c3254 (pattern : Twelve) (guard : d1867 pattern = 1) : d1 pattern ≤ (0 : Int) + d161 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3253 pattern childGuard
    simpa only [d1867, d161, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2832 pattern childGuard
    simpa only [d1867, d161, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3255 (pattern : Twelve) (guard : d1867 pattern = 1) : d26 pattern ≤ (0 : Int) + d171 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d26, d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3245 pattern childGuard
    simpa only [d26, d171, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d26, d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3254 pattern childGuard
    simpa only [d26, d171, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3256 (pattern : Twelve) (guard : d1866 pattern = 1) : d0 pattern ≤ (0 : Int) + d0 pattern := by
  omega
theorem c3257 (pattern : Twelve) (guard : d1867 pattern = 1) : d17 pattern ≤ (0 : Int) + d162 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d17, d162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3256 pattern childGuard
    simpa only [d1867, d17, d162, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d17, d162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2835 pattern childGuard
    simpa only [d1867, d17, d162, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3258 (pattern : Twelve) (guard : d1866 pattern = 1) : d1 pattern ≤ (0 : Int) + d157 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1866, d157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2831 pattern childGuard
    simpa only [d1866, d157, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1866, d157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1356 pattern childGuard
    simpa only [d1866, d157, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3259 (pattern : Twelve) (guard : d1867 pattern = 1) : d1 pattern ≤ (0 : Int) + d157 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3258 pattern childGuard
    simpa only [d1867, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2832 pattern childGuard
    simpa only [d1867, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3260 (pattern : Twelve) (guard : d1867 pattern = 1) : d27 pattern ≤ (0 : Int) + d648 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d27, d648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3257 pattern childGuard
    simpa only [d27, d648, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d27, d648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3259 pattern childGuard
    simpa only [d27, d648, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3261 (pattern : Twelve) (guard : d1867 pattern = 1) : d50 pattern ≤ (0 : Int) + d681 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d50, d681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3255 pattern childGuard
    simpa only [d50, d681, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d50, d681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3260 pattern childGuard
    simpa only [d50, d681, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3262 (pattern : Twelve) (guard : d1867 pattern = 1) : d72 pattern ≤ (0 : Int) + d709 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d72, d709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3252 pattern childGuard
    simpa only [d72, d709, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d72, d709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3261 pattern childGuard
    simpa only [d72, d709, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3263 (pattern : Twelve) (guard : d1867 pattern = 1) : d0 pattern ≤ (0 : Int) + d162 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3256 pattern childGuard
    simpa only [d1867, d162, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2841 pattern childGuard
    simpa only [d1867, d162, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3264 (pattern : Twelve) (guard : d1866 pattern = 1) : d0 pattern ≤ (0 : Int) + d158 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1866, d158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1866, d158, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1866, d158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c157 pattern childGuard
    simpa only [d1866, d158, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3265 (pattern : Twelve) (guard : d1867 pattern = 1) : d0 pattern ≤ (0 : Int) + d158 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3264 pattern childGuard
    simpa only [d1867, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2841 pattern childGuard
    simpa only [d1867, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3266 (pattern : Twelve) (guard : d1867 pattern = 1) : d0 pattern ≤ (0 : Int) + d649 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3263 pattern childGuard
    simpa only [d649, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3265 pattern childGuard
    simpa only [d649, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3267 (pattern : Twelve) (guard : d1867 pattern = 1) : d0 pattern ≤ (0 : Int) + d682 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3251 pattern childGuard
    simpa only [d682, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3266 pattern childGuard
    simpa only [d682, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3268 (pattern : Twelve) (guard : d1866 pattern = 1) : d8 pattern ≤ (0 : Int) + d157 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1866, d8, d157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2831 pattern childGuard
    simpa only [d1866, d8, d157, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1866, d8, d157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1311 pattern childGuard
    simpa only [d1866, d8, d157, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3269 (pattern : Twelve) (guard : d0 pattern = 1) : d9 pattern ≤ (0 : Int) + d160 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3270 (pattern : Twelve) (guard : d1867 pattern = 1) : d18 pattern ≤ (0 : Int) + d635 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d18, d635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3268 pattern childGuard
    simpa only [d1867, d18, d635, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d18, d635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3269 pattern childGuard
    simpa only [d1867, d18, d635, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3271 (pattern : Twelve) (guard : d1867 pattern = 1) : d28 pattern ≤ (0 : Int) + d650 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d28, d650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3257 pattern childGuard
    simpa only [d28, d650, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d28, d650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3270 pattern childGuard
    simpa only [d28, d650, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3272 (pattern : Twelve) (guard : d1866 pattern = 1) : d10 pattern ≤ (0 : Int) + d158 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1866, d10, d158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1866, d10, d158, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1866, d10, d158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1311 pattern childGuard
    simpa only [d1866, d10, d158, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3273 (pattern : Twelve) (guard : d0 pattern = 1) : d11 pattern ≤ (0 : Int) + d157 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3274 (pattern : Twelve) (guard : d1867 pattern = 1) : d19 pattern ≤ (0 : Int) + d636 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d19, d636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3272 pattern childGuard
    simpa only [d1867, d19, d636, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d19, d636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3273 pattern childGuard
    simpa only [d1867, d19, d636, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3275 (pattern : Twelve) (guard : d1867 pattern = 1) : d6 pattern ≤ (0 : Int) + d6 pattern := by
  omega
theorem c3276 (pattern : Twelve) (guard : d1867 pattern = 1) : d29 pattern ≤ (0 : Int) + d651 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d29, d651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3274 pattern childGuard
    simpa only [d29, d651, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d29, d651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d29, d651, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3277 (pattern : Twelve) (guard : d1867 pattern = 1) : d51 pattern ≤ (0 : Int) + d683 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d51, d683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3271 pattern childGuard
    simpa only [d51, d683, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d51, d683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3276 pattern childGuard
    simpa only [d51, d683, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3278 (pattern : Twelve) (guard : d1867 pattern = 1) : d73 pattern ≤ (0 : Int) + d710 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d73, d710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3267 pattern childGuard
    simpa only [d73, d710, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d73, d710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3277 pattern childGuard
    simpa only [d73, d710, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3279 (pattern : Twelve) (guard : d1867 pattern = 1) : d91 pattern ≤ (0 : Int) + d736 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d91, d736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3262 pattern childGuard
    simpa only [d91, d736, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d91, d736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3278 pattern childGuard
    simpa only [d91, d736, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3280 (pattern : Twelve) (guard : d1866 pattern = 1) : d0 pattern ≤ (0 : Int) + d10 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1866, d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1866, d10, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1866, d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2858 pattern childGuard
    simpa only [d1866, d10, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3281 (pattern : Twelve) (guard : d0 pattern = 1) : d0 pattern ≤ (0 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3282 (pattern : Twelve) (guard : d1867 pattern = 1) : d0 pattern ≤ (0 : Int) + d10 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3280 pattern childGuard
    simpa only [d1867, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3281 pattern childGuard
    simpa only [d1867, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3283 (pattern : Twelve) (guard : d0 pattern = 1) : d2 pattern ≤ (0 : Int) + d3 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3284 (pattern : Twelve) (guard : d1866 pattern = 1) : d2 pattern ≤ (0 : Int) + d9 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1866, d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1333 pattern childGuard
    simpa only [d1866, d9, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1866, d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3283 pattern childGuard
    simpa only [d1866, d9, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3285 (pattern : Twelve) (guard : d0 pattern = 1) : d2 pattern ≤ (0 : Int) + d160 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3286 (pattern : Twelve) (guard : d1867 pattern = 1) : d2 pattern ≤ (0 : Int) + d637 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3284 pattern childGuard
    simpa only [d1867, d637, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3285 pattern childGuard
    simpa only [d1867, d637, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3287 (pattern : Twelve) (guard : d1867 pattern = 1) : d30 pattern ≤ (0 : Int) + d652 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d30, d652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3282 pattern childGuard
    simpa only [d30, d652, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d30, d652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3286 pattern childGuard
    simpa only [d30, d652, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3288 (pattern : Twelve) (guard : d1867 pattern = 1) : d0 pattern ≤ (0 : Int) + d638 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3280 pattern childGuard
    simpa only [d1867, d638, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2841 pattern childGuard
    simpa only [d1867, d638, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3289 (pattern : Twelve) (guard : d1866 pattern = 1) : d12 pattern ≤ (0 : Int) + d159 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1866, d12, d159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2922 pattern childGuard
    simpa only [d1866, d12, d159, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1866, d12, d159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3025 pattern childGuard
    simpa only [d1866, d12, d159, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3290 (pattern : Twelve) (guard : d0 pattern = 1) : d13 pattern ≤ (0 : Int) + d13 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3291 (pattern : Twelve) (guard : d1867 pattern = 1) : d20 pattern ≤ (0 : Int) + d639 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d20, d639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3289 pattern childGuard
    simpa only [d1867, d20, d639, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d20, d639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3290 pattern childGuard
    simpa only [d1867, d20, d639, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3292 (pattern : Twelve) (guard : d1867 pattern = 1) : d31 pattern ≤ (0 : Int) + d653 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d31, d653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3288 pattern childGuard
    simpa only [d31, d653, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d31, d653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3291 pattern childGuard
    simpa only [d31, d653, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3293 (pattern : Twelve) (guard : d1867 pattern = 1) : d52 pattern ≤ (0 : Int) + d684 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d52, d684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3287 pattern childGuard
    simpa only [d52, d684, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d52, d684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3292 pattern childGuard
    simpa only [d52, d684, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3294 (pattern : Twelve) (guard : d1866 pattern = 1) : d2 pattern ≤ (0 : Int) + d160 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1866, d160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1333 pattern childGuard
    simpa only [d1866, d160, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1866, d160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1311 pattern childGuard
    simpa only [d1866, d160, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3295 (pattern : Twelve) (guard : d1867 pattern = 1) : d2 pattern ≤ (0 : Int) + d160 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3294 pattern childGuard
    simpa only [d1867, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3285 pattern childGuard
    simpa only [d1867, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3296 (pattern : Twelve) (guard : d1867 pattern = 1) : d30 pattern ≤ (0 : Int) + d654 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d30, d654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3288 pattern childGuard
    simpa only [d30, d654, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d30, d654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3295 pattern childGuard
    simpa only [d30, d654, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3297 (pattern : Twelve) (guard : d1867 pattern = 1) : d17 pattern ≤ (0 : Int) + d158 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3264 pattern childGuard
    simpa only [d1867, d17, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2835 pattern childGuard
    simpa only [d1867, d17, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3298 (pattern : Twelve) (guard : d1867 pattern = 1) : d21 pattern ≤ (0 : Int) + d21 pattern := by
  omega
theorem c3299 (pattern : Twelve) (guard : d1867 pattern = 1) : d32 pattern ≤ (0 : Int) + d655 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d32, d655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3297 pattern childGuard
    simpa only [d32, d655, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d32, d655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3298 pattern childGuard
    simpa only [d32, d655, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3300 (pattern : Twelve) (guard : d1867 pattern = 1) : d53 pattern ≤ (0 : Int) + d685 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d53, d685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3296 pattern childGuard
    simpa only [d53, d685, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d53, d685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3299 pattern childGuard
    simpa only [d53, d685, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3301 (pattern : Twelve) (guard : d1867 pattern = 1) : d74 pattern ≤ (0 : Int) + d711 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d74, d711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3293 pattern childGuard
    simpa only [d74, d711, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d74, d711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3300 pattern childGuard
    simpa only [d74, d711, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3302 (pattern : Twelve) (guard : d1867 pattern = 1) : d22 pattern ≤ (0 : Int) + d22 pattern := by
  omega
theorem c3303 (pattern : Twelve) (guard : d1867 pattern = 1) : d33 pattern ≤ (0 : Int) + d656 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d33, d656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3265 pattern childGuard
    simpa only [d33, d656, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d33, d656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3302 pattern childGuard
    simpa only [d33, d656, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3304 (pattern : Twelve) (guard : d1867 pattern = 1) : d54 pattern ≤ (0 : Int) + d686 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d54, d686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3296 pattern childGuard
    simpa only [d54, d686, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d54, d686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3303 pattern childGuard
    simpa only [d54, d686, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3305 (pattern : Twelve) (guard : d1867 pattern = 1) : d23 pattern ≤ (0 : Int) + d160 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3294 pattern childGuard
    simpa only [d1867, d23, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3269 pattern childGuard
    simpa only [d1867, d23, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3306 (pattern : Twelve) (guard : d1867 pattern = 1) : d34 pattern ≤ (0 : Int) + d657 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d34, d657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3297 pattern childGuard
    simpa only [d34, d657, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d34, d657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3305 pattern childGuard
    simpa only [d34, d657, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3307 (pattern : Twelve) (guard : d1867 pattern = 1) : d55 pattern ≤ (0 : Int) + d687 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d55, d687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3306 pattern childGuard
    simpa only [d55, d687, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d55, d687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3276 pattern childGuard
    simpa only [d55, d687, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3308 (pattern : Twelve) (guard : d1867 pattern = 1) : d75 pattern ≤ (0 : Int) + d712 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d75, d712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3304 pattern childGuard
    simpa only [d75, d712, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d75, d712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3307 pattern childGuard
    simpa only [d75, d712, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3309 (pattern : Twelve) (guard : d1867 pattern = 1) : d92 pattern ≤ (0 : Int) + d737 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d92, d737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3301 pattern childGuard
    simpa only [d92, d737, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d92, d737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3308 pattern childGuard
    simpa only [d92, d737, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3310 (pattern : Twelve) (guard : d1867 pattern = 1) : d102 pattern ≤ (0 : Int) + d754 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d102, d754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3279 pattern childGuard
    simpa only [d102, d754, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d102, d754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3309 pattern childGuard
    simpa only [d102, d754, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3311 (pattern : Twelve) (guard : d1866 pattern = 1) : d0 pattern ≤ (0 : Int) + d630 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1866, d630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1866, d630, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1866, d630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2915 pattern childGuard
    simpa only [d1866, d630, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3312 (pattern : Twelve) (guard : d1867 pattern = 1) : d0 pattern ≤ (0 : Int) + d640 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3311 pattern childGuard
    simpa only [d1867, d640, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2841 pattern childGuard
    simpa only [d1867, d640, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3313 (pattern : Twelve) (guard : d1867 pattern = 1) : d0 pattern ≤ (0 : Int) + d658 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3282 pattern childGuard
    simpa only [d658, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3312 pattern childGuard
    simpa only [d658, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3314 (pattern : Twelve) (guard : d1867 pattern = 1) : d0 pattern ≤ (0 : Int) + d659 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3288 pattern childGuard
    simpa only [d659, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3265 pattern childGuard
    simpa only [d659, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3315 (pattern : Twelve) (guard : d1867 pattern = 1) : d0 pattern ≤ (0 : Int) + d688 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3313 pattern childGuard
    simpa only [d688, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3314 pattern childGuard
    simpa only [d688, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3316 (pattern : Twelve) (guard : d1867 pattern = 1) : d26 pattern ≤ (0 : Int) + d660 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d26, d660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3288 pattern childGuard
    simpa only [d26, d660, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d26, d660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3259 pattern childGuard
    simpa only [d26, d660, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3317 (pattern : Twelve) (guard : d1867 pattern = 1) : d27 pattern ≤ (0 : Int) + d661 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d27, d661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3297 pattern childGuard
    simpa only [d27, d661, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d27, d661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3259 pattern childGuard
    simpa only [d27, d661, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3318 (pattern : Twelve) (guard : d1867 pattern = 1) : d50 pattern ≤ (0 : Int) + d689 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d50, d689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3316 pattern childGuard
    simpa only [d50, d689, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d50, d689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3317 pattern childGuard
    simpa only [d50, d689, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3319 (pattern : Twelve) (guard : d1867 pattern = 1) : d72 pattern ≤ (0 : Int) + d713 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d72, d713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3315 pattern childGuard
    simpa only [d72, d713, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d72, d713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3318 pattern childGuard
    simpa only [d72, d713, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3320 (pattern : Twelve) (guard : d1867 pattern = 1) : d0 pattern ≤ (0 : Int) + d690 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3314 pattern childGuard
    simpa only [d690, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3265 pattern childGuard
    simpa only [d690, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3321 (pattern : Twelve) (guard : d1867 pattern = 1) : d76 pattern ≤ (0 : Int) + d714 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d76, d714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3320 pattern childGuard
    simpa only [d76, d714, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d76, d714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3307 pattern childGuard
    simpa only [d76, d714, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3322 (pattern : Twelve) (guard : d1867 pattern = 1) : d93 pattern ≤ (0 : Int) + d738 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d93, d738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3319 pattern childGuard
    simpa only [d93, d738, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d93, d738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3321 pattern childGuard
    simpa only [d93, d738, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3323 (pattern : Twelve) (guard : d0 pattern = 1) : d0 pattern ≤ (0 : Int) + d4 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3324 (pattern : Twelve) (guard : d1866 pattern = 1) : d0 pattern ≤ (0 : Int) + d631 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1866, d631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1866, d631, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1866, d631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3323 pattern childGuard
    simpa only [d1866, d631, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3325 (pattern : Twelve) (guard : d1867 pattern = 1) : d0 pattern ≤ (0 : Int) + d641 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3324 pattern childGuard
    simpa only [d1867, d641, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2841 pattern childGuard
    simpa only [d1867, d641, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3326 (pattern : Twelve) (guard : d1867 pattern = 1) : d30 pattern ≤ (0 : Int) + d662 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d30, d662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3325 pattern childGuard
    simpa only [d30, d662, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d30, d662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3295 pattern childGuard
    simpa only [d30, d662, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3327 (pattern : Twelve) (guard : d1867 pattern = 1) : d35 pattern ≤ (0 : Int) + d663 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d35, d663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3265 pattern childGuard
    simpa only [d35, d663, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d35, d663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d35, d663, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3328 (pattern : Twelve) (guard : d1867 pattern = 1) : d56 pattern ≤ (0 : Int) + d691 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d56, d691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3326 pattern childGuard
    simpa only [d56, d691, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d56, d691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3327 pattern childGuard
    simpa only [d56, d691, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3329 (pattern : Twelve) (guard : d1867 pattern = 1) : d30 pattern ≤ (0 : Int) + d657 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d30, d657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3265 pattern childGuard
    simpa only [d30, d657, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d30, d657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3295 pattern childGuard
    simpa only [d30, d657, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3330 (pattern : Twelve) (guard : d1867 pattern = 1) : d36 pattern ≤ (0 : Int) + d663 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d36, d663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3297 pattern childGuard
    simpa only [d36, d663, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d36, d663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d36, d663, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3331 (pattern : Twelve) (guard : d1867 pattern = 1) : d57 pattern ≤ (0 : Int) + d692 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d57, d692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3329 pattern childGuard
    simpa only [d57, d692, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d57, d692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3330 pattern childGuard
    simpa only [d57, d692, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3332 (pattern : Twelve) (guard : d1867 pattern = 1) : d77 pattern ≤ (0 : Int) + d715 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d77, d715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3328 pattern childGuard
    simpa only [d77, d715, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d77, d715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3331 pattern childGuard
    simpa only [d77, d715, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3333 (pattern : Twelve) (guard : d1867 pattern = 1) : d56 pattern ≤ (0 : Int) + d692 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d56, d692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3329 pattern childGuard
    simpa only [d56, d692, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d56, d692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3327 pattern childGuard
    simpa only [d56, d692, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3334 (pattern : Twelve) (guard : d1867 pattern = 1) : d78 pattern ≤ (0 : Int) + d716 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d78, d716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3333 pattern childGuard
    simpa only [d78, d716, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d78, d716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3307 pattern childGuard
    simpa only [d78, d716, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3335 (pattern : Twelve) (guard : d1867 pattern = 1) : d94 pattern ≤ (0 : Int) + d739 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d94, d739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3332 pattern childGuard
    simpa only [d94, d739, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d94, d739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3334 pattern childGuard
    simpa only [d94, d739, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3336 (pattern : Twelve) (guard : d1867 pattern = 1) : d103 pattern ≤ (0 : Int) + d755 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d103, d755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3322 pattern childGuard
    simpa only [d103, d755, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d103, d755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3335 pattern childGuard
    simpa only [d103, d755, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3337 (pattern : Twelve) (guard : d1867 pattern = 1) : d110 pattern ≤ (0 : Int) + d766 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d110, d766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3310 pattern childGuard
    simpa only [d110, d766, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d110, d766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3336 pattern childGuard
    simpa only [d110, d766, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3338 (pattern : Twelve) (guard : d0 pattern = 1) : d0 pattern ≤ (0 : Int) + d630 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3339 (pattern : Twelve) (guard : d1867 pattern = 1) : d0 pattern ≤ (0 : Int) + d630 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3311 pattern childGuard
    simpa only [d1867, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3338 pattern childGuard
    simpa only [d1867, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3340 (pattern : Twelve) (guard : d0 pattern = 1) : d2 pattern ≤ (0 : Int) + d4 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3341 (pattern : Twelve) (guard : d1866 pattern = 1) : d2 pattern ≤ (0 : Int) + d16 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1866, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1333 pattern childGuard
    simpa only [d1866, d16, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1866, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3340 pattern childGuard
    simpa only [d1866, d16, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3342 (pattern : Twelve) (guard : d1867 pattern = 1) : d2 pattern ≤ (0 : Int) + d642 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3341 pattern childGuard
    simpa only [d1867, d642, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3285 pattern childGuard
    simpa only [d1867, d642, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3343 (pattern : Twelve) (guard : d1867 pattern = 1) : d30 pattern ≤ (0 : Int) + d664 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d30, d664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3339 pattern childGuard
    simpa only [d30, d664, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d30, d664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3342 pattern childGuard
    simpa only [d30, d664, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3344 (pattern : Twelve) (guard : d1867 pattern = 1) : d30 pattern ≤ (0 : Int) + d665 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d30, d665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3312 pattern childGuard
    simpa only [d30, d665, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d30, d665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3295 pattern childGuard
    simpa only [d30, d665, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3345 (pattern : Twelve) (guard : d1867 pattern = 1) : d30 pattern ≤ (0 : Int) + d693 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3343 pattern childGuard
    simpa only [d693, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3344 pattern childGuard
    simpa only [d693, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3346 (pattern : Twelve) (guard : d1866 pattern = 1) : d3 pattern ≤ (0 : Int) + d159 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1866, d159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2922 pattern childGuard
    simpa only [d1866, d159, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1866, d159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2923 pattern childGuard
    simpa only [d1866, d159, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3347 (pattern : Twelve) (guard : d0 pattern = 1) : d3 pattern ≤ (0 : Int) + d159 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3348 (pattern : Twelve) (guard : d1867 pattern = 1) : d3 pattern ≤ (0 : Int) + d159 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3346 pattern childGuard
    simpa only [d1867, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3347 pattern childGuard
    simpa only [d1867, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3349 (pattern : Twelve) (guard : d1867 pattern = 1) : d37 pattern ≤ (0 : Int) + d666 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d37, d666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3297 pattern childGuard
    simpa only [d37, d666, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d37, d666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3348 pattern childGuard
    simpa only [d37, d666, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3350 (pattern : Twelve) (guard : d1867 pattern = 1) : d58 pattern ≤ (0 : Int) + d694 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d58, d694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3344 pattern childGuard
    simpa only [d58, d694, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d58, d694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3349 pattern childGuard
    simpa only [d58, d694, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3351 (pattern : Twelve) (guard : d1867 pattern = 1) : d79 pattern ≤ (0 : Int) + d717 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d79, d717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3345 pattern childGuard
    simpa only [d79, d717, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d79, d717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3350 pattern childGuard
    simpa only [d79, d717, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3352 (pattern : Twelve) (guard : d1867 pattern = 1) : d30 pattern ≤ (0 : Int) + d695 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3344 pattern childGuard
    simpa only [d695, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3329 pattern childGuard
    simpa only [d695, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3353 (pattern : Twelve) (guard : d1867 pattern = 1) : d80 pattern ≤ (0 : Int) + d718 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d80, d718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3352 pattern childGuard
    simpa only [d80, d718, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d80, d718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3307 pattern childGuard
    simpa only [d80, d718, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3354 (pattern : Twelve) (guard : d1867 pattern = 1) : d95 pattern ≤ (0 : Int) + d740 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d95, d740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3351 pattern childGuard
    simpa only [d95, d740, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d95, d740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3353 pattern childGuard
    simpa only [d95, d740, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3355 (pattern : Twelve) (guard : d0 pattern = 1) : d2 pattern ≤ (0 : Int) + d5 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3356 (pattern : Twelve) (guard : d1866 pattern = 1) : d2 pattern ≤ (0 : Int) + d632 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1866, d632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1333 pattern childGuard
    simpa only [d1866, d632, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1866, d632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3355 pattern childGuard
    simpa only [d1866, d632, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3357 (pattern : Twelve) (guard : d1867 pattern = 1) : d2 pattern ≤ (0 : Int) + d643 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3356 pattern childGuard
    simpa only [d1867, d643, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3285 pattern childGuard
    simpa only [d1867, d643, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3358 (pattern : Twelve) (guard : d1866 pattern = 1) : d4 pattern ≤ (0 : Int) + d13 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1866, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2933 pattern childGuard
    simpa only [d1866, d13, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1866, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1334 pattern childGuard
    simpa only [d1866, d13, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3359 (pattern : Twelve) (guard : d0 pattern = 1) : d4 pattern ≤ (0 : Int) + d13 pattern := by
  change (0 : Int) = 1 at guard
  omega
end NetHack.Sokoban21.Diagram
