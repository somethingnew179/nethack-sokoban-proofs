/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons038
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c5460 (pattern : Twelve) (guard : d1870 pattern = 1) : d1716 pattern ≤ (0 : Int) + d1298 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1870, d1716, d1298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5096 pattern childGuard
    simpa only [d1870, d1716, d1298, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1870, d1716, d1298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c398 pattern childGuard
    simpa only [d1870, d1716, d1298, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5461 (pattern : Twelve) (guard : d1870 pattern = 1) : d1452 pattern ≤ (0 : Int) + d1653 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1870, d1452, d1653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5123 pattern childGuard
    simpa only [d1870, d1452, d1653, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1870, d1452, d1653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d1870, d1452, d1653, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5462 (pattern : Twelve) (guard : d1870 pattern = 1) : d1719 pattern ≤ (0 : Int) + d1732 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1719, d1732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5460 pattern childGuard
    simpa only [d1719, d1732, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1719, d1732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5461 pattern childGuard
    simpa only [d1719, d1732, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5463 (pattern : Twelve) (guard : d1870 pattern = 1) : d1717 pattern ≤ (0 : Int) + d1300 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1870, d1717, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5429 pattern childGuard
    simpa only [d1870, d1717, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1870, d1717, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c411 pattern childGuard
    simpa only [d1870, d1717, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5464 (pattern : Twelve) (guard : d1870 pattern = 1) : d1655 pattern ≤ (0 : Int) + d1655 pattern := by
  omega
theorem c5465 (pattern : Twelve) (guard : d1870 pattern = 1) : d1720 pattern ≤ (0 : Int) + d1733 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1720, d1733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5463 pattern childGuard
    simpa only [d1720, d1733, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1720, d1733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5464 pattern childGuard
    simpa only [d1720, d1733, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5466 (pattern : Twelve) (guard : d1870 pattern = 1) : d1722 pattern ≤ (0 : Int) + d1737 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1722, d1737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5462 pattern childGuard
    simpa only [d1722, d1737, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1722, d1737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5465 pattern childGuard
    simpa only [d1722, d1737, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5467 (pattern : Twelve) (guard : d1870 pattern = 1) : d1723 pattern ≤ (0 : Int) + d1738 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1723, d1738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5458 pattern childGuard
    simpa only [d1723, d1738, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1723, d1738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5294 pattern childGuard
    simpa only [d1723, d1738, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5468 (pattern : Twelve) (guard : d1870 pattern = 1) : d1725 pattern ≤ (0 : Int) + d1740 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1725, d1740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5466 pattern childGuard
    simpa only [d1725, d1740, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1725, d1740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5467 pattern childGuard
    simpa only [d1725, d1740, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5469 (pattern : Twelve) (guard : d1870 pattern = 1) : d1727 pattern ≤ (0 : Int) + d1742 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1727, d1742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5459 pattern childGuard
    simpa only [d1727, d1742, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1727, d1742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5468 pattern childGuard
    simpa only [d1727, d1742, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5470 (pattern : Twelve) (guard : d1870 pattern = 1) : d1719 pattern ≤ (0 : Int) + d1734 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1719, d1734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5460 pattern childGuard
    simpa only [d1719, d1734, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1719, d1734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5430 pattern childGuard
    simpa only [d1719, d1734, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5471 (pattern : Twelve) (guard : d0 pattern = 1) : d1667 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5472 (pattern : Twelve) (guard : d1870 pattern = 1) : d1718 pattern ≤ (0 : Int) + d1300 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1870, d1718, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5429 pattern childGuard
    simpa only [d1870, d1718, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1870, d1718, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5471 pattern childGuard
    simpa only [d1870, d1718, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5473 (pattern : Twelve) (guard : d1870 pattern = 1) : d1626 pattern ≤ (0 : Int) + d1626 pattern := by
  omega
theorem c5474 (pattern : Twelve) (guard : d1870 pattern = 1) : d1721 pattern ≤ (0 : Int) + d1735 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1721, d1735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5472 pattern childGuard
    simpa only [d1721, d1735, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1721, d1735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5473 pattern childGuard
    simpa only [d1721, d1735, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5475 (pattern : Twelve) (guard : d1870 pattern = 1) : d1724 pattern ≤ (0 : Int) + d1739 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1724, d1739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5470 pattern childGuard
    simpa only [d1724, d1739, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1724, d1739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5474 pattern childGuard
    simpa only [d1724, d1739, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5476 (pattern : Twelve) (guard : d1870 pattern = 1) : d1726 pattern ≤ (0 : Int) + d1741 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1726, d1741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5475 pattern childGuard
    simpa only [d1726, d1741, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1726, d1741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5467 pattern childGuard
    simpa only [d1726, d1741, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5477 (pattern : Twelve) (guard : d1870 pattern = 1) : d1728 pattern ≤ (0 : Int) + d1743 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1728, d1743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5459 pattern childGuard
    simpa only [d1728, d1743, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1728, d1743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5476 pattern childGuard
    simpa only [d1728, d1743, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5478 (pattern : Twelve) (guard : d1870 pattern = 1) : d1729 pattern ≤ (0 : Int) + d1744 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1729, d1744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5469 pattern childGuard
    simpa only [d1729, d1744, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1729, d1744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5477 pattern childGuard
    simpa only [d1729, d1744, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5479 (pattern : Twelve) (guard : d1848 pattern = 1) : d372 pattern ≤ (0 : Int) + d50 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d372, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4961 pattern childGuard
    simpa only [d372, d50, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d372, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5088 pattern childGuard
    simpa only [d372, d50, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5480 (pattern : Twelve) (guard : d1848 pattern = 1) : d389 pattern ≤ (0 : Int) + d72 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d389, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5243 pattern childGuard
    simpa only [d389, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d389, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5479 pattern childGuard
    simpa only [d389, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5481 (pattern : Twelve) (guard : d1848 pattern = 1) : d374 pattern ≤ (0 : Int) + d51 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d374, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4970 pattern childGuard
    simpa only [d374, d51, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d374, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2795 pattern childGuard
    simpa only [d374, d51, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5482 (pattern : Twelve) (guard : d1848 pattern = 1) : d390 pattern ≤ (0 : Int) + d73 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d390, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5248 pattern childGuard
    simpa only [d390, d73, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d390, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5481 pattern childGuard
    simpa only [d390, d73, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5483 (pattern : Twelve) (guard : d1848 pattern = 1) : d402 pattern ≤ (0 : Int) + d91 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d402, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5480 pattern childGuard
    simpa only [d402, d91, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d402, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5482 pattern childGuard
    simpa only [d402, d91, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5484 (pattern : Twelve) (guard : d1848 pattern = 1) : d36 pattern ≤ (0 : Int) + d32 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d36, d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c240 pattern childGuard
    simpa only [d1848, d36, d32, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d36, d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5122 pattern childGuard
    simpa only [d1848, d36, d32, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5485 (pattern : Twelve) (guard : d1848 pattern = 1) : d376 pattern ≤ (0 : Int) + d53 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d376, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4979 pattern childGuard
    simpa only [d376, d53, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d376, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5484 pattern childGuard
    simpa only [d376, d53, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5486 (pattern : Twelve) (guard : d1848 pattern = 1) : d391 pattern ≤ (0 : Int) + d74 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d391, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5254 pattern childGuard
    simpa only [d391, d74, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d391, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5485 pattern childGuard
    simpa only [d391, d74, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5487 (pattern : Twelve) (guard : d1848 pattern = 1) : d378 pattern ≤ (0 : Int) + d55 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d378, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4985 pattern childGuard
    simpa only [d378, d55, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d378, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2795 pattern childGuard
    simpa only [d378, d55, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5488 (pattern : Twelve) (guard : d1848 pattern = 1) : d392 pattern ≤ (0 : Int) + d75 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d392, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5258 pattern childGuard
    simpa only [d392, d75, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d392, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5487 pattern childGuard
    simpa only [d392, d75, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5489 (pattern : Twelve) (guard : d1848 pattern = 1) : d403 pattern ≤ (0 : Int) + d92 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d403, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5486 pattern childGuard
    simpa only [d403, d92, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d403, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5488 pattern childGuard
    simpa only [d403, d92, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5490 (pattern : Twelve) (guard : d1848 pattern = 1) : d409 pattern ≤ (0 : Int) + d102 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d409, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5483 pattern childGuard
    simpa only [d409, d102, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d409, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5489 pattern childGuard
    simpa only [d409, d102, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5491 (pattern : Twelve) (guard : d1848 pattern = 1) : d376 pattern ≤ (0 : Int) + d50 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d376, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4994 pattern childGuard
    simpa only [d376, d50, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d376, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5106 pattern childGuard
    simpa only [d376, d50, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5492 (pattern : Twelve) (guard : d1848 pattern = 1) : d391 pattern ≤ (0 : Int) + d72 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d391, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5263 pattern childGuard
    simpa only [d391, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d391, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5491 pattern childGuard
    simpa only [d391, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5493 (pattern : Twelve) (guard : d1848 pattern = 1) : d392 pattern ≤ (0 : Int) + d76 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d392, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5265 pattern childGuard
    simpa only [d392, d76, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d392, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5487 pattern childGuard
    simpa only [d392, d76, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5494 (pattern : Twelve) (guard : d1848 pattern = 1) : d403 pattern ≤ (0 : Int) + d93 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d403, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5492 pattern childGuard
    simpa only [d403, d93, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d403, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5493 pattern childGuard
    simpa only [d403, d93, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5495 (pattern : Twelve) (guard : d1848 pattern = 1) : d380 pattern ≤ (0 : Int) + d57 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d380, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5006 pattern childGuard
    simpa only [d380, d57, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d380, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2752 pattern childGuard
    simpa only [d380, d57, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5496 (pattern : Twelve) (guard : d1848 pattern = 1) : d393 pattern ≤ (0 : Int) + d77 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d393, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5268 pattern childGuard
    simpa only [d393, d77, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d393, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5495 pattern childGuard
    simpa only [d393, d77, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5497 (pattern : Twelve) (guard : d1848 pattern = 1) : d394 pattern ≤ (0 : Int) + d78 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d394, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5271 pattern childGuard
    simpa only [d394, d78, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d394, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5487 pattern childGuard
    simpa only [d394, d78, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5498 (pattern : Twelve) (guard : d1848 pattern = 1) : d404 pattern ≤ (0 : Int) + d94 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d404, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5496 pattern childGuard
    simpa only [d404, d94, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d404, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5497 pattern childGuard
    simpa only [d404, d94, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5499 (pattern : Twelve) (guard : d1848 pattern = 1) : d410 pattern ≤ (0 : Int) + d103 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d410, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5494 pattern childGuard
    simpa only [d410, d103, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d410, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5498 pattern childGuard
    simpa only [d410, d103, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5500 (pattern : Twelve) (guard : d1848 pattern = 1) : d415 pattern ≤ (0 : Int) + d110 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d415, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5490 pattern childGuard
    simpa only [d415, d110, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d415, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5499 pattern childGuard
    simpa only [d415, d110, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5501 (pattern : Twelve) (guard : d1848 pattern = 1) : d36 pattern ≤ (0 : Int) + d37 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d36, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c240 pattern childGuard
    simpa only [d1848, d36, d37, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d36, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5328 pattern childGuard
    simpa only [d1848, d36, d37, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5502 (pattern : Twelve) (guard : d1848 pattern = 1) : d382 pattern ≤ (0 : Int) + d58 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d382, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5019 pattern childGuard
    simpa only [d382, d58, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d382, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5501 pattern childGuard
    simpa only [d382, d58, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5503 (pattern : Twelve) (guard : d1848 pattern = 1) : d395 pattern ≤ (0 : Int) + d79 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d395, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5277 pattern childGuard
    simpa only [d395, d79, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d395, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5502 pattern childGuard
    simpa only [d395, d79, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5504 (pattern : Twelve) (guard : d1848 pattern = 1) : d396 pattern ≤ (0 : Int) + d80 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d396, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5280 pattern childGuard
    simpa only [d396, d80, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d396, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5487 pattern childGuard
    simpa only [d396, d80, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5505 (pattern : Twelve) (guard : d1848 pattern = 1) : d405 pattern ≤ (0 : Int) + d95 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d405, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5503 pattern childGuard
    simpa only [d405, d95, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d405, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5504 pattern childGuard
    simpa only [d405, d95, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5506 (pattern : Twelve) (guard : d1848 pattern = 1) : d384 pattern ≤ (0 : Int) + d60 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d384, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5028 pattern childGuard
    simpa only [d384, d60, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d384, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2768 pattern childGuard
    simpa only [d384, d60, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5507 (pattern : Twelve) (guard : d1848 pattern = 1) : d397 pattern ≤ (0 : Int) + d81 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d397, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5284 pattern childGuard
    simpa only [d397, d81, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d397, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5506 pattern childGuard
    simpa only [d397, d81, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5508 (pattern : Twelve) (guard : d1848 pattern = 1) : d385 pattern ≤ (0 : Int) + d61 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d385, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5034 pattern childGuard
    simpa only [d385, d61, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d385, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2806 pattern childGuard
    simpa only [d385, d61, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5509 (pattern : Twelve) (guard : d1848 pattern = 1) : d398 pattern ≤ (0 : Int) + d82 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d398, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5284 pattern childGuard
    simpa only [d398, d82, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d398, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5508 pattern childGuard
    simpa only [d398, d82, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5510 (pattern : Twelve) (guard : d1848 pattern = 1) : d406 pattern ≤ (0 : Int) + d96 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d406, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5507 pattern childGuard
    simpa only [d406, d96, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d406, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5509 pattern childGuard
    simpa only [d406, d96, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5511 (pattern : Twelve) (guard : d1848 pattern = 1) : d411 pattern ≤ (0 : Int) + d104 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d411, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5505 pattern childGuard
    simpa only [d411, d104, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d411, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5510 pattern childGuard
    simpa only [d411, d104, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5512 (pattern : Twelve) (guard : d1848 pattern = 1) : d399 pattern ≤ (0 : Int) + d77 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d399, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5271 pattern childGuard
    simpa only [d399, d77, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d399, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5495 pattern childGuard
    simpa only [d399, d77, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5513 (pattern : Twelve) (guard : d1848 pattern = 1) : d407 pattern ≤ (0 : Int) + d94 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d407, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5512 pattern childGuard
    simpa only [d407, d94, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d407, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5497 pattern childGuard
    simpa only [d407, d94, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5514 (pattern : Twelve) (guard : d1848 pattern = 1) : d412 pattern ≤ (0 : Int) + d105 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d412, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5513 pattern childGuard
    simpa only [d412, d105, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d412, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4269 pattern childGuard
    simpa only [d412, d105, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5515 (pattern : Twelve) (guard : d1848 pattern = 1) : d416 pattern ≤ (0 : Int) + d111 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d416, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5511 pattern childGuard
    simpa only [d416, d111, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d416, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5514 pattern childGuard
    simpa only [d416, d111, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5516 (pattern : Twelve) (guard : d1848 pattern = 1) : d419 pattern ≤ (0 : Int) + d114 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d419, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5500 pattern childGuard
    simpa only [d419, d114, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d419, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5515 pattern childGuard
    simpa only [d419, d114, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5517 (pattern : Twelve) (guard : d1848 pattern = 1) : d380 pattern ≤ (0 : Int) + d50 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d380, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5048 pattern childGuard
    simpa only [d380, d50, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d380, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5106 pattern childGuard
    simpa only [d380, d50, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5518 (pattern : Twelve) (guard : d1848 pattern = 1) : d399 pattern ≤ (0 : Int) + d72 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d399, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5045 pattern childGuard
    simpa only [d399, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d399, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5517 pattern childGuard
    simpa only [d399, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5519 (pattern : Twelve) (guard : d1848 pattern = 1) : d378 pattern ≤ (0 : Int) + d51 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d378, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5063 pattern childGuard
    simpa only [d378, d51, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d378, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2795 pattern childGuard
    simpa only [d378, d51, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5520 (pattern : Twelve) (guard : d1848 pattern = 1) : d394 pattern ≤ (0 : Int) + d73 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d394, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5045 pattern childGuard
    simpa only [d394, d73, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d394, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5519 pattern childGuard
    simpa only [d394, d73, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5521 (pattern : Twelve) (guard : d1848 pattern = 1) : d407 pattern ≤ (0 : Int) + d91 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d407, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5518 pattern childGuard
    simpa only [d407, d91, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d407, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5520 pattern childGuard
    simpa only [d407, d91, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5522 (pattern : Twelve) (guard : d1848 pattern = 1) : d380 pattern ≤ (0 : Int) + d53 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d380, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5006 pattern childGuard
    simpa only [d380, d53, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d380, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5484 pattern childGuard
    simpa only [d380, d53, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5523 (pattern : Twelve) (guard : d1848 pattern = 1) : d399 pattern ≤ (0 : Int) + d74 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d399, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5303 pattern childGuard
    simpa only [d399, d74, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d399, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5522 pattern childGuard
    simpa only [d399, d74, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5524 (pattern : Twelve) (guard : d1848 pattern = 1) : d394 pattern ≤ (0 : Int) + d75 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d394, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5305 pattern childGuard
    simpa only [d394, d75, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d394, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5487 pattern childGuard
    simpa only [d394, d75, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5525 (pattern : Twelve) (guard : d1848 pattern = 1) : d407 pattern ≤ (0 : Int) + d92 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d407, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5523 pattern childGuard
    simpa only [d407, d92, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d407, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5524 pattern childGuard
    simpa only [d407, d92, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5526 (pattern : Twelve) (guard : d1848 pattern = 1) : d407 pattern ≤ (0 : Int) + d102 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5521 pattern childGuard
    simpa only [d102, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5525 pattern childGuard
    simpa only [d102, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5527 (pattern : Twelve) (guard : d1848 pattern = 1) : d394 pattern ≤ (0 : Int) + d76 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d394, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5045 pattern childGuard
    simpa only [d394, d76, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d394, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5487 pattern childGuard
    simpa only [d394, d76, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5528 (pattern : Twelve) (guard : d1848 pattern = 1) : d407 pattern ≤ (0 : Int) + d93 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d407, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5518 pattern childGuard
    simpa only [d407, d93, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d407, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5527 pattern childGuard
    simpa only [d407, d93, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5529 (pattern : Twelve) (guard : d1848 pattern = 1) : d407 pattern ≤ (0 : Int) + d103 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5528 pattern childGuard
    simpa only [d103, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5513 pattern childGuard
    simpa only [d103, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5530 (pattern : Twelve) (guard : d1848 pattern = 1) : d407 pattern ≤ (0 : Int) + d110 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5526 pattern childGuard
    simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5529 pattern childGuard
    simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5531 (pattern : Twelve) (guard : d1848 pattern = 1) : d380 pattern ≤ (0 : Int) + d58 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d380, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5006 pattern childGuard
    simpa only [d380, d58, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d380, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5501 pattern childGuard
    simpa only [d380, d58, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5532 (pattern : Twelve) (guard : d1848 pattern = 1) : d399 pattern ≤ (0 : Int) + d79 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d399, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5006 pattern childGuard
    simpa only [d399, d79, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d399, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5531 pattern childGuard
    simpa only [d399, d79, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5533 (pattern : Twelve) (guard : d1848 pattern = 1) : d394 pattern ≤ (0 : Int) + d80 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d394, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5006 pattern childGuard
    simpa only [d394, d80, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d394, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5487 pattern childGuard
    simpa only [d394, d80, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5534 (pattern : Twelve) (guard : d1848 pattern = 1) : d407 pattern ≤ (0 : Int) + d95 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d407, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5532 pattern childGuard
    simpa only [d407, d95, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d407, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5533 pattern childGuard
    simpa only [d407, d95, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5535 (pattern : Twelve) (guard : d1848 pattern = 1) : d413 pattern ≤ (0 : Int) + d104 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d413, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5534 pattern childGuard
    simpa only [d413, d104, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d413, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5510 pattern childGuard
    simpa only [d413, d104, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5536 (pattern : Twelve) (guard : d1848 pattern = 1) : d417 pattern ≤ (0 : Int) + d111 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d417, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5535 pattern childGuard
    simpa only [d417, d111, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d417, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5514 pattern childGuard
    simpa only [d417, d111, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5537 (pattern : Twelve) (guard : d1848 pattern = 1) : d420 pattern ≤ (0 : Int) + d114 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d420, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5530 pattern childGuard
    simpa only [d420, d114, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d420, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5536 pattern childGuard
    simpa only [d420, d114, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5538 (pattern : Twelve) (guard : d1848 pattern = 1) : d422 pattern ≤ (0 : Int) + d114 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5516 pattern childGuard
    simpa only [d422, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5537 pattern childGuard
    simpa only [d422, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5539 (pattern : Twelve) (guard : d1848 pattern = 1) : d423 pattern ≤ (0 : Int) + d114 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5538 pattern childGuard
    simpa only [d423, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5537 pattern childGuard
    simpa only [d423, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5540 (pattern : Twelve) (guard : d1848 pattern = 1) : d36 pattern ≤ (0 : Int) + d120 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d36, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c240 pattern childGuard
    simpa only [d1848, d36, d120, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d36, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1105 pattern childGuard
    simpa only [d1848, d36, d120, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5541 (pattern : Twelve) (guard : d1848 pattern = 1) : d378 pattern ≤ (0 : Int) + d129 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d378, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5540 pattern childGuard
    simpa only [d378, d129, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d378, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2795 pattern childGuard
    simpa only [d378, d129, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5542 (pattern : Twelve) (guard : d1848 pattern = 1) : d394 pattern ≤ (0 : Int) + d136 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d394, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5045 pattern childGuard
    simpa only [d394, d136, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d394, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5541 pattern childGuard
    simpa only [d394, d136, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5543 (pattern : Twelve) (guard : d1848 pattern = 1) : d407 pattern ≤ (0 : Int) + d144 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d407, d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5518 pattern childGuard
    simpa only [d407, d144, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d407, d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5542 pattern childGuard
    simpa only [d407, d144, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5544 (pattern : Twelve) (guard : d1848 pattern = 1) : d35 pattern ≤ (0 : Int) + d121 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d35, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1848, d35, d121, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d35, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4984 pattern childGuard
    simpa only [d1848, d35, d121, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5545 (pattern : Twelve) (guard : d1848 pattern = 1) : d380 pattern ≤ (0 : Int) + d130 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d380, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5544 pattern childGuard
    simpa only [d380, d130, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d380, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2752 pattern childGuard
    simpa only [d380, d130, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5546 (pattern : Twelve) (guard : d1848 pattern = 1) : d399 pattern ≤ (0 : Int) + d137 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d399, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5303 pattern childGuard
    simpa only [d399, d137, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d399, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5545 pattern childGuard
    simpa only [d399, d137, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5547 (pattern : Twelve) (guard : d1848 pattern = 1) : d394 pattern ≤ (0 : Int) + d138 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d394, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5271 pattern childGuard
    simpa only [d394, d138, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d394, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5541 pattern childGuard
    simpa only [d394, d138, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5548 (pattern : Twelve) (guard : d1848 pattern = 1) : d407 pattern ≤ (0 : Int) + d145 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d407, d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5546 pattern childGuard
    simpa only [d407, d145, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d407, d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5547 pattern childGuard
    simpa only [d407, d145, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5549 (pattern : Twelve) (guard : d1848 pattern = 1) : d407 pattern ≤ (0 : Int) + d149 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5543 pattern childGuard
    simpa only [d149, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5548 pattern childGuard
    simpa only [d149, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5550 (pattern : Twelve) (guard : d1848 pattern = 1) : d399 pattern ≤ (0 : Int) + d139 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d399, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5271 pattern childGuard
    simpa only [d399, d139, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d399, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5545 pattern childGuard
    simpa only [d399, d139, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5551 (pattern : Twelve) (guard : d1848 pattern = 1) : d407 pattern ≤ (0 : Int) + d146 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d407, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5550 pattern childGuard
    simpa only [d407, d146, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d407, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5547 pattern childGuard
    simpa only [d407, d146, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5552 (pattern : Twelve) (guard : d1848 pattern = 1) : d407 pattern ≤ (0 : Int) + d150 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5543 pattern childGuard
    simpa only [d150, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5551 pattern childGuard
    simpa only [d150, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5553 (pattern : Twelve) (guard : d1848 pattern = 1) : d407 pattern ≤ (0 : Int) + d153 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5549 pattern childGuard
    simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5552 pattern childGuard
    simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5554 (pattern : Twelve) (guard : d1848 pattern = 1) : d36 pattern ≤ (0 : Int) + d122 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d36, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c240 pattern childGuard
    simpa only [d1848, d36, d122, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d36, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5027 pattern childGuard
    simpa only [d1848, d36, d122, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5555 (pattern : Twelve) (guard : d1848 pattern = 1) : d380 pattern ≤ (0 : Int) + d131 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d380, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5544 pattern childGuard
    simpa only [d380, d131, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d380, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5554 pattern childGuard
    simpa only [d380, d131, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5556 (pattern : Twelve) (guard : d1848 pattern = 1) : d399 pattern ≤ (0 : Int) + d140 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d399, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5006 pattern childGuard
    simpa only [d399, d140, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d399, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5555 pattern childGuard
    simpa only [d399, d140, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5557 (pattern : Twelve) (guard : d1848 pattern = 1) : d394 pattern ≤ (0 : Int) + d141 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d394, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5330 pattern childGuard
    simpa only [d394, d141, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d394, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5541 pattern childGuard
    simpa only [d394, d141, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5558 (pattern : Twelve) (guard : d1848 pattern = 1) : d407 pattern ≤ (0 : Int) + d147 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d407, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5556 pattern childGuard
    simpa only [d407, d147, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d407, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5557 pattern childGuard
    simpa only [d407, d147, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5559 (pattern : Twelve) (guard : d1848 pattern = 1) : d39 pattern ≤ (0 : Int) + d124 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d39, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1333 pattern childGuard
    simpa only [d1848, d39, d124, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d39, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5399 pattern childGuard
    simpa only [d1848, d39, d124, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5560 (pattern : Twelve) (guard : d1848 pattern = 1) : d386 pattern ≤ (0 : Int) + d133 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d386, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5559 pattern childGuard
    simpa only [d386, d133, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d386, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5401 pattern childGuard
    simpa only [d386, d133, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5561 (pattern : Twelve) (guard : d1848 pattern = 1) : d400 pattern ≤ (0 : Int) + d142 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d400, d142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5284 pattern childGuard
    simpa only [d400, d142, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d400, d142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5560 pattern childGuard
    simpa only [d400, d142, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5562 (pattern : Twelve) (guard : d1848 pattern = 1) : d40 pattern ≤ (0 : Int) + d127 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d40, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1340 pattern childGuard
    simpa only [d1848, d40, d127, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d40, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5224 pattern childGuard
    simpa only [d1848, d40, d127, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5563 (pattern : Twelve) (guard : d1848 pattern = 1) : d388 pattern ≤ (0 : Int) + d135 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d388, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5562 pattern childGuard
    simpa only [d388, d135, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d388, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5446 pattern childGuard
    simpa only [d388, d135, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5564 (pattern : Twelve) (guard : d1848 pattern = 1) : d401 pattern ≤ (0 : Int) + d143 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d401, d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5338 pattern childGuard
    simpa only [d401, d143, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d401, d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5563 pattern childGuard
    simpa only [d401, d143, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5565 (pattern : Twelve) (guard : d1848 pattern = 1) : d408 pattern ≤ (0 : Int) + d148 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d408, d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5561 pattern childGuard
    simpa only [d408, d148, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d408, d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5564 pattern childGuard
    simpa only [d408, d148, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5566 (pattern : Twelve) (guard : d1848 pattern = 1) : d414 pattern ≤ (0 : Int) + d151 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d414, d151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5558 pattern childGuard
    simpa only [d414, d151, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d414, d151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5565 pattern childGuard
    simpa only [d414, d151, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5567 (pattern : Twelve) (guard : d1848 pattern = 1) : d412 pattern ≤ (0 : Int) + d152 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d412, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5551 pattern childGuard
    simpa only [d412, d152, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d412, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4269 pattern childGuard
    simpa only [d412, d152, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5568 (pattern : Twelve) (guard : d1848 pattern = 1) : d418 pattern ≤ (0 : Int) + d154 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d418, d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5566 pattern childGuard
    simpa only [d418, d154, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d418, d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5567 pattern childGuard
    simpa only [d418, d154, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5569 (pattern : Twelve) (guard : d1848 pattern = 1) : d421 pattern ≤ (0 : Int) + d155 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d421, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5553 pattern childGuard
    simpa only [d421, d155, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d421, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5568 pattern childGuard
    simpa only [d421, d155, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5570 (pattern : Twelve) (guard : d1848 pattern = 1) : d424 pattern ≤ (0 : Int) + d156 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d424, d156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5539 pattern childGuard
    simpa only [d424, d156, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d424, d156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5569 pattern childGuard
    simpa only [d424, d156, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5571 (pattern : Twelve) (guard : d1848 pattern = 1) : d818 pattern ≤ (0 : Int) + d816 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d818, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4215 pattern childGuard
    simpa only [d1848, d818, d816, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d818, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5047 pattern childGuard
    simpa only [d1848, d818, d816, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5572 (pattern : Twelve) (guard : d1848 pattern = 1) : d1030 pattern ≤ (0 : Int) + d824 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1030, d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5088 pattern childGuard
    simpa only [d1030, d824, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1030, d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5571 pattern childGuard
    simpa only [d1030, d824, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5573 (pattern : Twelve) (guard : d1848 pattern = 1) : d1038 pattern ≤ (0 : Int) + d838 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1038, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5248 pattern childGuard
    simpa only [d1038, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1038, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5572 pattern childGuard
    simpa only [d1038, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5574 (pattern : Twelve) (guard : d1848 pattern = 1) : d1032 pattern ≤ (0 : Int) + d825 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1032, d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5096 pattern childGuard
    simpa only [d1032, d825, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1032, d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2806 pattern childGuard
    simpa only [d1032, d825, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5575 (pattern : Twelve) (guard : d1848 pattern = 1) : d1039 pattern ≤ (0 : Int) + d839 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1039, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5348 pattern childGuard
    simpa only [d1039, d839, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1039, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5574 pattern childGuard
    simpa only [d1039, d839, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5576 (pattern : Twelve) (guard : d1848 pattern = 1) : d1048 pattern ≤ (0 : Int) + d853 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1048, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5573 pattern childGuard
    simpa only [d1048, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1048, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5575 pattern childGuard
    simpa only [d1048, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5577 (pattern : Twelve) (guard : d1848 pattern = 1) : d818 pattern ≤ (0 : Int) + d818 pattern := by
  omega
theorem c5578 (pattern : Twelve) (guard : d1848 pattern = 1) : d1033 pattern ≤ (0 : Int) + d826 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1033, d826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4985 pattern childGuard
    simpa only [d1033, d826, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1033, d826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5577 pattern childGuard
    simpa only [d1033, d826, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5579 (pattern : Twelve) (guard : d1848 pattern = 1) : d1040 pattern ≤ (0 : Int) + d840 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1040, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5352 pattern childGuard
    simpa only [d1040, d840, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1040, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5578 pattern childGuard
    simpa only [d1040, d840, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5580 (pattern : Twelve) (guard : d1848 pattern = 1) : d1041 pattern ≤ (0 : Int) + d841 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1041, d841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5355 pattern childGuard
    simpa only [d1041, d841, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1041, d841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5574 pattern childGuard
    simpa only [d1041, d841, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5581 (pattern : Twelve) (guard : d1848 pattern = 1) : d1049 pattern ≤ (0 : Int) + d854 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1049, d854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5579 pattern childGuard
    simpa only [d1049, d854, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1049, d854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5580 pattern childGuard
    simpa only [d1049, d854, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5582 (pattern : Twelve) (guard : d1848 pattern = 1) : d1054 pattern ≤ (0 : Int) + d861 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1054, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5576 pattern childGuard
    simpa only [d1054, d861, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1054, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5581 pattern childGuard
    simpa only [d1054, d861, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5583 (pattern : Twelve) (guard : d1848 pattern = 1) : d1033 pattern ≤ (0 : Int) + d824 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1033, d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5106 pattern childGuard
    simpa only [d1033, d824, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1033, d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5571 pattern childGuard
    simpa only [d1033, d824, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5584 (pattern : Twelve) (guard : d1848 pattern = 1) : d1040 pattern ≤ (0 : Int) + d838 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1040, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5265 pattern childGuard
    simpa only [d1040, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1040, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5583 pattern childGuard
    simpa only [d1040, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5585 (pattern : Twelve) (guard : d1848 pattern = 1) : d1041 pattern ≤ (0 : Int) + d839 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1041, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5109 pattern childGuard
    simpa only [d1041, d839, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1041, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5574 pattern childGuard
    simpa only [d1041, d839, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5586 (pattern : Twelve) (guard : d1848 pattern = 1) : d1049 pattern ≤ (0 : Int) + d853 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1049, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5584 pattern childGuard
    simpa only [d1049, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1049, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5585 pattern childGuard
    simpa only [d1049, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5587 (pattern : Twelve) (guard : d1848 pattern = 1) : d1042 pattern ≤ (0 : Int) + d840 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1042, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5271 pattern childGuard
    simpa only [d1042, d840, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1042, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5578 pattern childGuard
    simpa only [d1042, d840, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5588 (pattern : Twelve) (guard : d1848 pattern = 1) : d1050 pattern ≤ (0 : Int) + d854 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1050, d854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5587 pattern childGuard
    simpa only [d1050, d854, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1050, d854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5580 pattern childGuard
    simpa only [d1050, d854, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5589 (pattern : Twelve) (guard : d1848 pattern = 1) : d1055 pattern ≤ (0 : Int) + d861 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1055, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5586 pattern childGuard
    simpa only [d1055, d861, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1055, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5588 pattern childGuard
    simpa only [d1055, d861, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5590 (pattern : Twelve) (guard : d1848 pattern = 1) : d1060 pattern ≤ (0 : Int) + d861 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5582 pattern childGuard
    simpa only [d1060, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5589 pattern childGuard
    simpa only [d1060, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5591 (pattern : Twelve) (guard : d1848 pattern = 1) : d818 pattern ≤ (0 : Int) + d819 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d818, d819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4215 pattern childGuard
    simpa only [d1848, d818, d819, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d818, d819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5328 pattern childGuard
    simpa only [d1848, d818, d819, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5592 (pattern : Twelve) (guard : d1848 pattern = 1) : d1033 pattern ≤ (0 : Int) + d828 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1033, d828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4985 pattern childGuard
    simpa only [d1033, d828, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1033, d828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5591 pattern childGuard
    simpa only [d1033, d828, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5593 (pattern : Twelve) (guard : d1848 pattern = 1) : d1043 pattern ≤ (0 : Int) + d842 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1043, d842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5280 pattern childGuard
    simpa only [d1043, d842, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1043, d842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5592 pattern childGuard
    simpa only [d1043, d842, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5594 (pattern : Twelve) (guard : d1848 pattern = 1) : d1041 pattern ≤ (0 : Int) + d843 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1041, d843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4985 pattern childGuard
    simpa only [d1041, d843, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1041, d843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5574 pattern childGuard
    simpa only [d1041, d843, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5595 (pattern : Twelve) (guard : d1848 pattern = 1) : d1051 pattern ≤ (0 : Int) + d855 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1051, d855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5593 pattern childGuard
    simpa only [d1051, d855, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1051, d855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5594 pattern childGuard
    simpa only [d1051, d855, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5596 (pattern : Twelve) (guard : d1848 pattern = 1) : d820 pattern ≤ (0 : Int) + d820 pattern := by
  omega
theorem c5597 (pattern : Twelve) (guard : d1848 pattern = 1) : d1034 pattern ≤ (0 : Int) + d829 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1034, d829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5034 pattern childGuard
    simpa only [d1034, d829, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1034, d829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5596 pattern childGuard
    simpa only [d1034, d829, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5598 (pattern : Twelve) (guard : d1848 pattern = 1) : d1044 pattern ≤ (0 : Int) + d844 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1044, d844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5284 pattern childGuard
    simpa only [d1044, d844, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1044, d844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5597 pattern childGuard
    simpa only [d1044, d844, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5599 (pattern : Twelve) (guard : d1848 pattern = 1) : d1035 pattern ≤ (0 : Int) + d831 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1035, d831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5123 pattern childGuard
    simpa only [d1035, d831, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1035, d831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1541 pattern childGuard
    simpa only [d1035, d831, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
