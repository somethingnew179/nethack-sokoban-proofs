/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons107
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c15120 (pattern : Twelve) (guard : d26 pattern = 1) : d19 pattern ≤ (0 : Int) + d19 pattern := by
  omega
theorem c15121 (pattern : Twelve) (guard : d2355 pattern = 1) : d1294 pattern ≤ (0 : Int) + d1649 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2355, d1294, d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15120 pattern childGuard
    simpa only [d2355, d1294, d1649, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2355, d1294, d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1102 pattern childGuard
    simpa only [d2355, d1294, d1649, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15122 (pattern : Twelve) (guard : d2355 pattern = 1) : d1650 pattern ≤ (0 : Int) + d1650 pattern := by
  omega
theorem c15123 (pattern : Twelve) (guard : d2355 pattern = 1) : d1730 pattern ≤ (0 : Int) + d1656 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2355 pattern = 1 := by simpa only [d1730, d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15121 pattern childGuard
    simpa only [d1730, d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2355 pattern = 1 := by simpa only [d1730, d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15122 pattern childGuard
    simpa only [d1730, d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15124 (pattern : Twelve) (guard : d0 pattern = 1) : d1731 pattern ≤ (0 : Int) + d1656 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15125 (pattern : Twelve) (guard : d2356 pattern = 1) : d1736 pattern ≤ (0 : Int) + d1656 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2355 pattern = 1 := by simpa only [d2356, d1736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15123 pattern childGuard
    simpa only [d2356, d1736, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2356, d1736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15124 pattern childGuard
    simpa only [d2356, d1736, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15126 (pattern : Twelve) (guard : d2355 pattern = 1) : d1298 pattern ≤ (0 : Int) + d1814 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2355, d1298, d1814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15090 pattern childGuard
    simpa only [d2355, d1298, d1814, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2355, d1298, d1814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5218 pattern childGuard
    simpa only [d2355, d1298, d1814, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15127 (pattern : Twelve) (guard : d26 pattern = 1) : d821 pattern ≤ (0 : Int) + d21 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d26, d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4576 pattern childGuard
    simpa only [d26, d821, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d26, d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11589 pattern childGuard
    simpa only [d26, d821, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15128 (pattern : Twelve) (guard : d2355 pattern = 1) : d1653 pattern ≤ (0 : Int) + d1815 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2355, d1653, d1815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15127 pattern childGuard
    simpa only [d2355, d1653, d1815, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2355, d1653, d1815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d2355, d1653, d1815, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15129 (pattern : Twelve) (guard : d2355 pattern = 1) : d1732 pattern ≤ (0 : Int) + d1818 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2355 pattern = 1 := by simpa only [d1732, d1818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15126 pattern childGuard
    simpa only [d1732, d1818, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2355 pattern = 1 := by simpa only [d1732, d1818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15128 pattern childGuard
    simpa only [d1732, d1818, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15130 (pattern : Twelve) (guard : d0 pattern = 1) : d1733 pattern ≤ (0 : Int) + d1818 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15131 (pattern : Twelve) (guard : d2356 pattern = 1) : d1737 pattern ≤ (0 : Int) + d1818 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2355 pattern = 1 := by simpa only [d2356, d1737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15129 pattern childGuard
    simpa only [d2356, d1737, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2356, d1737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15130 pattern childGuard
    simpa only [d2356, d1737, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15132 (pattern : Twelve) (guard : d26 pattern = 1) : d821 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d26, d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c393 pattern childGuard
    simpa only [d26, d821, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d26, d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11039 pattern childGuard
    simpa only [d26, d821, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15133 (pattern : Twelve) (guard : d26 pattern = 1) : d42 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d26, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c393 pattern childGuard
    simpa only [d26, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d26, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10876 pattern childGuard
    simpa only [d26, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15134 (pattern : Twelve) (guard : d26 pattern = 1) : d1289 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15132 pattern childGuard
    simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d26 pattern = 1 := by simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15133 pattern childGuard
    simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15135 (pattern : Twelve) (guard : d2355 pattern = 1) : d1300 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2355, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15134 pattern childGuard
    simpa only [d2355, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2355, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d2355, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15136 (pattern : Twelve) (guard : d2355 pattern = 1) : d1731 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2355 pattern = 1 := by simpa only [d1731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15101 pattern childGuard
    simpa only [d1731, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2355 pattern = 1 := by simpa only [d1731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15135 pattern childGuard
    simpa only [d1731, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15137 (pattern : Twelve) (guard : d2356 pattern = 1) : d1738 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2355 pattern = 1 := by simpa only [d2356, d1738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15136 pattern childGuard
    simpa only [d2356, d1738, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2356, d1738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d2356, d1738, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15138 (pattern : Twelve) (guard : d2356 pattern = 1) : d1740 pattern ≤ (0 : Int) + d2491 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d2356 pattern = 1 := by simpa only [d1740, d2491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15131 pattern childGuard
    simpa only [d1740, d2491, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2356 pattern = 1 := by simpa only [d1740, d2491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15137 pattern childGuard
    simpa only [d1740, d2491, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15139 (pattern : Twelve) (guard : d2356 pattern = 1) : d1742 pattern ≤ (0 : Int) + d2492 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d2356 pattern = 1 := by simpa only [d1742, d2492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15125 pattern childGuard
    simpa only [d1742, d2492, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2356 pattern = 1 := by simpa only [d1742, d2492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15138 pattern childGuard
    simpa only [d1742, d2492, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15140 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d2410 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15141 (pattern : Twelve) (guard : d2355 pattern = 1) : d1298 pattern ≤ (0 : Int) + d2468 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2355, d1298, d2468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15090 pattern childGuard
    simpa only [d2355, d1298, d2468, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2355, d1298, d2468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15140 pattern childGuard
    simpa only [d2355, d1298, d2468, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15142 (pattern : Twelve) (guard : d26 pattern = 1) : d1289 pattern ≤ (0 : Int) + d2469 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d1289, d2469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15127 pattern childGuard
    simpa only [d1289, d2469, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d26 pattern = 1 := by simpa only [d1289, d2469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15133 pattern childGuard
    simpa only [d1289, d2469, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15143 (pattern : Twelve) (guard : d2355 pattern = 1) : d1300 pattern ≤ (0 : Int) + d2470 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2355, d1300, d2470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15142 pattern childGuard
    simpa only [d2355, d1300, d2470, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2355, d1300, d2470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d2355, d1300, d2470, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15144 (pattern : Twelve) (guard : d2355 pattern = 1) : d1734 pattern ≤ (0 : Int) + d2471 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2355 pattern = 1 := by simpa only [d1734, d2471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15141 pattern childGuard
    simpa only [d1734, d2471, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2355 pattern = 1 := by simpa only [d1734, d2471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15143 pattern childGuard
    simpa only [d1734, d2471, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15145 (pattern : Twelve) (guard : d0 pattern = 1) : d1735 pattern ≤ (0 : Int) + d2471 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15146 (pattern : Twelve) (guard : d2356 pattern = 1) : d1739 pattern ≤ (0 : Int) + d2471 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2355 pattern = 1 := by simpa only [d2356, d1739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15144 pattern childGuard
    simpa only [d2356, d1739, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2356, d1739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15145 pattern childGuard
    simpa only [d2356, d1739, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15147 (pattern : Twelve) (guard : d2356 pattern = 1) : d1741 pattern ≤ (0 : Int) + d2493 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d2356 pattern = 1 := by simpa only [d1741, d2493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15146 pattern childGuard
    simpa only [d1741, d2493, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2356 pattern = 1 := by simpa only [d1741, d2493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15137 pattern childGuard
    simpa only [d1741, d2493, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15148 (pattern : Twelve) (guard : d2356 pattern = 1) : d1743 pattern ≤ (0 : Int) + d2494 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d2356 pattern = 1 := by simpa only [d1743, d2494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15125 pattern childGuard
    simpa only [d1743, d2494, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2356 pattern = 1 := by simpa only [d1743, d2494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15147 pattern childGuard
    simpa only [d1743, d2494, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15149 (pattern : Twelve) (guard : d2356 pattern = 1) : d1744 pattern ≤ (0 : Int) + d2495 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d2356 pattern = 1 := by simpa only [d1744, d2495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15139 pattern childGuard
    simpa only [d1744, d2495, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2356 pattern = 1 := by simpa only [d1744, d2495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15148 pattern childGuard
    simpa only [d1744, d2495, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15150 (pattern : Twelve) (guard : d0 pattern = 1) : d0 pattern ≤ (1 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15151 (pattern : Twelve) (guard : d1 pattern = 1) : d1 pattern ≤ (1 : Int) + d0 pattern := by
  change (1 : Int) ≤ (1 : Int) + 0
  decide
theorem c15152 (pattern : Twelve) (guard : d1 pattern = 1) : d26 pattern ≤ (1 : Int) + d0 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11049 pattern childGuard
    simpa only [d26, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15151 pattern childGuard
    simpa only [d26, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15153 (pattern : Twelve) (guard : d1 pattern = 1) : d7 pattern ≤ (1 : Int) + d0 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11049 pattern childGuard
    simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15151 pattern childGuard
    simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15154 (pattern : Twelve) (guard : d1 pattern = 1) : d17 pattern ≤ (1 : Int) + d0 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11049 pattern childGuard
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15153 pattern childGuard
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15155 (pattern : Twelve) (guard : d1 pattern = 1) : d27 pattern ≤ (1 : Int) + d0 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15154 pattern childGuard
    simpa only [d27, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15151 pattern childGuard
    simpa only [d27, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15156 (pattern : Twelve) (guard : d1 pattern = 1) : d50 pattern ≤ (1 : Int) + d0 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15152 pattern childGuard
    simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15155 pattern childGuard
    simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15157 (pattern : Twelve) (guard : d1859 pattern = 1) : d72 pattern ≤ (1 : Int) + d0 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1859, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15150 pattern childGuard
    simpa only [d1859, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1859, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15156 pattern childGuard
    simpa only [d1859, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15158 (pattern : Twelve) (guard : d0 pattern = 1) : d73 pattern ≤ (1 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15159 (pattern : Twelve) (guard : d2496 pattern = 1) : d91 pattern ≤ (1 : Int) + d0 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1859 pattern = 1 := by simpa only [d2496, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15157 pattern childGuard
    simpa only [d2496, d91, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2496, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15158 pattern childGuard
    simpa only [d2496, d91, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15160 (pattern : Twelve) (guard : d0 pattern = 1) : d52 pattern ≤ (1 : Int) + d54 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15161 (pattern : Twelve) (guard : d1 pattern = 1) : d21 pattern ≤ (1 : Int) + d22 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d21, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11393 pattern childGuard
    simpa only [d21, d22, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d21, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11284 pattern childGuard
    simpa only [d21, d22, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15162 (pattern : Twelve) (guard : d1 pattern = 1) : d32 pattern ≤ (1 : Int) + d33 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d32, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15154 pattern childGuard
    simpa only [d32, d33, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d32, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15161 pattern childGuard
    simpa only [d32, d33, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15163 (pattern : Twelve) (guard : d1 pattern = 1) : d53 pattern ≤ (1 : Int) + d54 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d53, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11732 pattern childGuard
    simpa only [d53, d54, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d53, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15162 pattern childGuard
    simpa only [d53, d54, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15164 (pattern : Twelve) (guard : d1859 pattern = 1) : d74 pattern ≤ (1 : Int) + d54 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1859, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15160 pattern childGuard
    simpa only [d1859, d74, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1859, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15163 pattern childGuard
    simpa only [d1859, d74, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15165 (pattern : Twelve) (guard : d0 pattern = 1) : d75 pattern ≤ (1 : Int) + d54 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15166 (pattern : Twelve) (guard : d2496 pattern = 1) : d92 pattern ≤ (1 : Int) + d54 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1859 pattern = 1 := by simpa only [d2496, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15164 pattern childGuard
    simpa only [d2496, d92, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2496, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15165 pattern childGuard
    simpa only [d2496, d92, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15167 (pattern : Twelve) (guard : d2496 pattern = 1) : d102 pattern ≤ (1 : Int) + d2497 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d102, d2497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15159 pattern childGuard
    simpa only [d102, d2497, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d102, d2497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15166 pattern childGuard
    simpa only [d102, d2497, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15168 (pattern : Twelve) (guard : d0 pattern = 1) : d76 pattern ≤ (1 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15169 (pattern : Twelve) (guard : d2496 pattern = 1) : d93 pattern ≤ (1 : Int) + d0 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1859 pattern = 1 := by simpa only [d2496, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15157 pattern childGuard
    simpa only [d2496, d93, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2496, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15168 pattern childGuard
    simpa only [d2496, d93, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15170 (pattern : Twelve) (guard : d0 pattern = 1) : d56 pattern ≤ (1 : Int) + d56 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15171 (pattern : Twelve) (guard : d1 pattern = 1) : d36 pattern ≤ (1 : Int) + d35 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d36, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15154 pattern childGuard
    simpa only [d36, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d36, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11282 pattern childGuard
    simpa only [d36, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15172 (pattern : Twelve) (guard : d1 pattern = 1) : d57 pattern ≤ (1 : Int) + d56 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d57, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11732 pattern childGuard
    simpa only [d57, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d57, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15171 pattern childGuard
    simpa only [d57, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15173 (pattern : Twelve) (guard : d1859 pattern = 1) : d77 pattern ≤ (1 : Int) + d56 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1859, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15170 pattern childGuard
    simpa only [d1859, d77, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1859, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15172 pattern childGuard
    simpa only [d1859, d77, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15174 (pattern : Twelve) (guard : d0 pattern = 1) : d78 pattern ≤ (1 : Int) + d56 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15175 (pattern : Twelve) (guard : d2496 pattern = 1) : d94 pattern ≤ (1 : Int) + d56 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1859 pattern = 1 := by simpa only [d2496, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15173 pattern childGuard
    simpa only [d2496, d94, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2496, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15174 pattern childGuard
    simpa only [d2496, d94, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15176 (pattern : Twelve) (guard : d2496 pattern = 1) : d103 pattern ≤ (1 : Int) + d2498 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d103, d2498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15169 pattern childGuard
    simpa only [d103, d2498, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d103, d2498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15175 pattern childGuard
    simpa only [d103, d2498, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15177 (pattern : Twelve) (guard : d2496 pattern = 1) : d110 pattern ≤ (1 : Int) + d2499 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d110, d2499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15167 pattern childGuard
    simpa only [d110, d2499, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d110, d2499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15176 pattern childGuard
    simpa only [d110, d2499, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15178 (pattern : Twelve) (guard : d0 pattern = 1) : d30 pattern ≤ (1 : Int) + d30 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15179 (pattern : Twelve) (guard : d1 pattern = 1) : d37 pattern ≤ (1 : Int) + d30 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d37, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15154 pattern childGuard
    simpa only [d37, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d37, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11183 pattern childGuard
    simpa only [d37, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15180 (pattern : Twelve) (guard : d1 pattern = 1) : d58 pattern ≤ (1 : Int) + d30 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11732 pattern childGuard
    simpa only [d58, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15179 pattern childGuard
    simpa only [d58, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15181 (pattern : Twelve) (guard : d1859 pattern = 1) : d79 pattern ≤ (1 : Int) + d30 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1859, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15178 pattern childGuard
    simpa only [d1859, d79, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1859, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15180 pattern childGuard
    simpa only [d1859, d79, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15182 (pattern : Twelve) (guard : d0 pattern = 1) : d80 pattern ≤ (1 : Int) + d30 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15183 (pattern : Twelve) (guard : d2496 pattern = 1) : d95 pattern ≤ (1 : Int) + d30 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1859 pattern = 1 := by simpa only [d2496, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15181 pattern childGuard
    simpa only [d2496, d95, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2496, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15182 pattern childGuard
    simpa only [d2496, d95, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15184 (pattern : Twelve) (guard : d0 pattern = 1) : d59 pattern ≤ (1 : Int) + d59 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15185 (pattern : Twelve) (guard : d1 pattern = 1) : d9 pattern ≤ (1 : Int) + d2 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11127 pattern childGuard
    simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11183 pattern childGuard
    simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15186 (pattern : Twelve) (guard : d1 pattern = 1) : d23 pattern ≤ (1 : Int) + d2 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11127 pattern childGuard
    simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15185 pattern childGuard
    simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15187 (pattern : Twelve) (guard : d1 pattern = 1) : d40 pattern ≤ (1 : Int) + d39 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d40, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15186 pattern childGuard
    simpa only [d40, d39, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d40, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11282 pattern childGuard
    simpa only [d40, d39, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15188 (pattern : Twelve) (guard : d1 pattern = 1) : d60 pattern ≤ (1 : Int) + d59 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d60, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12003 pattern childGuard
    simpa only [d60, d59, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d60, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15187 pattern childGuard
    simpa only [d60, d59, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15189 (pattern : Twelve) (guard : d1859 pattern = 1) : d81 pattern ≤ (1 : Int) + d59 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1859, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15184 pattern childGuard
    simpa only [d1859, d81, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1859, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15188 pattern childGuard
    simpa only [d1859, d81, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15190 (pattern : Twelve) (guard : d0 pattern = 1) : d82 pattern ≤ (1 : Int) + d59 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15191 (pattern : Twelve) (guard : d2496 pattern = 1) : d96 pattern ≤ (1 : Int) + d59 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1859 pattern = 1 := by simpa only [d2496, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15189 pattern childGuard
    simpa only [d2496, d96, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2496, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15190 pattern childGuard
    simpa only [d2496, d96, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15192 (pattern : Twelve) (guard : d2496 pattern = 1) : d104 pattern ≤ (1 : Int) + d2500 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d104, d2500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15183 pattern childGuard
    simpa only [d104, d2500, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d104, d2500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15191 pattern childGuard
    simpa only [d104, d2500, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15193 (pattern : Twelve) (guard : d2496 pattern = 1) : d6 pattern ≤ (1 : Int) + d6 pattern := by
  omega
theorem c15194 (pattern : Twelve) (guard : d2496 pattern = 1) : d105 pattern ≤ (1 : Int) + d2501 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d105, d2501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15175 pattern childGuard
    simpa only [d105, d2501, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d105, d2501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15193 pattern childGuard
    simpa only [d105, d2501, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15195 (pattern : Twelve) (guard : d2496 pattern = 1) : d111 pattern ≤ (1 : Int) + d2502 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d111, d2502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15192 pattern childGuard
    simpa only [d111, d2502, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d111, d2502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15194 pattern childGuard
    simpa only [d111, d2502, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15196 (pattern : Twelve) (guard : d2496 pattern = 1) : d114 pattern ≤ (1 : Int) + d2503 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d114, d2503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15177 pattern childGuard
    simpa only [d114, d2503, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d114, d2503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15195 pattern childGuard
    simpa only [d114, d2503, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15197 (pattern : Twelve) (guard : d0 pattern = 1) : d136 pattern ≤ (1 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15198 (pattern : Twelve) (guard : d2496 pattern = 1) : d144 pattern ≤ (1 : Int) + d0 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1859 pattern = 1 := by simpa only [d2496, d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15157 pattern childGuard
    simpa only [d2496, d144, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2496, d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15197 pattern childGuard
    simpa only [d2496, d144, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15199 (pattern : Twelve) (guard : d0 pattern = 1) : d52 pattern ≤ (1 : Int) + d56 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15200 (pattern : Twelve) (guard : d1 pattern = 1) : d121 pattern ≤ (1 : Int) + d30 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d121, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11049 pattern childGuard
    simpa only [d121, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d121, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15186 pattern childGuard
    simpa only [d121, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15201 (pattern : Twelve) (guard : d1 pattern = 1) : d130 pattern ≤ (1 : Int) + d56 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d130, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15200 pattern childGuard
    simpa only [d130, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d130, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15171 pattern childGuard
    simpa only [d130, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15202 (pattern : Twelve) (guard : d1859 pattern = 1) : d137 pattern ≤ (1 : Int) + d56 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1859, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15199 pattern childGuard
    simpa only [d1859, d137, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1859, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15201 pattern childGuard
    simpa only [d1859, d137, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15203 (pattern : Twelve) (guard : d0 pattern = 1) : d138 pattern ≤ (1 : Int) + d56 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15204 (pattern : Twelve) (guard : d2496 pattern = 1) : d145 pattern ≤ (1 : Int) + d56 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1859 pattern = 1 := by simpa only [d2496, d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15202 pattern childGuard
    simpa only [d2496, d145, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2496, d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15203 pattern childGuard
    simpa only [d2496, d145, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15205 (pattern : Twelve) (guard : d2496 pattern = 1) : d149 pattern ≤ (1 : Int) + d2498 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d149, d2498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15198 pattern childGuard
    simpa only [d149, d2498, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d149, d2498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15204 pattern childGuard
    simpa only [d149, d2498, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15206 (pattern : Twelve) (guard : d1859 pattern = 1) : d139 pattern ≤ (1 : Int) + d56 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1859, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15170 pattern childGuard
    simpa only [d1859, d139, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1859, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15201 pattern childGuard
    simpa only [d1859, d139, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15207 (pattern : Twelve) (guard : d2496 pattern = 1) : d146 pattern ≤ (1 : Int) + d56 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1859 pattern = 1 := by simpa only [d2496, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15206 pattern childGuard
    simpa only [d2496, d146, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2496, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15203 pattern childGuard
    simpa only [d2496, d146, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15208 (pattern : Twelve) (guard : d2496 pattern = 1) : d150 pattern ≤ (1 : Int) + d2498 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d150, d2498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15198 pattern childGuard
    simpa only [d150, d2498, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d150, d2498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15207 pattern childGuard
    simpa only [d150, d2498, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15209 (pattern : Twelve) (guard : d2496 pattern = 1) : d153 pattern ≤ (1 : Int) + d2498 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15205 pattern childGuard
    simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15208 pattern childGuard
    simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15210 (pattern : Twelve) (guard : d0 pattern = 1) : d30 pattern ≤ (1 : Int) + d132 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15211 (pattern : Twelve) (guard : d1 pattern = 1) : d122 pattern ≤ (1 : Int) + d123 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d122, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15154 pattern childGuard
    simpa only [d122, d123, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d122, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11184 pattern childGuard
    simpa only [d122, d123, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15212 (pattern : Twelve) (guard : d1 pattern = 1) : d131 pattern ≤ (1 : Int) + d132 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d131, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15200 pattern childGuard
    simpa only [d131, d132, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d131, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15211 pattern childGuard
    simpa only [d131, d132, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15213 (pattern : Twelve) (guard : d1859 pattern = 1) : d140 pattern ≤ (1 : Int) + d132 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1859, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15210 pattern childGuard
    simpa only [d1859, d140, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1859, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15212 pattern childGuard
    simpa only [d1859, d140, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15214 (pattern : Twelve) (guard : d0 pattern = 1) : d141 pattern ≤ (1 : Int) + d132 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15215 (pattern : Twelve) (guard : d2496 pattern = 1) : d147 pattern ≤ (1 : Int) + d132 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1859 pattern = 1 := by simpa only [d2496, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15213 pattern childGuard
    simpa only [d2496, d147, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2496, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15214 pattern childGuard
    simpa only [d2496, d147, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15216 (pattern : Twelve) (guard : d0 pattern = 1) : d59 pattern ≤ (1 : Int) + d134 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15217 (pattern : Twelve) (guard : d1 pattern = 1) : d14 pattern ≤ (1 : Int) + d5 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11385 pattern childGuard
    simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11197 pattern childGuard
    simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15218 (pattern : Twelve) (guard : d1 pattern = 1) : d118 pattern ≤ (1 : Int) + d5 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11385 pattern childGuard
    simpa only [d118, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15217 pattern childGuard
    simpa only [d118, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15219 (pattern : Twelve) (guard : d1 pattern = 1) : d124 pattern ≤ (1 : Int) + d126 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d124, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11127 pattern childGuard
    simpa only [d124, d126, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d124, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15218 pattern childGuard
    simpa only [d124, d126, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15220 (pattern : Twelve) (guard : d1 pattern = 1) : d117 pattern ≤ (1 : Int) + d3 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11190 pattern childGuard
    simpa only [d117, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11184 pattern childGuard
    simpa only [d117, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15221 (pattern : Twelve) (guard : d1 pattern = 1) : d119 pattern ≤ (1 : Int) + d3 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11190 pattern childGuard
    simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15220 pattern childGuard
    simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15222 (pattern : Twelve) (guard : d1 pattern = 1) : d125 pattern ≤ (1 : Int) + d47 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d125, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15221 pattern childGuard
    simpa only [d125, d47, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d125, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11282 pattern childGuard
    simpa only [d125, d47, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15223 (pattern : Twelve) (guard : d1 pattern = 1) : d133 pattern ≤ (1 : Int) + d134 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d133, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15219 pattern childGuard
    simpa only [d133, d134, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d133, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15222 pattern childGuard
    simpa only [d133, d134, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15224 (pattern : Twelve) (guard : d1859 pattern = 1) : d142 pattern ≤ (1 : Int) + d134 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1859, d142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15216 pattern childGuard
    simpa only [d1859, d142, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1859, d142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15223 pattern childGuard
    simpa only [d1859, d142, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15225 (pattern : Twelve) (guard : d0 pattern = 1) : d143 pattern ≤ (1 : Int) + d134 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15226 (pattern : Twelve) (guard : d2496 pattern = 1) : d148 pattern ≤ (1 : Int) + d134 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1859 pattern = 1 := by simpa only [d2496, d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15224 pattern childGuard
    simpa only [d2496, d148, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2496, d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15225 pattern childGuard
    simpa only [d2496, d148, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15227 (pattern : Twelve) (guard : d2496 pattern = 1) : d151 pattern ≤ (1 : Int) + d2504 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d151, d2504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15215 pattern childGuard
    simpa only [d151, d2504, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d151, d2504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15226 pattern childGuard
    simpa only [d151, d2504, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15228 (pattern : Twelve) (guard : d2496 pattern = 1) : d152 pattern ≤ (1 : Int) + d2501 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d152, d2501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15207 pattern childGuard
    simpa only [d152, d2501, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d152, d2501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15193 pattern childGuard
    simpa only [d152, d2501, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15229 (pattern : Twelve) (guard : d2496 pattern = 1) : d154 pattern ≤ (1 : Int) + d2505 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d154, d2505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15227 pattern childGuard
    simpa only [d154, d2505, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d154, d2505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15228 pattern childGuard
    simpa only [d154, d2505, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15230 (pattern : Twelve) (guard : d2496 pattern = 1) : d155 pattern ≤ (1 : Int) + d2506 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d155, d2506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15209 pattern childGuard
    simpa only [d155, d2506, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d155, d2506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15229 pattern childGuard
    simpa only [d155, d2506, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15231 (pattern : Twelve) (guard : d2496 pattern = 1) : d156 pattern ≤ (1 : Int) + d2507 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d156, d2507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15196 pattern childGuard
    simpa only [d156, d2507, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d156, d2507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15230 pattern childGuard
    simpa only [d156, d2507, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15232 (pattern : Twelve) (guard : d0 pattern = 1) : d0 pattern ≤ (1 : Int) + d17 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15233 (pattern : Twelve) (guard : d1 pattern = 1) : d1 pattern ≤ (1 : Int) + d7 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15151 pattern childGuard
    simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11212 pattern childGuard
    simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15234 (pattern : Twelve) (guard : d1 pattern = 1) : d1 pattern ≤ (1 : Int) + d17 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15151 pattern childGuard
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15233 pattern childGuard
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15235 (pattern : Twelve) (guard : d1 pattern = 1) : d27 pattern ≤ (1 : Int) + d17 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11054 pattern childGuard
    simpa only [d27, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15234 pattern childGuard
    simpa only [d27, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15236 (pattern : Twelve) (guard : d1 pattern = 1) : d814 pattern ≤ (1 : Int) + d17 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d814, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15153 pattern childGuard
    simpa only [d814, d17, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d814, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15233 pattern childGuard
    simpa only [d814, d17, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15237 (pattern : Twelve) (guard : d1 pattern = 1) : d816 pattern ≤ (1 : Int) + d17 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15236 pattern childGuard
    simpa only [d816, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15234 pattern childGuard
    simpa only [d816, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15238 (pattern : Twelve) (guard : d1 pattern = 1) : d824 pattern ≤ (1 : Int) + d17 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15235 pattern childGuard
    simpa only [d824, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15237 pattern childGuard
    simpa only [d824, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15239 (pattern : Twelve) (guard : d1859 pattern = 1) : d838 pattern ≤ (1 : Int) + d17 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1859, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15232 pattern childGuard
    simpa only [d1859, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1859, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15238 pattern childGuard
    simpa only [d1859, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15240 (pattern : Twelve) (guard : d0 pattern = 1) : d839 pattern ≤ (1 : Int) + d17 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15241 (pattern : Twelve) (guard : d2496 pattern = 1) : d853 pattern ≤ (1 : Int) + d17 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1859 pattern = 1 := by simpa only [d2496, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15239 pattern childGuard
    simpa only [d2496, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2496, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15240 pattern childGuard
    simpa only [d2496, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15242 (pattern : Twelve) (guard : d0 pattern = 1) : d56 pattern ≤ (1 : Int) + d827 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15243 (pattern : Twelve) (guard : d1 pattern = 1) : d818 pattern ≤ (1 : Int) + d36 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d818, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15236 pattern childGuard
    simpa only [d818, d36, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d818, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11282 pattern childGuard
    simpa only [d818, d36, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15244 (pattern : Twelve) (guard : d1 pattern = 1) : d826 pattern ≤ (1 : Int) + d827 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d826, d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11859 pattern childGuard
    simpa only [d826, d827, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d826, d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15243 pattern childGuard
    simpa only [d826, d827, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15245 (pattern : Twelve) (guard : d1859 pattern = 1) : d840 pattern ≤ (1 : Int) + d827 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1859, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15242 pattern childGuard
    simpa only [d1859, d840, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1859, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15244 pattern childGuard
    simpa only [d1859, d840, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15246 (pattern : Twelve) (guard : d0 pattern = 1) : d841 pattern ≤ (1 : Int) + d827 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15247 (pattern : Twelve) (guard : d2496 pattern = 1) : d854 pattern ≤ (1 : Int) + d827 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1859 pattern = 1 := by simpa only [d2496, d854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15245 pattern childGuard
    simpa only [d2496, d854, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2496, d854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15246 pattern childGuard
    simpa only [d2496, d854, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15248 (pattern : Twelve) (guard : d2496 pattern = 1) : d861 pattern ≤ (1 : Int) + d2508 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d861, d2508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15241 pattern childGuard
    simpa only [d861, d2508, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d861, d2508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15247 pattern childGuard
    simpa only [d861, d2508, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15249 (pattern : Twelve) (guard : d0 pattern = 1) : d30 pattern ≤ (1 : Int) + d34 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15250 (pattern : Twelve) (guard : d1 pattern = 1) : d819 pattern ≤ (1 : Int) + d34 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d819, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15236 pattern childGuard
    simpa only [d819, d34, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d819, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11192 pattern childGuard
    simpa only [d819, d34, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15251 (pattern : Twelve) (guard : d1 pattern = 1) : d828 pattern ≤ (1 : Int) + d34 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11859 pattern childGuard
    simpa only [d828, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15250 pattern childGuard
    simpa only [d828, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15252 (pattern : Twelve) (guard : d1859 pattern = 1) : d842 pattern ≤ (1 : Int) + d34 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1859, d842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15249 pattern childGuard
    simpa only [d1859, d842, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1859, d842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15251 pattern childGuard
    simpa only [d1859, d842, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15253 (pattern : Twelve) (guard : d0 pattern = 1) : d843 pattern ≤ (1 : Int) + d34 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15254 (pattern : Twelve) (guard : d2496 pattern = 1) : d855 pattern ≤ (1 : Int) + d34 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1859 pattern = 1 := by simpa only [d2496, d855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15252 pattern childGuard
    simpa only [d2496, d855, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2496, d855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15253 pattern childGuard
    simpa only [d2496, d855, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15255 (pattern : Twelve) (guard : d0 pattern = 1) : d59 pattern ≤ (1 : Int) + d830 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15256 (pattern : Twelve) (guard : d1 pattern = 1) : d815 pattern ≤ (1 : Int) + d23 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d815, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15185 pattern childGuard
    simpa only [d815, d23, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d815, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11191 pattern childGuard
    simpa only [d815, d23, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15257 (pattern : Twelve) (guard : d1 pattern = 1) : d820 pattern ≤ (1 : Int) + d40 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d820, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15256 pattern childGuard
    simpa only [d820, d40, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d820, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11282 pattern childGuard
    simpa only [d820, d40, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15258 (pattern : Twelve) (guard : d1 pattern = 1) : d829 pattern ≤ (1 : Int) + d830 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d829, d830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12077 pattern childGuard
    simpa only [d829, d830, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d829, d830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15257 pattern childGuard
    simpa only [d829, d830, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15259 (pattern : Twelve) (guard : d1859 pattern = 1) : d844 pattern ≤ (1 : Int) + d830 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1859, d844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15255 pattern childGuard
    simpa only [d1859, d844, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1859, d844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15258 pattern childGuard
    simpa only [d1859, d844, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
