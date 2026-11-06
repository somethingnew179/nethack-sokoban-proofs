/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons086
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c12180 (pattern : Twelve) (guard : d1999 pattern = 1) : d1323 pattern ≤ (1 : Int) + d2051 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1999 pattern = 1 := by simpa only [d1323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12154 pattern childGuard
    simpa only [d1323, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1999 pattern = 1 := by simpa only [d1323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12179 pattern childGuard
    simpa only [d1323, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12181 (pattern : Twelve) (guard : d0 pattern = 1) : d1649 pattern ≤ (1 : Int) + d1324 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c12182 (pattern : Twelve) (guard : d1 pattern = 1) : d16 pattern ≤ (1 : Int) + d11 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d16, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12013 pattern childGuard
    simpa only [d16, d11, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d16, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11184 pattern childGuard
    simpa only [d16, d11, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12183 (pattern : Twelve) (guard : d1 pattern = 1) : d25 pattern ≤ (1 : Int) + d1324 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d25, d1324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12182 pattern childGuard
    simpa only [d25, d1324, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d25, d1324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11196 pattern childGuard
    simpa only [d25, d1324, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12184 (pattern : Twelve) (guard : d1852 pattern = 1) : d1650 pattern ≤ (1 : Int) + d1324 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12183 pattern childGuard
    simpa only [d1852, d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11335 pattern childGuard
    simpa only [d1852, d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12185 (pattern : Twelve) (guard : d1999 pattern = 1) : d1656 pattern ≤ (1 : Int) + d1324 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1999, d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12181 pattern childGuard
    simpa only [d1999, d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1999, d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12184 pattern childGuard
    simpa only [d1999, d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12186 (pattern : Twelve) (guard : d0 pattern = 1) : d1651 pattern ≤ (1 : Int) + d1647 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c12187 (pattern : Twelve) (guard : d1 pattern = 1) : d21 pattern ≤ (1 : Int) + d20 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d21, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11198 pattern childGuard
    simpa only [d21, d20, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d21, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11387 pattern childGuard
    simpa only [d21, d20, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12188 (pattern : Twelve) (guard : d1 pattern = 1) : d821 pattern ≤ (1 : Int) + d1644 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d821, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12183 pattern childGuard
    simpa only [d821, d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d821, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12187 pattern childGuard
    simpa only [d821, d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12189 (pattern : Twelve) (guard : d1 pattern = 1) : d42 pattern ≤ (1 : Int) + d1645 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d42, d1645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12183 pattern childGuard
    simpa only [d42, d1645, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d42, d1645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11282 pattern childGuard
    simpa only [d42, d1645, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12190 (pattern : Twelve) (guard : d1 pattern = 1) : d1289 pattern ≤ (1 : Int) + d1647 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1289, d1647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12188 pattern childGuard
    simpa only [d1289, d1647, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1289, d1647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12189 pattern childGuard
    simpa only [d1289, d1647, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12191 (pattern : Twelve) (guard : d1852 pattern = 1) : d1300 pattern ≤ (1 : Int) + d1647 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12190 pattern childGuard
    simpa only [d1852, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11902 pattern childGuard
    simpa only [d1852, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12192 (pattern : Twelve) (guard : d1999 pattern = 1) : d1657 pattern ≤ (1 : Int) + d1647 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1999, d1657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12186 pattern childGuard
    simpa only [d1999, d1657, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1999, d1657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12191 pattern childGuard
    simpa only [d1999, d1657, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12193 (pattern : Twelve) (guard : d1999 pattern = 1) : d1660 pattern ≤ (1 : Int) + d2052 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1999 pattern = 1 := by simpa only [d1660, d2052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12185 pattern childGuard
    simpa only [d1660, d2052, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1999 pattern = 1 := by simpa only [d1660, d2052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12192 pattern childGuard
    simpa only [d1660, d2052, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12194 (pattern : Twelve) (guard : d0 pattern = 1) : d1652 pattern ≤ (1 : Int) + d1644 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c12195 (pattern : Twelve) (guard : d1852 pattern = 1) : d1653 pattern ≤ (1 : Int) + d1644 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d1653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12188 pattern childGuard
    simpa only [d1852, d1653, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d1653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11912 pattern childGuard
    simpa only [d1852, d1653, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12196 (pattern : Twelve) (guard : d1999 pattern = 1) : d1658 pattern ≤ (1 : Int) + d1644 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1999, d1658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12194 pattern childGuard
    simpa only [d1999, d1658, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1999, d1658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12195 pattern childGuard
    simpa only [d1999, d1658, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12197 (pattern : Twelve) (guard : d0 pattern = 1) : d1654 pattern ≤ (1 : Int) + d1648 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c12198 (pattern : Twelve) (guard : d1 pattern = 1) : d6 pattern ≤ (1 : Int) + d22 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11931 pattern childGuard
    simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11282 pattern childGuard
    simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12199 (pattern : Twelve) (guard : d1 pattern = 1) : d822 pattern ≤ (1 : Int) + d1646 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d822, d1646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12187 pattern childGuard
    simpa only [d822, d1646, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d822, d1646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12198 pattern childGuard
    simpa only [d822, d1646, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12200 (pattern : Twelve) (guard : d1 pattern = 1) : d822 pattern ≤ (1 : Int) + d128 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d822, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12187 pattern childGuard
    simpa only [d822, d128, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d822, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11282 pattern childGuard
    simpa only [d822, d128, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12201 (pattern : Twelve) (guard : d1 pattern = 1) : d822 pattern ≤ (1 : Int) + d1648 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12199 pattern childGuard
    simpa only [d1648, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12200 pattern childGuard
    simpa only [d1648, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12202 (pattern : Twelve) (guard : d1852 pattern = 1) : d1655 pattern ≤ (1 : Int) + d1648 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d1655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12201 pattern childGuard
    simpa only [d1852, d1655, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d1655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11917 pattern childGuard
    simpa only [d1852, d1655, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12203 (pattern : Twelve) (guard : d1999 pattern = 1) : d1659 pattern ≤ (1 : Int) + d1648 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1999, d1659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12197 pattern childGuard
    simpa only [d1999, d1659, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1999, d1659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12202 pattern childGuard
    simpa only [d1999, d1659, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12204 (pattern : Twelve) (guard : d1999 pattern = 1) : d1661 pattern ≤ (1 : Int) + d2053 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1999 pattern = 1 := by simpa only [d1661, d2053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12196 pattern childGuard
    simpa only [d1661, d2053, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1999 pattern = 1 := by simpa only [d1661, d2053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12203 pattern childGuard
    simpa only [d1661, d2053, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12205 (pattern : Twelve) (guard : d1999 pattern = 1) : d1662 pattern ≤ (1 : Int) + d2054 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1999 pattern = 1 := by simpa only [d1662, d2054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12192 pattern childGuard
    simpa only [d1662, d2054, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1999 pattern = 1 := by simpa only [d1662, d2054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11762 pattern childGuard
    simpa only [d1662, d2054, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12206 (pattern : Twelve) (guard : d1999 pattern = 1) : d1663 pattern ≤ (1 : Int) + d2055 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1999 pattern = 1 := by simpa only [d1663, d2055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12204 pattern childGuard
    simpa only [d1663, d2055, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1999 pattern = 1 := by simpa only [d1663, d2055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12205 pattern childGuard
    simpa only [d1663, d2055, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12207 (pattern : Twelve) (guard : d1999 pattern = 1) : d1664 pattern ≤ (1 : Int) + d2056 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1999 pattern = 1 := by simpa only [d1664, d2056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12193 pattern childGuard
    simpa only [d1664, d2056, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1999 pattern = 1 := by simpa only [d1664, d2056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12206 pattern childGuard
    simpa only [d1664, d2056, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12208 (pattern : Twelve) (guard : d1865 pattern = 1) : d0 pattern ≤ (1 : Int) + d0 pattern := by
  omega
theorem c12209 (pattern : Twelve) (guard : d0 pattern = 1) : d1 pattern ≤ (1 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c12210 (pattern : Twelve) (guard : d1865 pattern = 1) : d477 pattern ≤ (1 : Int) + d0 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11049 pattern childGuard
    simpa only [d1865, d477, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12209 pattern childGuard
    simpa only [d1865, d477, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12211 (pattern : Twelve) (guard : d1865 pattern = 1) : d498 pattern ≤ (1 : Int) + d0 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12208 pattern childGuard
    simpa only [d498, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12210 pattern childGuard
    simpa only [d498, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12212 (pattern : Twelve) (guard : d0 pattern = 1) : d157 pattern ≤ (1 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c12213 (pattern : Twelve) (guard : d1865 pattern = 1) : d478 pattern ≤ (1 : Int) + d0 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11049 pattern childGuard
    simpa only [d1865, d478, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12212 pattern childGuard
    simpa only [d1865, d478, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12214 (pattern : Twelve) (guard : d1865 pattern = 1) : d499 pattern ≤ (1 : Int) + d0 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12208 pattern childGuard
    simpa only [d499, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12213 pattern childGuard
    simpa only [d499, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12215 (pattern : Twelve) (guard : d1865 pattern = 1) : d532 pattern ≤ (1 : Int) + d0 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12211 pattern childGuard
    simpa only [d532, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12214 pattern childGuard
    simpa only [d532, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12216 (pattern : Twelve) (guard : d0 pattern = 1) : d0 pattern ≤ (1 : Int) + d7 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c12217 (pattern : Twelve) (guard : d1865 pattern = 1) : d0 pattern ≤ (1 : Int) + d17 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11049 pattern childGuard
    simpa only [d1865, d17, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12216 pattern childGuard
    simpa only [d1865, d17, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12218 (pattern : Twelve) (guard : d0 pattern = 1) : d157 pattern ≤ (1 : Int) + d1 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c12219 (pattern : Twelve) (guard : d1865 pattern = 1) : d161 pattern ≤ (1 : Int) + d1 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11212 pattern childGuard
    simpa only [d1865, d161, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12218 pattern childGuard
    simpa only [d1865, d161, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12220 (pattern : Twelve) (guard : d1865 pattern = 1) : d171 pattern ≤ (1 : Int) + d27 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d171, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12217 pattern childGuard
    simpa only [d171, d27, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d171, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12219 pattern childGuard
    simpa only [d171, d27, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12221 (pattern : Twelve) (guard : d0 pattern = 1) : d158 pattern ≤ (1 : Int) + d1 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c12222 (pattern : Twelve) (guard : d1865 pattern = 1) : d162 pattern ≤ (1 : Int) + d814 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d162, d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11061 pattern childGuard
    simpa only [d1865, d162, d814, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d162, d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12221 pattern childGuard
    simpa only [d1865, d162, d814, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12223 (pattern : Twelve) (guard : d1865 pattern = 1) : d479 pattern ≤ (1 : Int) + d1 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11212 pattern childGuard
    simpa only [d1865, d479, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11094 pattern childGuard
    simpa only [d1865, d479, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12224 (pattern : Twelve) (guard : d1865 pattern = 1) : d500 pattern ≤ (1 : Int) + d816 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d500, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12222 pattern childGuard
    simpa only [d500, d816, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d500, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12223 pattern childGuard
    simpa only [d500, d816, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12225 (pattern : Twelve) (guard : d1865 pattern = 1) : d533 pattern ≤ (1 : Int) + d824 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d533, d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12220 pattern childGuard
    simpa only [d533, d824, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d533, d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12224 pattern childGuard
    simpa only [d533, d824, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12226 (pattern : Twelve) (guard : d1865 pattern = 1) : d561 pattern ≤ (1 : Int) + d838 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d561, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12215 pattern childGuard
    simpa only [d561, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d561, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12225 pattern childGuard
    simpa only [d561, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12227 (pattern : Twelve) (guard : d0 pattern = 1) : d157 pattern ≤ (1 : Int) + d7 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c12228 (pattern : Twelve) (guard : d1865 pattern = 1) : d478 pattern ≤ (1 : Int) + d17 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d478, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11049 pattern childGuard
    simpa only [d1865, d478, d17, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d478, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12227 pattern childGuard
    simpa only [d1865, d478, d17, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12229 (pattern : Twelve) (guard : d1865 pattern = 1) : d499 pattern ≤ (1 : Int) + d17 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12217 pattern childGuard
    simpa only [d499, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12228 pattern childGuard
    simpa only [d499, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12230 (pattern : Twelve) (guard : d0 pattern = 1) : d158 pattern ≤ (1 : Int) + d7 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c12231 (pattern : Twelve) (guard : d1865 pattern = 1) : d162 pattern ≤ (1 : Int) + d17 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d162, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11049 pattern childGuard
    simpa only [d1865, d162, d17, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d162, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12230 pattern childGuard
    simpa only [d1865, d162, d17, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12232 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (1 : Int) + d7 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c12233 (pattern : Twelve) (guard : d1865 pattern = 1) : d480 pattern ≤ (1 : Int) + d17 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d480, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11049 pattern childGuard
    simpa only [d1865, d480, d17, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d480, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12232 pattern childGuard
    simpa only [d1865, d480, d17, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12234 (pattern : Twelve) (guard : d1865 pattern = 1) : d501 pattern ≤ (1 : Int) + d17 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12231 pattern childGuard
    simpa only [d501, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12233 pattern childGuard
    simpa only [d501, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12235 (pattern : Twelve) (guard : d1865 pattern = 1) : d534 pattern ≤ (1 : Int) + d17 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12229 pattern childGuard
    simpa only [d534, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12234 pattern childGuard
    simpa only [d534, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12236 (pattern : Twelve) (guard : d0 pattern = 1) : d158 pattern ≤ (1 : Int) + d11 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c12237 (pattern : Twelve) (guard : d1865 pattern = 1) : d162 pattern ≤ (1 : Int) + d19 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d162, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11222 pattern childGuard
    simpa only [d1865, d162, d19, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d162, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12236 pattern childGuard
    simpa only [d1865, d162, d19, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12238 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (1 : Int) + d12 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c12239 (pattern : Twelve) (guard : d1865 pattern = 1) : d481 pattern ≤ (1 : Int) + d25 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d481, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11333 pattern childGuard
    simpa only [d1865, d481, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d481, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12238 pattern childGuard
    simpa only [d1865, d481, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12240 (pattern : Twelve) (guard : d1865 pattern = 1) : d502 pattern ≤ (1 : Int) + d817 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d502, d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12237 pattern childGuard
    simpa only [d502, d817, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d502, d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12239 pattern childGuard
    simpa only [d502, d817, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12241 (pattern : Twelve) (guard : d1865 pattern = 1) : d482 pattern ≤ (1 : Int) + d25 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d482, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11340 pattern childGuard
    simpa only [d1865, d482, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d482, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12238 pattern childGuard
    simpa only [d1865, d482, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12242 (pattern : Twelve) (guard : d1865 pattern = 1) : d6 pattern ≤ (1 : Int) + d6 pattern := by
  omega
theorem c12243 (pattern : Twelve) (guard : d1865 pattern = 1) : d503 pattern ≤ (1 : Int) + d42 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d503, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12241 pattern childGuard
    simpa only [d503, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d503, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12242 pattern childGuard
    simpa only [d503, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12244 (pattern : Twelve) (guard : d1865 pattern = 1) : d535 pattern ≤ (1 : Int) + d825 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d535, d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12240 pattern childGuard
    simpa only [d535, d825, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d535, d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12243 pattern childGuard
    simpa only [d535, d825, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12245 (pattern : Twelve) (guard : d1865 pattern = 1) : d562 pattern ≤ (1 : Int) + d839 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d562, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12235 pattern childGuard
    simpa only [d562, d839, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d562, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12244 pattern childGuard
    simpa only [d562, d839, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12246 (pattern : Twelve) (guard : d1865 pattern = 1) : d588 pattern ≤ (1 : Int) + d853 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d588, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12226 pattern childGuard
    simpa only [d588, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d588, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12245 pattern childGuard
    simpa only [d588, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12247 (pattern : Twelve) (guard : d0 pattern = 1) : d2 pattern ≤ (1 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c12248 (pattern : Twelve) (guard : d1865 pattern = 1) : d483 pattern ≤ (1 : Int) + d0 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11049 pattern childGuard
    simpa only [d1865, d483, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12247 pattern childGuard
    simpa only [d1865, d483, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12249 (pattern : Twelve) (guard : d0 pattern = 1) : d159 pattern ≤ (1 : Int) + d2 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c12250 (pattern : Twelve) (guard : d1865 pattern = 1) : d484 pattern ≤ (1 : Int) + d2 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11127 pattern childGuard
    simpa only [d1865, d484, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12249 pattern childGuard
    simpa only [d1865, d484, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12251 (pattern : Twelve) (guard : d1865 pattern = 1) : d504 pattern ≤ (1 : Int) + d30 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d504, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12248 pattern childGuard
    simpa only [d504, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d504, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12250 pattern childGuard
    simpa only [d504, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12252 (pattern : Twelve) (guard : d0 pattern = 1) : d160 pattern ≤ (1 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c12253 (pattern : Twelve) (guard : d1865 pattern = 1) : d485 pattern ≤ (1 : Int) + d0 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11049 pattern childGuard
    simpa only [d1865, d485, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12252 pattern childGuard
    simpa only [d1865, d485, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12254 (pattern : Twelve) (guard : d1865 pattern = 1) : d486 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d486, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11235 pattern childGuard
    simpa only [d1865, d486, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d486, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11237 pattern childGuard
    simpa only [d1865, d486, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12255 (pattern : Twelve) (guard : d1865 pattern = 1) : d505 pattern ≤ (1 : Int) + d35 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d505, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12253 pattern childGuard
    simpa only [d505, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d505, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12254 pattern childGuard
    simpa only [d505, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12256 (pattern : Twelve) (guard : d1865 pattern = 1) : d536 pattern ≤ (1 : Int) + d56 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d536, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12251 pattern childGuard
    simpa only [d536, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d536, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12255 pattern childGuard
    simpa only [d536, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12257 (pattern : Twelve) (guard : d0 pattern = 1) : d160 pattern ≤ (1 : Int) + d7 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c12258 (pattern : Twelve) (guard : d1865 pattern = 1) : d485 pattern ≤ (1 : Int) + d17 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d485, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11049 pattern childGuard
    simpa only [d1865, d485, d17, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d485, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12257 pattern childGuard
    simpa only [d1865, d485, d17, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12259 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (1 : Int) + d9 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c12260 (pattern : Twelve) (guard : d1865 pattern = 1) : d487 pattern ≤ (1 : Int) + d23 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d487, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11127 pattern childGuard
    simpa only [d1865, d487, d23, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d487, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12259 pattern childGuard
    simpa only [d1865, d487, d23, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12261 (pattern : Twelve) (guard : d1865 pattern = 1) : d506 pattern ≤ (1 : Int) + d34 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d506, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12258 pattern childGuard
    simpa only [d506, d34, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d506, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12260 pattern childGuard
    simpa only [d506, d34, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12262 (pattern : Twelve) (guard : d1865 pattern = 1) : d480 pattern ≤ (1 : Int) + d814 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d480, d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11061 pattern childGuard
    simpa only [d1865, d480, d814, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d480, d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11094 pattern childGuard
    simpa only [d1865, d480, d814, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12263 (pattern : Twelve) (guard : d1865 pattern = 1) : d170 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11283 pattern childGuard
    simpa only [d1865, d170, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11237 pattern childGuard
    simpa only [d1865, d170, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12264 (pattern : Twelve) (guard : d1865 pattern = 1) : d507 pattern ≤ (1 : Int) + d818 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d507, d818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12262 pattern childGuard
    simpa only [d507, d818, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d507, d818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12263 pattern childGuard
    simpa only [d507, d818, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12265 (pattern : Twelve) (guard : d1865 pattern = 1) : d537 pattern ≤ (1 : Int) + d826 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d537, d826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12261 pattern childGuard
    simpa only [d537, d826, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d537, d826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12264 pattern childGuard
    simpa only [d537, d826, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12266 (pattern : Twelve) (guard : d1865 pattern = 1) : d563 pattern ≤ (1 : Int) + d840 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d563, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12256 pattern childGuard
    simpa only [d563, d840, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d563, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12265 pattern childGuard
    simpa only [d563, d840, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12267 (pattern : Twelve) (guard : d1865 pattern = 1) : d22 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11284 pattern childGuard
    simpa only [d1865, d22, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11237 pattern childGuard
    simpa only [d1865, d22, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12268 (pattern : Twelve) (guard : d1865 pattern = 1) : d508 pattern ≤ (1 : Int) + d36 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d508, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12233 pattern childGuard
    simpa only [d508, d36, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d508, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12267 pattern childGuard
    simpa only [d508, d36, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12269 (pattern : Twelve) (guard : d1865 pattern = 1) : d538 pattern ≤ (1 : Int) + d827 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d538, d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12261 pattern childGuard
    simpa only [d538, d827, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d538, d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12268 pattern childGuard
    simpa only [d538, d827, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12270 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (1 : Int) + d11 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c12271 (pattern : Twelve) (guard : d1865 pattern = 1) : d480 pattern ≤ (1 : Int) + d19 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d480, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11222 pattern childGuard
    simpa only [d1865, d480, d19, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d480, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12270 pattern childGuard
    simpa only [d1865, d480, d19, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12272 (pattern : Twelve) (guard : d1865 pattern = 1) : d487 pattern ≤ (1 : Int) + d25 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d487, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11275 pattern childGuard
    simpa only [d1865, d487, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d487, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12238 pattern childGuard
    simpa only [d1865, d487, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12273 (pattern : Twelve) (guard : d1865 pattern = 1) : d509 pattern ≤ (1 : Int) + d817 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d509, d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12271 pattern childGuard
    simpa only [d509, d817, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d509, d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12272 pattern childGuard
    simpa only [d509, d817, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12274 (pattern : Twelve) (guard : d1865 pattern = 1) : d539 pattern ≤ (1 : Int) + d825 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d539, d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12273 pattern childGuard
    simpa only [d539, d825, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d539, d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12243 pattern childGuard
    simpa only [d539, d825, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12275 (pattern : Twelve) (guard : d1865 pattern = 1) : d564 pattern ≤ (1 : Int) + d841 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d564, d841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12269 pattern childGuard
    simpa only [d564, d841, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d564, d841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12274 pattern childGuard
    simpa only [d564, d841, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12276 (pattern : Twelve) (guard : d1865 pattern = 1) : d589 pattern ≤ (1 : Int) + d854 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d589, d854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12266 pattern childGuard
    simpa only [d589, d854, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d589, d854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12275 pattern childGuard
    simpa only [d589, d854, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12277 (pattern : Twelve) (guard : d1865 pattern = 1) : d606 pattern ≤ (1 : Int) + d861 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d606, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12246 pattern childGuard
    simpa only [d606, d861, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d606, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12276 pattern childGuard
    simpa only [d606, d861, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12278 (pattern : Twelve) (guard : d0 pattern = 1) : d159 pattern ≤ (1 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c12279 (pattern : Twelve) (guard : d1865 pattern = 1) : d488 pattern ≤ (1 : Int) + d0 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11049 pattern childGuard
    simpa only [d1865, d488, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12278 pattern childGuard
    simpa only [d1865, d488, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12280 (pattern : Twelve) (guard : d1865 pattern = 1) : d510 pattern ≤ (1 : Int) + d0 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12248 pattern childGuard
    simpa only [d510, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12279 pattern childGuard
    simpa only [d510, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12281 (pattern : Twelve) (guard : d1865 pattern = 1) : d480 pattern ≤ (1 : Int) + d0 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11049 pattern childGuard
    simpa only [d1865, d480, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11159 pattern childGuard
    simpa only [d1865, d480, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12282 (pattern : Twelve) (guard : d1865 pattern = 1) : d511 pattern ≤ (1 : Int) + d0 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12253 pattern childGuard
    simpa only [d511, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12281 pattern childGuard
    simpa only [d511, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12283 (pattern : Twelve) (guard : d1865 pattern = 1) : d540 pattern ≤ (1 : Int) + d0 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12280 pattern childGuard
    simpa only [d540, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12282 pattern childGuard
    simpa only [d540, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12284 (pattern : Twelve) (guard : d1865 pattern = 1) : d512 pattern ≤ (1 : Int) + d27 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d512, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12258 pattern childGuard
    simpa only [d512, d27, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d512, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12223 pattern childGuard
    simpa only [d512, d27, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12285 (pattern : Twelve) (guard : d1865 pattern = 1) : d513 pattern ≤ (1 : Int) + d816 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d513, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12262 pattern childGuard
    simpa only [d513, d816, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d513, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12223 pattern childGuard
    simpa only [d513, d816, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12286 (pattern : Twelve) (guard : d1865 pattern = 1) : d541 pattern ≤ (1 : Int) + d824 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d541, d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12284 pattern childGuard
    simpa only [d541, d824, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d541, d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12285 pattern childGuard
    simpa only [d541, d824, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12287 (pattern : Twelve) (guard : d1865 pattern = 1) : d565 pattern ≤ (1 : Int) + d838 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d565, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12283 pattern childGuard
    simpa only [d565, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d565, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12286 pattern childGuard
    simpa only [d565, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12288 (pattern : Twelve) (guard : d1865 pattern = 1) : d511 pattern ≤ (1 : Int) + d17 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12258 pattern childGuard
    simpa only [d511, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12233 pattern childGuard
    simpa only [d511, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12289 (pattern : Twelve) (guard : d1865 pattern = 1) : d542 pattern ≤ (1 : Int) + d17 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12288 pattern childGuard
    simpa only [d542, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12233 pattern childGuard
    simpa only [d542, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12290 (pattern : Twelve) (guard : d1865 pattern = 1) : d566 pattern ≤ (1 : Int) + d839 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d566, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12289 pattern childGuard
    simpa only [d566, d839, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d566, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12274 pattern childGuard
    simpa only [d566, d839, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12291 (pattern : Twelve) (guard : d1865 pattern = 1) : d590 pattern ≤ (1 : Int) + d853 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d590, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12287 pattern childGuard
    simpa only [d590, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d590, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12290 pattern childGuard
    simpa only [d590, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12292 (pattern : Twelve) (guard : d0 pattern = 1) : d13 pattern ≤ (1 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c12293 (pattern : Twelve) (guard : d1865 pattern = 1) : d489 pattern ≤ (1 : Int) + d0 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11049 pattern childGuard
    simpa only [d1865, d489, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12292 pattern childGuard
    simpa only [d1865, d489, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12294 (pattern : Twelve) (guard : d1865 pattern = 1) : d487 pattern ≤ (1 : Int) + d2 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11127 pattern childGuard
    simpa only [d1865, d487, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11105 pattern childGuard
    simpa only [d1865, d487, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12295 (pattern : Twelve) (guard : d1865 pattern = 1) : d514 pattern ≤ (1 : Int) + d30 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d514, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12293 pattern childGuard
    simpa only [d514, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d514, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12294 pattern childGuard
    simpa only [d514, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12296 (pattern : Twelve) (guard : d1865 pattern = 1) : d515 pattern ≤ (1 : Int) + d35 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d515, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12281 pattern childGuard
    simpa only [d515, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d515, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12242 pattern childGuard
    simpa only [d515, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12297 (pattern : Twelve) (guard : d1865 pattern = 1) : d543 pattern ≤ (1 : Int) + d56 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d543, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12295 pattern childGuard
    simpa only [d543, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d543, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12296 pattern childGuard
    simpa only [d543, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12298 (pattern : Twelve) (guard : d1865 pattern = 1) : d509 pattern ≤ (1 : Int) + d34 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d509, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12233 pattern childGuard
    simpa only [d509, d34, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d509, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12260 pattern childGuard
    simpa only [d509, d34, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12299 (pattern : Twelve) (guard : d1865 pattern = 1) : d515 pattern ≤ (1 : Int) + d818 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d515, d818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12262 pattern childGuard
    simpa only [d515, d818, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d515, d818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12242 pattern childGuard
    simpa only [d515, d818, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12300 (pattern : Twelve) (guard : d1865 pattern = 1) : d544 pattern ≤ (1 : Int) + d826 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d544, d826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12298 pattern childGuard
    simpa only [d544, d826, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d544, d826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12299 pattern childGuard
    simpa only [d544, d826, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12301 (pattern : Twelve) (guard : d1865 pattern = 1) : d567 pattern ≤ (1 : Int) + d840 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d567, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12297 pattern childGuard
    simpa only [d567, d840, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d567, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12300 pattern childGuard
    simpa only [d567, d840, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12302 (pattern : Twelve) (guard : d1865 pattern = 1) : d515 pattern ≤ (1 : Int) + d36 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d515, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12233 pattern childGuard
    simpa only [d515, d36, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d515, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12242 pattern childGuard
    simpa only [d515, d36, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12303 (pattern : Twelve) (guard : d1865 pattern = 1) : d544 pattern ≤ (1 : Int) + d827 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d544, d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12298 pattern childGuard
    simpa only [d544, d827, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d544, d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12302 pattern childGuard
    simpa only [d544, d827, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12304 (pattern : Twelve) (guard : d1865 pattern = 1) : d568 pattern ≤ (1 : Int) + d841 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d568, d841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12303 pattern childGuard
    simpa only [d568, d841, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d568, d841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12274 pattern childGuard
    simpa only [d568, d841, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12305 (pattern : Twelve) (guard : d1865 pattern = 1) : d591 pattern ≤ (1 : Int) + d854 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d591, d854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12301 pattern childGuard
    simpa only [d591, d854, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d591, d854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12304 pattern childGuard
    simpa only [d591, d854, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12306 (pattern : Twelve) (guard : d1865 pattern = 1) : d607 pattern ≤ (1 : Int) + d861 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d607, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12291 pattern childGuard
    simpa only [d607, d861, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d607, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12305 pattern childGuard
    simpa only [d607, d861, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12307 (pattern : Twelve) (guard : d1865 pattern = 1) : d618 pattern ≤ (1 : Int) + d861 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12277 pattern childGuard
    simpa only [d618, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12306 pattern childGuard
    simpa only [d618, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12308 (pattern : Twelve) (guard : d0 pattern = 1) : d3 pattern ≤ (1 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c12309 (pattern : Twelve) (guard : d1865 pattern = 1) : d490 pattern ≤ (1 : Int) + d0 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11049 pattern childGuard
    simpa only [d1865, d490, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12308 pattern childGuard
    simpa only [d1865, d490, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12310 (pattern : Twelve) (guard : d0 pattern = 1) : d13 pattern ≤ (1 : Int) + d2 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c12311 (pattern : Twelve) (guard : d1865 pattern = 1) : d491 pattern ≤ (1 : Int) + d2 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11127 pattern childGuard
    simpa only [d1865, d491, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12310 pattern childGuard
    simpa only [d1865, d491, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12312 (pattern : Twelve) (guard : d1865 pattern = 1) : d516 pattern ≤ (1 : Int) + d30 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d516, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12309 pattern childGuard
    simpa only [d516, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d516, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12311 pattern childGuard
    simpa only [d516, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12313 (pattern : Twelve) (guard : d1865 pattern = 1) : d517 pattern ≤ (1 : Int) + d30 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d517, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12279 pattern childGuard
    simpa only [d517, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d517, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12294 pattern childGuard
    simpa only [d517, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12314 (pattern : Twelve) (guard : d1865 pattern = 1) : d545 pattern ≤ (1 : Int) + d30 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12312 pattern childGuard
    simpa only [d545, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12313 pattern childGuard
    simpa only [d545, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12315 (pattern : Twelve) (guard : d0 pattern = 1) : d159 pattern ≤ (1 : Int) + d7 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c12316 (pattern : Twelve) (guard : d1865 pattern = 1) : d488 pattern ≤ (1 : Int) + d17 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d488, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11049 pattern childGuard
    simpa only [d1865, d488, d17, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d488, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12315 pattern childGuard
    simpa only [d1865, d488, d17, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12317 (pattern : Twelve) (guard : d1865 pattern = 1) : d517 pattern ≤ (1 : Int) + d34 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d517, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12316 pattern childGuard
    simpa only [d517, d34, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d517, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12260 pattern childGuard
    simpa only [d517, d34, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12318 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (1 : Int) + d3 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c12319 (pattern : Twelve) (guard : d1865 pattern = 1) : d492 pattern ≤ (1 : Int) + d3 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11190 pattern childGuard
    simpa only [d1865, d492, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12318 pattern childGuard
    simpa only [d1865, d492, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
