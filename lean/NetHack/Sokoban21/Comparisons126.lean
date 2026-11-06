/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons125
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c17640 (pattern : Twelve) (guard : d1852 pattern = 1) : d1654 pattern ≤ (1 : Int) + d1648 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d1654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17638 pattern childGuard
    simpa only [d1852, d1654, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d1654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17639 pattern childGuard
    simpa only [d1852, d1654, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17641 (pattern : Twelve) (guard : d1852 pattern = 1) : d1659 pattern ≤ (1 : Int) + d3225 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1659, d3225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17640 pattern childGuard
    simpa only [d1659, d3225, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1659, d3225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11957 pattern childGuard
    simpa only [d1659, d3225, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17642 (pattern : Twelve) (guard : d1852 pattern = 1) : d1661 pattern ≤ (1 : Int) + d3226 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1661, d3226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17635 pattern childGuard
    simpa only [d1661, d3226, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1661, d3226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17641 pattern childGuard
    simpa only [d1661, d3226, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17643 (pattern : Twelve) (guard : d1852 pattern = 1) : d1662 pattern ≤ (1 : Int) + d3227 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1662, d3227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17631 pattern childGuard
    simpa only [d1662, d3227, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1662, d3227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17373 pattern childGuard
    simpa only [d1662, d3227, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17644 (pattern : Twelve) (guard : d1852 pattern = 1) : d1663 pattern ≤ (1 : Int) + d3228 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1663, d3228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17642 pattern childGuard
    simpa only [d1663, d3228, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1663, d3228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17643 pattern childGuard
    simpa only [d1663, d3228, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17645 (pattern : Twelve) (guard : d1852 pattern = 1) : d1664 pattern ≤ (1 : Int) + d3229 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1664, d3229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17632 pattern childGuard
    simpa only [d1664, d3229, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1664, d3229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17644 pattern childGuard
    simpa only [d1664, d3229, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17646 (pattern : Twelve) (guard : d1 pattern = 1) : d10 pattern ≤ (1 : Int) + d12 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d10, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17319 pattern childGuard
    simpa only [d10, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d10, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17364 pattern childGuard
    simpa only [d10, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17647 (pattern : Twelve) (guard : d1 pattern = 1) : d11 pattern ≤ (1 : Int) + d13 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17580 pattern childGuard
    simpa only [d11, d13, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11233 pattern childGuard
    simpa only [d11, d13, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17648 (pattern : Twelve) (guard : d1 pattern = 1) : d19 pattern ≤ (1 : Int) + d20 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d19, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17646 pattern childGuard
    simpa only [d19, d20, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d19, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17647 pattern childGuard
    simpa only [d19, d20, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17649 (pattern : Twelve) (guard : d1 pattern = 1) : d19 pattern ≤ (1 : Int) + d1644 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17621 pattern childGuard
    simpa only [d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17648 pattern childGuard
    simpa only [d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17650 (pattern : Twelve) (guard : d1852 pattern = 1) : d1668 pattern ≤ (1 : Int) + d1644 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d1668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17649 pattern childGuard
    simpa only [d1852, d1668, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d1668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17633 pattern childGuard
    simpa only [d1852, d1668, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17651 (pattern : Twelve) (guard : d1852 pattern = 1) : d1671 pattern ≤ (1 : Int) + d3224 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1671, d3224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17650 pattern childGuard
    simpa only [d1671, d3224, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1671, d3224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11943 pattern childGuard
    simpa only [d1671, d3224, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17652 (pattern : Twelve) (guard : d1852 pattern = 1) : d1674 pattern ≤ (1 : Int) + d3230 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1674, d3230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17651 pattern childGuard
    simpa only [d1674, d3230, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1674, d3230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17631 pattern childGuard
    simpa only [d1674, d3230, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17653 (pattern : Twelve) (guard : d1 pattern = 1) : d16 pattern ≤ (1 : Int) + d14 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d16, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17364 pattern childGuard
    simpa only [d16, d14, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d16, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11231 pattern childGuard
    simpa only [d16, d14, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17654 (pattern : Twelve) (guard : d1 pattern = 1) : d25 pattern ≤ (1 : Int) + d22 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d25, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17653 pattern childGuard
    simpa only [d25, d22, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d25, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11235 pattern childGuard
    simpa only [d25, d22, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17655 (pattern : Twelve) (guard : d1 pattern = 1) : d817 pattern ≤ (1 : Int) + d1665 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d817, d1665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17621 pattern childGuard
    simpa only [d817, d1665, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d817, d1665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17654 pattern childGuard
    simpa only [d817, d1665, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17656 (pattern : Twelve) (guard : d1 pattern = 1) : d817 pattern ≤ (1 : Int) + d1666 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17626 pattern childGuard
    simpa only [d1666, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17655 pattern childGuard
    simpa only [d1666, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17657 (pattern : Twelve) (guard : d0 pattern = 1) : d1666 pattern ≤ (1 : Int) + d1666 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c17658 (pattern : Twelve) (guard : d1852 pattern = 1) : d1669 pattern ≤ (1 : Int) + d1666 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d1669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17656 pattern childGuard
    simpa only [d1852, d1669, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d1669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17657 pattern childGuard
    simpa only [d1852, d1669, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17659 (pattern : Twelve) (guard : d1852 pattern = 1) : d1672 pattern ≤ (1 : Int) + d3231 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1672, d3231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17658 pattern childGuard
    simpa only [d1672, d3231, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1672, d3231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11949 pattern childGuard
    simpa only [d1672, d3231, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17660 (pattern : Twelve) (guard : d1 pattern = 1) : d821 pattern ≤ (1 : Int) + d128 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d821, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17625 pattern childGuard
    simpa only [d821, d128, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d821, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11285 pattern childGuard
    simpa only [d821, d128, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17661 (pattern : Twelve) (guard : d1 pattern = 1) : d42 pattern ≤ (1 : Int) + d183 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d42, d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17654 pattern childGuard
    simpa only [d42, d183, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d42, d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11282 pattern childGuard
    simpa only [d42, d183, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17662 (pattern : Twelve) (guard : d1 pattern = 1) : d1289 pattern ≤ (1 : Int) + d1667 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1289, d1667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17660 pattern childGuard
    simpa only [d1289, d1667, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1289, d1667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17661 pattern childGuard
    simpa only [d1289, d1667, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17663 (pattern : Twelve) (guard : d0 pattern = 1) : d1667 pattern ≤ (1 : Int) + d1667 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c17664 (pattern : Twelve) (guard : d1852 pattern = 1) : d1670 pattern ≤ (1 : Int) + d1667 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d1670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17662 pattern childGuard
    simpa only [d1852, d1670, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d1670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17663 pattern childGuard
    simpa only [d1852, d1670, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17665 (pattern : Twelve) (guard : d1852 pattern = 1) : d1673 pattern ≤ (1 : Int) + d3232 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1673, d3232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17664 pattern childGuard
    simpa only [d1673, d3232, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1673, d3232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11965 pattern childGuard
    simpa only [d1673, d3232, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17666 (pattern : Twelve) (guard : d1852 pattern = 1) : d1675 pattern ≤ (1 : Int) + d3233 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1675, d3233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17659 pattern childGuard
    simpa only [d1675, d3233, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1675, d3233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17665 pattern childGuard
    simpa only [d1675, d3233, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17667 (pattern : Twelve) (guard : d1852 pattern = 1) : d1676 pattern ≤ (1 : Int) + d3234 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1676, d3234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17666 pattern childGuard
    simpa only [d1676, d3234, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1676, d3234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17643 pattern childGuard
    simpa only [d1676, d3234, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17668 (pattern : Twelve) (guard : d1852 pattern = 1) : d1677 pattern ≤ (1 : Int) + d3235 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1677, d3235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17652 pattern childGuard
    simpa only [d1677, d3235, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1677, d3235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17667 pattern childGuard
    simpa only [d1677, d3235, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17669 (pattern : Twelve) (guard : d1852 pattern = 1) : d1678 pattern ≤ (1 : Int) + d3236 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1678, d3236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17645 pattern childGuard
    simpa only [d1678, d3236, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1678, d3236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17668 pattern childGuard
    simpa only [d1678, d3236, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17670 (pattern : Twelve) (guard : d0 pattern = 1) : d185 pattern ≤ (1 : Int) + d50 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c17671 (pattern : Twelve) (guard : d1852 pattern = 1) : d425 pattern ≤ (1 : Int) + d72 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d425, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11049 pattern childGuard
    simpa only [d1852, d425, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d425, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17670 pattern childGuard
    simpa only [d1852, d425, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17672 (pattern : Twelve) (guard : d0 pattern = 1) : d186 pattern ≤ (1 : Int) + d51 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c17673 (pattern : Twelve) (guard : d1852 pattern = 1) : d426 pattern ≤ (1 : Int) + d73 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d426, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11049 pattern childGuard
    simpa only [d1852, d426, d73, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d426, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17672 pattern childGuard
    simpa only [d1852, d426, d73, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17674 (pattern : Twelve) (guard : d1852 pattern = 1) : d444 pattern ≤ (1 : Int) + d91 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d444, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17671 pattern childGuard
    simpa only [d444, d91, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d444, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17673 pattern childGuard
    simpa only [d444, d91, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17675 (pattern : Twelve) (guard : d1 pattern = 1) : d52 pattern ≤ (1 : Int) + d52 pattern := by
  omega
theorem c17676 (pattern : Twelve) (guard : d0 pattern = 1) : d188 pattern ≤ (1 : Int) + d53 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c17677 (pattern : Twelve) (guard : d1852 pattern = 1) : d427 pattern ≤ (1 : Int) + d74 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d427, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17675 pattern childGuard
    simpa only [d1852, d427, d74, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d427, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17676 pattern childGuard
    simpa only [d1852, d427, d74, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17678 (pattern : Twelve) (guard : d1 pattern = 1) : d54 pattern ≤ (1 : Int) + d54 pattern := by
  omega
theorem c17679 (pattern : Twelve) (guard : d0 pattern = 1) : d189 pattern ≤ (1 : Int) + d55 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c17680 (pattern : Twelve) (guard : d1852 pattern = 1) : d428 pattern ≤ (1 : Int) + d75 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d428, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17678 pattern childGuard
    simpa only [d1852, d428, d75, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d428, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17679 pattern childGuard
    simpa only [d1852, d428, d75, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17681 (pattern : Twelve) (guard : d1852 pattern = 1) : d445 pattern ≤ (1 : Int) + d92 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d445, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17677 pattern childGuard
    simpa only [d445, d92, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d445, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17680 pattern childGuard
    simpa only [d445, d92, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17682 (pattern : Twelve) (guard : d1852 pattern = 1) : d455 pattern ≤ (1 : Int) + d102 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d455, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17674 pattern childGuard
    simpa only [d455, d102, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d455, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17681 pattern childGuard
    simpa only [d455, d102, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17683 (pattern : Twelve) (guard : d0 pattern = 1) : d188 pattern ≤ (1 : Int) + d50 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c17684 (pattern : Twelve) (guard : d1852 pattern = 1) : d429 pattern ≤ (1 : Int) + d72 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d429, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11049 pattern childGuard
    simpa only [d1852, d429, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d429, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17683 pattern childGuard
    simpa only [d1852, d429, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17685 (pattern : Twelve) (guard : d1852 pattern = 1) : d430 pattern ≤ (1 : Int) + d76 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d430, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11049 pattern childGuard
    simpa only [d1852, d430, d76, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d430, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17679 pattern childGuard
    simpa only [d1852, d430, d76, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17686 (pattern : Twelve) (guard : d1852 pattern = 1) : d446 pattern ≤ (1 : Int) + d93 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d446, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17684 pattern childGuard
    simpa only [d446, d93, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d446, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17685 pattern childGuard
    simpa only [d446, d93, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17687 (pattern : Twelve) (guard : d0 pattern = 1) : d191 pattern ≤ (1 : Int) + d57 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c17688 (pattern : Twelve) (guard : d1852 pattern = 1) : d431 pattern ≤ (1 : Int) + d77 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d431, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11744 pattern childGuard
    simpa only [d1852, d431, d77, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d431, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17687 pattern childGuard
    simpa only [d1852, d431, d77, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17689 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (1 : Int) + d55 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c17690 (pattern : Twelve) (guard : d1852 pattern = 1) : d432 pattern ≤ (1 : Int) + d78 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d432, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11744 pattern childGuard
    simpa only [d1852, d432, d78, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d432, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17689 pattern childGuard
    simpa only [d1852, d432, d78, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17691 (pattern : Twelve) (guard : d1852 pattern = 1) : d447 pattern ≤ (1 : Int) + d94 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d447, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17688 pattern childGuard
    simpa only [d447, d94, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d447, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17690 pattern childGuard
    simpa only [d447, d94, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17692 (pattern : Twelve) (guard : d1852 pattern = 1) : d456 pattern ≤ (1 : Int) + d103 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d456, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17686 pattern childGuard
    simpa only [d456, d103, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d456, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17691 pattern childGuard
    simpa only [d456, d103, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17693 (pattern : Twelve) (guard : d1852 pattern = 1) : d465 pattern ≤ (1 : Int) + d110 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d465, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17682 pattern childGuard
    simpa only [d465, d110, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d465, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17692 pattern childGuard
    simpa only [d465, d110, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17694 (pattern : Twelve) (guard : d0 pattern = 1) : d193 pattern ≤ (1 : Int) + d58 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c17695 (pattern : Twelve) (guard : d1852 pattern = 1) : d433 pattern ≤ (1 : Int) + d79 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d433, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11732 pattern childGuard
    simpa only [d1852, d433, d79, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d433, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17694 pattern childGuard
    simpa only [d1852, d433, d79, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17696 (pattern : Twelve) (guard : d0 pattern = 1) : d194 pattern ≤ (1 : Int) + d55 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c17697 (pattern : Twelve) (guard : d1852 pattern = 1) : d434 pattern ≤ (1 : Int) + d80 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d434, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11732 pattern childGuard
    simpa only [d1852, d434, d80, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d434, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17696 pattern childGuard
    simpa only [d1852, d434, d80, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17698 (pattern : Twelve) (guard : d1852 pattern = 1) : d448 pattern ≤ (1 : Int) + d95 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d448, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17695 pattern childGuard
    simpa only [d448, d95, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d448, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17697 pattern childGuard
    simpa only [d448, d95, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17699 (pattern : Twelve) (guard : d0 pattern = 1) : d196 pattern ≤ (1 : Int) + d60 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c17700 (pattern : Twelve) (guard : d1852 pattern = 1) : d435 pattern ≤ (1 : Int) + d81 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d435, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11755 pattern childGuard
    simpa only [d1852, d435, d81, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d435, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17699 pattern childGuard
    simpa only [d1852, d435, d81, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17701 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (1 : Int) + d61 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c17702 (pattern : Twelve) (guard : d1852 pattern = 1) : d436 pattern ≤ (1 : Int) + d82 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d436, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11755 pattern childGuard
    simpa only [d1852, d436, d82, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d436, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17701 pattern childGuard
    simpa only [d1852, d436, d82, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17703 (pattern : Twelve) (guard : d1852 pattern = 1) : d449 pattern ≤ (1 : Int) + d96 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d449, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17700 pattern childGuard
    simpa only [d449, d96, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d449, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17702 pattern childGuard
    simpa only [d449, d96, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17704 (pattern : Twelve) (guard : d1852 pattern = 1) : d457 pattern ≤ (1 : Int) + d104 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d457, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17698 pattern childGuard
    simpa only [d457, d104, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d457, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17703 pattern childGuard
    simpa only [d457, d104, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17705 (pattern : Twelve) (guard : d0 pattern = 1) : d196 pattern ≤ (1 : Int) + d57 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c17706 (pattern : Twelve) (guard : d1852 pattern = 1) : d437 pattern ≤ (1 : Int) + d77 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d437, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11744 pattern childGuard
    simpa only [d1852, d437, d77, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d437, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17705 pattern childGuard
    simpa only [d1852, d437, d77, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17707 (pattern : Twelve) (guard : d1852 pattern = 1) : d450 pattern ≤ (1 : Int) + d94 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d450, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17706 pattern childGuard
    simpa only [d450, d94, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d450, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17690 pattern childGuard
    simpa only [d450, d94, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17708 (pattern : Twelve) (guard : d1852 pattern = 1) : d458 pattern ≤ (1 : Int) + d105 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d458, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17707 pattern childGuard
    simpa only [d458, d105, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d458, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17373 pattern childGuard
    simpa only [d458, d105, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17709 (pattern : Twelve) (guard : d1852 pattern = 1) : d466 pattern ≤ (1 : Int) + d111 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d466, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17704 pattern childGuard
    simpa only [d466, d111, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d466, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17708 pattern childGuard
    simpa only [d466, d111, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17710 (pattern : Twelve) (guard : d1852 pattern = 1) : d471 pattern ≤ (1 : Int) + d114 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d471, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17693 pattern childGuard
    simpa only [d471, d114, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d471, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17709 pattern childGuard
    simpa only [d471, d114, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17711 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (1 : Int) + d50 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c17712 (pattern : Twelve) (guard : d1852 pattern = 1) : d438 pattern ≤ (1 : Int) + d72 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d438, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11049 pattern childGuard
    simpa only [d1852, d438, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d438, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17711 pattern childGuard
    simpa only [d1852, d438, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17713 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (1 : Int) + d51 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c17714 (pattern : Twelve) (guard : d1852 pattern = 1) : d438 pattern ≤ (1 : Int) + d73 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d438, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11049 pattern childGuard
    simpa only [d1852, d438, d73, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d438, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17713 pattern childGuard
    simpa only [d1852, d438, d73, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17715 (pattern : Twelve) (guard : d1852 pattern = 1) : d438 pattern ≤ (1 : Int) + d91 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17712 pattern childGuard
    simpa only [d91, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17714 pattern childGuard
    simpa only [d91, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17716 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (1 : Int) + d53 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c17717 (pattern : Twelve) (guard : d1852 pattern = 1) : d439 pattern ≤ (1 : Int) + d74 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d439, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17675 pattern childGuard
    simpa only [d1852, d439, d74, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d439, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17716 pattern childGuard
    simpa only [d1852, d439, d74, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17718 (pattern : Twelve) (guard : d1852 pattern = 1) : d440 pattern ≤ (1 : Int) + d75 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d440, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17678 pattern childGuard
    simpa only [d1852, d440, d75, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d440, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17689 pattern childGuard
    simpa only [d1852, d440, d75, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17719 (pattern : Twelve) (guard : d1852 pattern = 1) : d451 pattern ≤ (1 : Int) + d92 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d451, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17717 pattern childGuard
    simpa only [d451, d92, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d451, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17718 pattern childGuard
    simpa only [d451, d92, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17720 (pattern : Twelve) (guard : d1852 pattern = 1) : d459 pattern ≤ (1 : Int) + d102 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d459, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17715 pattern childGuard
    simpa only [d459, d102, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d459, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17719 pattern childGuard
    simpa only [d459, d102, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17721 (pattern : Twelve) (guard : d1852 pattern = 1) : d438 pattern ≤ (1 : Int) + d76 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d438, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11049 pattern childGuard
    simpa only [d1852, d438, d76, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d438, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17689 pattern childGuard
    simpa only [d1852, d438, d76, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17722 (pattern : Twelve) (guard : d1852 pattern = 1) : d438 pattern ≤ (1 : Int) + d93 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17712 pattern childGuard
    simpa only [d93, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17721 pattern childGuard
    simpa only [d93, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17723 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (1 : Int) + d57 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c17724 (pattern : Twelve) (guard : d1852 pattern = 1) : d432 pattern ≤ (1 : Int) + d77 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d432, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11744 pattern childGuard
    simpa only [d1852, d432, d77, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d432, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17723 pattern childGuard
    simpa only [d1852, d432, d77, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17725 (pattern : Twelve) (guard : d1852 pattern = 1) : d432 pattern ≤ (1 : Int) + d94 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17724 pattern childGuard
    simpa only [d94, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17690 pattern childGuard
    simpa only [d94, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17726 (pattern : Twelve) (guard : d1852 pattern = 1) : d460 pattern ≤ (1 : Int) + d103 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d460, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17722 pattern childGuard
    simpa only [d460, d103, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d460, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17725 pattern childGuard
    simpa only [d460, d103, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17727 (pattern : Twelve) (guard : d1852 pattern = 1) : d467 pattern ≤ (1 : Int) + d110 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d467, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17720 pattern childGuard
    simpa only [d467, d110, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d467, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17726 pattern childGuard
    simpa only [d467, d110, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17728 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (1 : Int) + d58 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c17729 (pattern : Twelve) (guard : d1852 pattern = 1) : d441 pattern ≤ (1 : Int) + d79 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d441, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11732 pattern childGuard
    simpa only [d1852, d441, d79, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d441, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17728 pattern childGuard
    simpa only [d1852, d441, d79, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17730 (pattern : Twelve) (guard : d1852 pattern = 1) : d441 pattern ≤ (1 : Int) + d80 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d441, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11732 pattern childGuard
    simpa only [d1852, d441, d80, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d441, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17689 pattern childGuard
    simpa only [d1852, d441, d80, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17731 (pattern : Twelve) (guard : d1852 pattern = 1) : d441 pattern ≤ (1 : Int) + d95 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17729 pattern childGuard
    simpa only [d95, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17730 pattern childGuard
    simpa only [d95, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17732 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (1 : Int) + d60 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c17733 (pattern : Twelve) (guard : d1852 pattern = 1) : d436 pattern ≤ (1 : Int) + d81 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d436, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11755 pattern childGuard
    simpa only [d1852, d436, d81, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d436, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17732 pattern childGuard
    simpa only [d1852, d436, d81, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17734 (pattern : Twelve) (guard : d1852 pattern = 1) : d436 pattern ≤ (1 : Int) + d96 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17733 pattern childGuard
    simpa only [d96, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17702 pattern childGuard
    simpa only [d96, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17735 (pattern : Twelve) (guard : d1852 pattern = 1) : d461 pattern ≤ (1 : Int) + d104 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d461, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17731 pattern childGuard
    simpa only [d461, d104, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d461, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17734 pattern childGuard
    simpa only [d461, d104, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17736 (pattern : Twelve) (guard : d1852 pattern = 1) : d462 pattern ≤ (1 : Int) + d105 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d462, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17725 pattern childGuard
    simpa only [d462, d105, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d462, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17373 pattern childGuard
    simpa only [d462, d105, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17737 (pattern : Twelve) (guard : d1852 pattern = 1) : d468 pattern ≤ (1 : Int) + d111 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d468, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17735 pattern childGuard
    simpa only [d468, d111, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d468, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17736 pattern childGuard
    simpa only [d468, d111, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17738 (pattern : Twelve) (guard : d1852 pattern = 1) : d472 pattern ≤ (1 : Int) + d114 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d472, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17727 pattern childGuard
    simpa only [d472, d114, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d472, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17737 pattern childGuard
    simpa only [d472, d114, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17739 (pattern : Twelve) (guard : d1852 pattern = 1) : d474 pattern ≤ (1 : Int) + d114 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17710 pattern childGuard
    simpa only [d474, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17738 pattern childGuard
    simpa only [d474, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17740 (pattern : Twelve) (guard : d1852 pattern = 1) : d475 pattern ≤ (1 : Int) + d114 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17739 pattern childGuard
    simpa only [d475, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17738 pattern childGuard
    simpa only [d475, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17741 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (1 : Int) + d129 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c17742 (pattern : Twelve) (guard : d1852 pattern = 1) : d438 pattern ≤ (1 : Int) + d136 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d438, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11049 pattern childGuard
    simpa only [d1852, d438, d136, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d438, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17741 pattern childGuard
    simpa only [d1852, d438, d136, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17743 (pattern : Twelve) (guard : d1852 pattern = 1) : d438 pattern ≤ (1 : Int) + d144 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17712 pattern childGuard
    simpa only [d144, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17742 pattern childGuard
    simpa only [d144, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17744 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (1 : Int) + d130 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c17745 (pattern : Twelve) (guard : d1852 pattern = 1) : d439 pattern ≤ (1 : Int) + d137 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d439, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17675 pattern childGuard
    simpa only [d1852, d439, d137, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d439, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17744 pattern childGuard
    simpa only [d1852, d439, d137, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17746 (pattern : Twelve) (guard : d1852 pattern = 1) : d432 pattern ≤ (1 : Int) + d138 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d432, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11744 pattern childGuard
    simpa only [d1852, d432, d138, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d432, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17741 pattern childGuard
    simpa only [d1852, d432, d138, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17747 (pattern : Twelve) (guard : d1852 pattern = 1) : d452 pattern ≤ (1 : Int) + d145 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d452, d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17745 pattern childGuard
    simpa only [d452, d145, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d452, d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17746 pattern childGuard
    simpa only [d452, d145, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17748 (pattern : Twelve) (guard : d1852 pattern = 1) : d463 pattern ≤ (1 : Int) + d149 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d463, d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17743 pattern childGuard
    simpa only [d463, d149, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d463, d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17747 pattern childGuard
    simpa only [d463, d149, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17749 (pattern : Twelve) (guard : d1852 pattern = 1) : d432 pattern ≤ (1 : Int) + d139 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d432, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11744 pattern childGuard
    simpa only [d1852, d432, d139, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d432, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17744 pattern childGuard
    simpa only [d1852, d432, d139, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17750 (pattern : Twelve) (guard : d1852 pattern = 1) : d432 pattern ≤ (1 : Int) + d146 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17749 pattern childGuard
    simpa only [d146, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17746 pattern childGuard
    simpa only [d146, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17751 (pattern : Twelve) (guard : d1852 pattern = 1) : d460 pattern ≤ (1 : Int) + d150 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d460, d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17743 pattern childGuard
    simpa only [d460, d150, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d460, d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17750 pattern childGuard
    simpa only [d460, d150, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17752 (pattern : Twelve) (guard : d1852 pattern = 1) : d469 pattern ≤ (1 : Int) + d153 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d469, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17748 pattern childGuard
    simpa only [d469, d153, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d469, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17751 pattern childGuard
    simpa only [d469, d153, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17753 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (1 : Int) + d131 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c17754 (pattern : Twelve) (guard : d1852 pattern = 1) : d441 pattern ≤ (1 : Int) + d140 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d441, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11732 pattern childGuard
    simpa only [d1852, d441, d140, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d441, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17753 pattern childGuard
    simpa only [d1852, d441, d140, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17755 (pattern : Twelve) (guard : d1 pattern = 1) : d132 pattern ≤ (1 : Int) + d132 pattern := by
  omega
theorem c17756 (pattern : Twelve) (guard : d1852 pattern = 1) : d442 pattern ≤ (1 : Int) + d141 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d442, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17755 pattern childGuard
    simpa only [d1852, d442, d141, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d442, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17741 pattern childGuard
    simpa only [d1852, d442, d141, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17757 (pattern : Twelve) (guard : d1852 pattern = 1) : d453 pattern ≤ (1 : Int) + d147 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d453, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17754 pattern childGuard
    simpa only [d453, d147, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d453, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17756 pattern childGuard
    simpa only [d453, d147, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17758 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (1 : Int) + d133 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c17759 (pattern : Twelve) (guard : d1852 pattern = 1) : d436 pattern ≤ (1 : Int) + d142 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d436, d142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11755 pattern childGuard
    simpa only [d1852, d436, d142, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d436, d142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17758 pattern childGuard
    simpa only [d1852, d436, d142, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17760 (pattern : Twelve) (guard : d1 pattern = 1) : d134 pattern ≤ (1 : Int) + d134 pattern := by
  omega
theorem c17761 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (1 : Int) + d135 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c17762 (pattern : Twelve) (guard : d1852 pattern = 1) : d443 pattern ≤ (1 : Int) + d143 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d443, d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17760 pattern childGuard
    simpa only [d1852, d443, d143, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d443, d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17761 pattern childGuard
    simpa only [d1852, d443, d143, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17763 (pattern : Twelve) (guard : d1852 pattern = 1) : d454 pattern ≤ (1 : Int) + d148 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d454, d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17759 pattern childGuard
    simpa only [d454, d148, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d454, d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17762 pattern childGuard
    simpa only [d454, d148, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17764 (pattern : Twelve) (guard : d1852 pattern = 1) : d464 pattern ≤ (1 : Int) + d151 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d464, d151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17757 pattern childGuard
    simpa only [d464, d151, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d464, d151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17763 pattern childGuard
    simpa only [d464, d151, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17765 (pattern : Twelve) (guard : d1852 pattern = 1) : d462 pattern ≤ (1 : Int) + d152 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d462, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17750 pattern childGuard
    simpa only [d462, d152, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d462, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17373 pattern childGuard
    simpa only [d462, d152, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17766 (pattern : Twelve) (guard : d1852 pattern = 1) : d470 pattern ≤ (1 : Int) + d154 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d470, d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17764 pattern childGuard
    simpa only [d470, d154, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d470, d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17765 pattern childGuard
    simpa only [d470, d154, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17767 (pattern : Twelve) (guard : d1852 pattern = 1) : d473 pattern ≤ (1 : Int) + d155 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d473, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17752 pattern childGuard
    simpa only [d473, d155, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d473, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17766 pattern childGuard
    simpa only [d473, d155, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17768 (pattern : Twelve) (guard : d1852 pattern = 1) : d476 pattern ≤ (1 : Int) + d156 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d476, d156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17740 pattern childGuard
    simpa only [d476, d156, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d476, d156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17767 pattern childGuard
    simpa only [d476, d156, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17769 (pattern : Twelve) (guard : d0 pattern = 1) : d908 pattern ≤ (1 : Int) + d825 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c17770 (pattern : Twelve) (guard : d1852 pattern = 1) : d1070 pattern ≤ (1 : Int) + d839 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d1070, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11054 pattern childGuard
    simpa only [d1852, d1070, d839, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d1070, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17769 pattern childGuard
    simpa only [d1852, d1070, d839, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17771 (pattern : Twelve) (guard : d1852 pattern = 1) : d1078 pattern ≤ (1 : Int) + d853 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1078, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11729 pattern childGuard
    simpa only [d1078, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1078, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17770 pattern childGuard
    simpa only [d1078, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17772 (pattern : Twelve) (guard : d1852 pattern = 1) : d1071 pattern ≤ (1 : Int) + d840 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d1071, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11744 pattern childGuard
    simpa only [d1852, d1071, d840, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d1071, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11735 pattern childGuard
    simpa only [d1852, d1071, d840, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17773 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (1 : Int) + d825 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c17774 (pattern : Twelve) (guard : d1852 pattern = 1) : d1072 pattern ≤ (1 : Int) + d841 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d1072, d841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11845 pattern childGuard
    simpa only [d1852, d1072, d841, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d1072, d841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17773 pattern childGuard
    simpa only [d1852, d1072, d841, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17775 (pattern : Twelve) (guard : d1852 pattern = 1) : d1079 pattern ≤ (1 : Int) + d854 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1079, d854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17772 pattern childGuard
    simpa only [d1079, d854, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1079, d854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17774 pattern childGuard
    simpa only [d1079, d854, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17776 (pattern : Twelve) (guard : d1852 pattern = 1) : d1088 pattern ≤ (1 : Int) + d861 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1088, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17771 pattern childGuard
    simpa only [d1088, d861, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1088, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17775 pattern childGuard
    simpa only [d1088, d861, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17777 (pattern : Twelve) (guard : d1852 pattern = 1) : d1073 pattern ≤ (1 : Int) + d839 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d1073, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11054 pattern childGuard
    simpa only [d1852, d1073, d839, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d1073, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17773 pattern childGuard
    simpa only [d1852, d1073, d839, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17778 (pattern : Twelve) (guard : d1852 pattern = 1) : d1080 pattern ≤ (1 : Int) + d853 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1080, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11741 pattern childGuard
    simpa only [d1080, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1080, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17777 pattern childGuard
    simpa only [d1080, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17779 (pattern : Twelve) (guard : d1852 pattern = 1) : d1081 pattern ≤ (1 : Int) + d854 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1081, d854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11746 pattern childGuard
    simpa only [d1081, d854, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1081, d854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17774 pattern childGuard
    simpa only [d1081, d854, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
