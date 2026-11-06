/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons118
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c16660 (pattern : Twelve) (guard : d1848 pattern = 1) : d91 pattern ≤ (0 : Int) + d2283 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d91, d2283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16647 pattern childGuard
    simpa only [d91, d2283, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d91, d2283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16659 pattern childGuard
    simpa only [d91, d2283, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16661 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (0 : Int) + d3 pattern := by
  change (0 : Int) ≤ (0 : Int) + 3
  decide
theorem c16662 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (0 : Int) + d5 pattern := by
  change (0 : Int) ≤ (0 : Int) + 5
  decide
theorem c16663 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (0 : Int) + d12 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16661 pattern childGuard
    simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16662 pattern childGuard
    simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16664 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (0 : Int) + d4 pattern := by
  change (0 : Int) ≤ (0 : Int) + 4
  decide
theorem c16665 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (0 : Int) + d13 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16664 pattern childGuard
    simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16652 pattern childGuard
    simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16666 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (0 : Int) + d20 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16663 pattern childGuard
    simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16665 pattern childGuard
    simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16667 (pattern : Twelve) (guard : d1848 pattern = 1) : d31 pattern ≤ (0 : Int) + d20 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16666 pattern childGuard
    simpa only [d1848, d31, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11706 pattern childGuard
    simpa only [d1848, d31, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16668 (pattern : Twelve) (guard : d1848 pattern = 1) : d52 pattern ≤ (0 : Int) + d3036 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d52, d3036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11483 pattern childGuard
    simpa only [d52, d3036, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d52, d3036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16667 pattern childGuard
    simpa only [d52, d3036, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16669 (pattern : Twelve) (guard : d1 pattern = 1) : d7 pattern ≤ (0 : Int) + d14 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16662 pattern childGuard
    simpa only [d7, d14, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16654 pattern childGuard
    simpa only [d7, d14, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16670 (pattern : Twelve) (guard : d1 pattern = 1) : d17 pattern ≤ (0 : Int) + d21 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16665 pattern childGuard
    simpa only [d17, d21, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16669 pattern childGuard
    simpa only [d17, d21, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16671 (pattern : Twelve) (guard : d1848 pattern = 1) : d32 pattern ≤ (0 : Int) + d21 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16670 pattern childGuard
    simpa only [d1848, d32, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11710 pattern childGuard
    simpa only [d1848, d32, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16672 (pattern : Twelve) (guard : d1848 pattern = 1) : d53 pattern ≤ (0 : Int) + d3037 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d53, d3037, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11483 pattern childGuard
    simpa only [d53, d3037, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d53, d3037, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16671 pattern childGuard
    simpa only [d53, d3037, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16673 (pattern : Twelve) (guard : d1848 pattern = 1) : d74 pattern ≤ (0 : Int) + d3038 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d74, d3038, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16668 pattern childGuard
    simpa only [d74, d3038, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d74, d3038, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16672 pattern childGuard
    simpa only [d74, d3038, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16674 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (0 : Int) + d14 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16662 pattern childGuard
    simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16652 pattern childGuard
    simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16675 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (0 : Int) + d22 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16674 pattern childGuard
    simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16652 pattern childGuard
    simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16676 (pattern : Twelve) (guard : d0 pattern = 1) : d22 pattern ≤ (0 : Int) + d22 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c16677 (pattern : Twelve) (guard : d1848 pattern = 1) : d33 pattern ≤ (0 : Int) + d22 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16675 pattern childGuard
    simpa only [d1848, d33, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16676 pattern childGuard
    simpa only [d1848, d33, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16678 (pattern : Twelve) (guard : d1848 pattern = 1) : d54 pattern ≤ (0 : Int) + d3039 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d54, d3039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11483 pattern childGuard
    simpa only [d54, d3039, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d54, d3039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16677 pattern childGuard
    simpa only [d54, d3039, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16679 (pattern : Twelve) (guard : d1848 pattern = 1) : d55 pattern ≤ (0 : Int) + d2284 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d55, d2284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11577 pattern childGuard
    simpa only [d55, d2284, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d55, d2284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16657 pattern childGuard
    simpa only [d55, d2284, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16680 (pattern : Twelve) (guard : d1848 pattern = 1) : d75 pattern ≤ (0 : Int) + d3040 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d75, d3040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16678 pattern childGuard
    simpa only [d75, d3040, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d75, d3040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16679 pattern childGuard
    simpa only [d75, d3040, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16681 (pattern : Twelve) (guard : d1848 pattern = 1) : d92 pattern ≤ (0 : Int) + d3041 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d92, d3041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16673 pattern childGuard
    simpa only [d92, d3041, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d92, d3041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16680 pattern childGuard
    simpa only [d92, d3041, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16682 (pattern : Twelve) (guard : d1848 pattern = 1) : d102 pattern ≤ (0 : Int) + d3042 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d102, d3042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16660 pattern childGuard
    simpa only [d102, d3042, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d102, d3042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16681 pattern childGuard
    simpa only [d102, d3042, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16683 (pattern : Twelve) (guard : d1848 pattern = 1) : d76 pattern ≤ (0 : Int) + d2285 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d76, d2285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1560 pattern childGuard
    simpa only [d76, d2285, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d76, d2285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16679 pattern childGuard
    simpa only [d76, d2285, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16684 (pattern : Twelve) (guard : d1848 pattern = 1) : d93 pattern ≤ (0 : Int) + d2286 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d93, d2286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16647 pattern childGuard
    simpa only [d93, d2286, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d93, d2286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16683 pattern childGuard
    simpa only [d93, d2286, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16685 (pattern : Twelve) (guard : d1848 pattern = 1) : d35 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16652 pattern childGuard
    simpa only [d1848, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d1848, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16686 (pattern : Twelve) (guard : d1848 pattern = 1) : d56 pattern ≤ (0 : Int) + d3043 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d56, d3043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11483 pattern childGuard
    simpa only [d56, d3043, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d56, d3043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16685 pattern childGuard
    simpa only [d56, d3043, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16687 (pattern : Twelve) (guard : d1 pattern = 1) : d7 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16652 pattern childGuard
    simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16654 pattern childGuard
    simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16688 (pattern : Twelve) (guard : d1 pattern = 1) : d17 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16652 pattern childGuard
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16687 pattern childGuard
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16689 (pattern : Twelve) (guard : d1848 pattern = 1) : d36 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16688 pattern childGuard
    simpa only [d1848, d36, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d1848, d36, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16690 (pattern : Twelve) (guard : d1848 pattern = 1) : d57 pattern ≤ (0 : Int) + d3043 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d57, d3043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11483 pattern childGuard
    simpa only [d57, d3043, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d57, d3043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16689 pattern childGuard
    simpa only [d57, d3043, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16691 (pattern : Twelve) (guard : d1848 pattern = 1) : d77 pattern ≤ (0 : Int) + d3043 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16686 pattern childGuard
    simpa only [d77, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16690 pattern childGuard
    simpa only [d77, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16692 (pattern : Twelve) (guard : d1848 pattern = 1) : d78 pattern ≤ (0 : Int) + d3044 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d78, d3044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16686 pattern childGuard
    simpa only [d78, d3044, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d78, d3044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16679 pattern childGuard
    simpa only [d78, d3044, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16693 (pattern : Twelve) (guard : d1848 pattern = 1) : d94 pattern ≤ (0 : Int) + d3045 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d94, d3045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16691 pattern childGuard
    simpa only [d94, d3045, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d94, d3045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16692 pattern childGuard
    simpa only [d94, d3045, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16694 (pattern : Twelve) (guard : d1848 pattern = 1) : d103 pattern ≤ (0 : Int) + d3046 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d103, d3046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16684 pattern childGuard
    simpa only [d103, d3046, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d103, d3046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16693 pattern childGuard
    simpa only [d103, d3046, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16695 (pattern : Twelve) (guard : d1848 pattern = 1) : d110 pattern ≤ (0 : Int) + d3047 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d110, d3047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16682 pattern childGuard
    simpa only [d110, d3047, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d110, d3047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16694 pattern childGuard
    simpa only [d110, d3047, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16696 (pattern : Twelve) (guard : d1 pattern = 1) : d7 pattern ≤ (0 : Int) + d3 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16661 pattern childGuard
    simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10867 pattern childGuard
    simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16697 (pattern : Twelve) (guard : d1 pattern = 1) : d17 pattern ≤ (0 : Int) + d3 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16661 pattern childGuard
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16696 pattern childGuard
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16698 (pattern : Twelve) (guard : d0 pattern = 1) : d3 pattern ≤ (0 : Int) + d3 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c16699 (pattern : Twelve) (guard : d1848 pattern = 1) : d37 pattern ≤ (0 : Int) + d3 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16697 pattern childGuard
    simpa only [d1848, d37, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16698 pattern childGuard
    simpa only [d1848, d37, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16700 (pattern : Twelve) (guard : d1848 pattern = 1) : d58 pattern ≤ (0 : Int) + d2427 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d58, d2427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11483 pattern childGuard
    simpa only [d58, d2427, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d58, d2427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16699 pattern childGuard
    simpa only [d58, d2427, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16701 (pattern : Twelve) (guard : d1848 pattern = 1) : d79 pattern ≤ (0 : Int) + d3048 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d79, d3048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11483 pattern childGuard
    simpa only [d79, d3048, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d79, d3048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16700 pattern childGuard
    simpa only [d79, d3048, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16702 (pattern : Twelve) (guard : d1848 pattern = 1) : d80 pattern ≤ (0 : Int) + d2288 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d80, d2288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11483 pattern childGuard
    simpa only [d80, d2288, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d80, d2288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16679 pattern childGuard
    simpa only [d80, d2288, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16703 (pattern : Twelve) (guard : d1848 pattern = 1) : d95 pattern ≤ (0 : Int) + d3049 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d95, d3049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16701 pattern childGuard
    simpa only [d95, d3049, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d95, d3049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16702 pattern childGuard
    simpa only [d95, d3049, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16704 (pattern : Twelve) (guard : d0 pattern = 1) : d4 pattern ≤ (0 : Int) + d4 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c16705 (pattern : Twelve) (guard : d1848 pattern = 1) : d38 pattern ≤ (0 : Int) + d4 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10874 pattern childGuard
    simpa only [d1848, d38, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16704 pattern childGuard
    simpa only [d1848, d38, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16706 (pattern : Twelve) (guard : d1848 pattern = 1) : d39 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14969 pattern childGuard
    simpa only [d1848, d39, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d1848, d39, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16707 (pattern : Twelve) (guard : d1848 pattern = 1) : d59 pattern ≤ (0 : Int) + d3050 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d59, d3050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16705 pattern childGuard
    simpa only [d59, d3050, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d59, d3050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16706 pattern childGuard
    simpa only [d59, d3050, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16708 (pattern : Twelve) (guard : d1848 pattern = 1) : d40 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15043 pattern childGuard
    simpa only [d1848, d40, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d1848, d40, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16709 (pattern : Twelve) (guard : d1848 pattern = 1) : d60 pattern ≤ (0 : Int) + d3050 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d60, d3050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16705 pattern childGuard
    simpa only [d60, d3050, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d60, d3050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16708 pattern childGuard
    simpa only [d60, d3050, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16710 (pattern : Twelve) (guard : d1848 pattern = 1) : d81 pattern ≤ (0 : Int) + d3050 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16707 pattern childGuard
    simpa only [d81, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16709 pattern childGuard
    simpa only [d81, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16711 (pattern : Twelve) (guard : d0 pattern = 1) : d24 pattern ≤ (0 : Int) + d24 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c16712 (pattern : Twelve) (guard : d1848 pattern = 1) : d41 pattern ≤ (0 : Int) + d24 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10886 pattern childGuard
    simpa only [d1848, d41, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16711 pattern childGuard
    simpa only [d1848, d41, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16713 (pattern : Twelve) (guard : d1848 pattern = 1) : d42 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15097 pattern childGuard
    simpa only [d1848, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d1848, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16714 (pattern : Twelve) (guard : d1848 pattern = 1) : d61 pattern ≤ (0 : Int) + d3051 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d61, d3051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16712 pattern childGuard
    simpa only [d61, d3051, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d61, d3051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16713 pattern childGuard
    simpa only [d61, d3051, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16715 (pattern : Twelve) (guard : d1848 pattern = 1) : d82 pattern ≤ (0 : Int) + d3052 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d82, d3052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16707 pattern childGuard
    simpa only [d82, d3052, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d82, d3052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16714 pattern childGuard
    simpa only [d82, d3052, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16716 (pattern : Twelve) (guard : d1848 pattern = 1) : d96 pattern ≤ (0 : Int) + d3053 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d96, d3053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16710 pattern childGuard
    simpa only [d96, d3053, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d96, d3053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16715 pattern childGuard
    simpa only [d96, d3053, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16717 (pattern : Twelve) (guard : d1848 pattern = 1) : d104 pattern ≤ (0 : Int) + d3054 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d104, d3054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16703 pattern childGuard
    simpa only [d104, d3054, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d104, d3054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16716 pattern childGuard
    simpa only [d104, d3054, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16718 (pattern : Twelve) (guard : d1848 pattern = 1) : d105 pattern ≤ (0 : Int) + d3055 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d105, d3055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16693 pattern childGuard
    simpa only [d105, d3055, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d105, d3055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4269 pattern childGuard
    simpa only [d105, d3055, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16719 (pattern : Twelve) (guard : d1848 pattern = 1) : d111 pattern ≤ (0 : Int) + d3056 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d111, d3056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16717 pattern childGuard
    simpa only [d111, d3056, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d111, d3056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16718 pattern childGuard
    simpa only [d111, d3056, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16720 (pattern : Twelve) (guard : d1848 pattern = 1) : d114 pattern ≤ (0 : Int) + d3057 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d114, d3057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16695 pattern childGuard
    simpa only [d114, d3057, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d114, d3057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16719 pattern childGuard
    simpa only [d114, d3057, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16721 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (0 : Int) + d16 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10863 pattern childGuard
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16664 pattern childGuard
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16722 (pattern : Twelve) (guard : d1 pattern = 1) : d1 pattern ≤ (0 : Int) + d5 pattern := by
  change (1 : Int) ≤ (0 : Int) + 5
  decide
theorem c16723 (pattern : Twelve) (guard : d1 pattern = 1) : d7 pattern ≤ (0 : Int) + d12 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16661 pattern childGuard
    simpa only [d7, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16722 pattern childGuard
    simpa only [d7, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16724 (pattern : Twelve) (guard : d1 pattern = 1) : d17 pattern ≤ (0 : Int) + d25 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16721 pattern childGuard
    simpa only [d17, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16723 pattern childGuard
    simpa only [d17, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16725 (pattern : Twelve) (guard : d1848 pattern = 1) : d120 pattern ≤ (0 : Int) + d25 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16724 pattern childGuard
    simpa only [d1848, d120, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11654 pattern childGuard
    simpa only [d1848, d120, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16726 (pattern : Twelve) (guard : d1848 pattern = 1) : d129 pattern ≤ (0 : Int) + d1690 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d129, d1690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16725 pattern childGuard
    simpa only [d129, d1690, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d129, d1690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16657 pattern childGuard
    simpa only [d129, d1690, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16727 (pattern : Twelve) (guard : d1848 pattern = 1) : d136 pattern ≤ (0 : Int) + d3058 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d136, d3058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1560 pattern childGuard
    simpa only [d136, d3058, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d136, d3058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16726 pattern childGuard
    simpa only [d136, d3058, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16728 (pattern : Twelve) (guard : d1848 pattern = 1) : d144 pattern ≤ (0 : Int) + d3059 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d144, d3059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16647 pattern childGuard
    simpa only [d144, d3059, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d144, d3059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16727 pattern childGuard
    simpa only [d144, d3059, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16729 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (0 : Int) + d9 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10863 pattern childGuard
    simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16661 pattern childGuard
    simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16730 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (0 : Int) + d23 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10863 pattern childGuard
    simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16729 pattern childGuard
    simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16731 (pattern : Twelve) (guard : d1848 pattern = 1) : d121 pattern ≤ (0 : Int) + d23 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16730 pattern childGuard
    simpa only [d1848, d121, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11576 pattern childGuard
    simpa only [d1848, d121, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16732 (pattern : Twelve) (guard : d1848 pattern = 1) : d130 pattern ≤ (0 : Int) + d2284 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d130, d2284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16731 pattern childGuard
    simpa only [d130, d2284, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d130, d2284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16689 pattern childGuard
    simpa only [d130, d2284, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16733 (pattern : Twelve) (guard : d1848 pattern = 1) : d137 pattern ≤ (0 : Int) + d3060 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d137, d3060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16668 pattern childGuard
    simpa only [d137, d3060, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d137, d3060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16732 pattern childGuard
    simpa only [d137, d3060, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16734 (pattern : Twelve) (guard : d1848 pattern = 1) : d138 pattern ≤ (0 : Int) + d3061 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d138, d3061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16686 pattern childGuard
    simpa only [d138, d3061, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d138, d3061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16726 pattern childGuard
    simpa only [d138, d3061, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16735 (pattern : Twelve) (guard : d1848 pattern = 1) : d145 pattern ≤ (0 : Int) + d3062 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d145, d3062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16733 pattern childGuard
    simpa only [d145, d3062, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d145, d3062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16734 pattern childGuard
    simpa only [d145, d3062, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16736 (pattern : Twelve) (guard : d1848 pattern = 1) : d149 pattern ≤ (0 : Int) + d3063 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d149, d3063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16728 pattern childGuard
    simpa only [d149, d3063, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d149, d3063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16735 pattern childGuard
    simpa only [d149, d3063, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16737 (pattern : Twelve) (guard : d1848 pattern = 1) : d139 pattern ≤ (0 : Int) + d3044 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d139, d3044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16686 pattern childGuard
    simpa only [d139, d3044, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d139, d3044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16732 pattern childGuard
    simpa only [d139, d3044, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16738 (pattern : Twelve) (guard : d1848 pattern = 1) : d146 pattern ≤ (0 : Int) + d3064 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d146, d3064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16737 pattern childGuard
    simpa only [d146, d3064, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d146, d3064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16734 pattern childGuard
    simpa only [d146, d3064, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16739 (pattern : Twelve) (guard : d1848 pattern = 1) : d150 pattern ≤ (0 : Int) + d3065 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d150, d3065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16728 pattern childGuard
    simpa only [d150, d3065, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d150, d3065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16738 pattern childGuard
    simpa only [d150, d3065, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16740 (pattern : Twelve) (guard : d1848 pattern = 1) : d153 pattern ≤ (0 : Int) + d3066 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d153, d3066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16736 pattern childGuard
    simpa only [d153, d3066, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d153, d3066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16739 pattern childGuard
    simpa only [d153, d3066, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16741 (pattern : Twelve) (guard : d1 pattern = 1) : d1 pattern ≤ (0 : Int) + d4 pattern := by
  change (1 : Int) ≤ (0 : Int) + 4
  decide
theorem c16742 (pattern : Twelve) (guard : d1 pattern = 1) : d7 pattern ≤ (0 : Int) + d4 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16664 pattern childGuard
    simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16741 pattern childGuard
    simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16743 (pattern : Twelve) (guard : d1 pattern = 1) : d17 pattern ≤ (0 : Int) + d4 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16664 pattern childGuard
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16742 pattern childGuard
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16744 (pattern : Twelve) (guard : d1848 pattern = 1) : d122 pattern ≤ (0 : Int) + d4 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16743 pattern childGuard
    simpa only [d1848, d122, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16704 pattern childGuard
    simpa only [d1848, d122, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16745 (pattern : Twelve) (guard : d1848 pattern = 1) : d131 pattern ≤ (0 : Int) + d3067 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d131, d3067, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16731 pattern childGuard
    simpa only [d131, d3067, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d131, d3067, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16744 pattern childGuard
    simpa only [d131, d3067, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16746 (pattern : Twelve) (guard : d1848 pattern = 1) : d140 pattern ≤ (0 : Int) + d3068 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d140, d3068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11483 pattern childGuard
    simpa only [d140, d3068, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d140, d3068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16745 pattern childGuard
    simpa only [d140, d3068, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16747 (pattern : Twelve) (guard : d1848 pattern = 1) : d123 pattern ≤ (0 : Int) + d3 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16661 pattern childGuard
    simpa only [d1848, d123, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16698 pattern childGuard
    simpa only [d1848, d123, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16748 (pattern : Twelve) (guard : d1848 pattern = 1) : d132 pattern ≤ (0 : Int) + d2427 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d132, d2427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11483 pattern childGuard
    simpa only [d132, d2427, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d132, d2427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16747 pattern childGuard
    simpa only [d132, d2427, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16749 (pattern : Twelve) (guard : d1848 pattern = 1) : d141 pattern ≤ (0 : Int) + d3069 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d141, d3069, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16748 pattern childGuard
    simpa only [d141, d3069, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d141, d3069, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16726 pattern childGuard
    simpa only [d141, d3069, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16750 (pattern : Twelve) (guard : d1848 pattern = 1) : d147 pattern ≤ (0 : Int) + d3070 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d147, d3070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16746 pattern childGuard
    simpa only [d147, d3070, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d147, d3070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16749 pattern childGuard
    simpa only [d147, d3070, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16751 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (0 : Int) + d5 pattern := by
  change (2 : Int) ≤ (0 : Int) + 5
  decide
theorem c16752 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (0 : Int) + d14 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16751 pattern childGuard
    simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14969 pattern childGuard
    simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16753 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (0 : Int) + d118 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16751 pattern childGuard
    simpa only [d118, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16752 pattern childGuard
    simpa only [d118, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16754 (pattern : Twelve) (guard : d0 pattern = 1) : d118 pattern ≤ (0 : Int) + d118 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c16755 (pattern : Twelve) (guard : d1848 pattern = 1) : d124 pattern ≤ (0 : Int) + d118 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16753 pattern childGuard
    simpa only [d1848, d124, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16754 pattern childGuard
    simpa only [d1848, d124, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16756 (pattern : Twelve) (guard : d1 pattern = 1) : d117 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15041 pattern childGuard
    simpa only [d117, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10944 pattern childGuard
    simpa only [d117, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16757 (pattern : Twelve) (guard : d1 pattern = 1) : d119 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15041 pattern childGuard
    simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16756 pattern childGuard
    simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16758 (pattern : Twelve) (guard : d1848 pattern = 1) : d125 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16757 pattern childGuard
    simpa only [d1848, d125, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d1848, d125, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16759 (pattern : Twelve) (guard : d1848 pattern = 1) : d133 pattern ≤ (0 : Int) + d3071 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d133, d3071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16755 pattern childGuard
    simpa only [d133, d3071, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d133, d3071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16758 pattern childGuard
    simpa only [d133, d3071, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16760 (pattern : Twelve) (guard : d1848 pattern = 1) : d142 pattern ≤ (0 : Int) + d3072 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d142, d3072, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16707 pattern childGuard
    simpa only [d142, d3072, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d142, d3072, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16759 pattern childGuard
    simpa only [d142, d3072, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16761 (pattern : Twelve) (guard : d0 pattern = 1) : d5 pattern ≤ (0 : Int) + d5 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c16762 (pattern : Twelve) (guard : d1848 pattern = 1) : d126 pattern ≤ (0 : Int) + d5 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16751 pattern childGuard
    simpa only [d1848, d126, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16761 pattern childGuard
    simpa only [d1848, d126, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16763 (pattern : Twelve) (guard : d1848 pattern = 1) : d47 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15041 pattern childGuard
    simpa only [d1848, d47, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d1848, d47, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16764 (pattern : Twelve) (guard : d1848 pattern = 1) : d134 pattern ≤ (0 : Int) + d3073 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d134, d3073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16762 pattern childGuard
    simpa only [d134, d3073, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d134, d3073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16763 pattern childGuard
    simpa only [d134, d3073, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16765 (pattern : Twelve) (guard : d1 pattern = 1) : d23 pattern ≤ (0 : Int) + d22 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16752 pattern childGuard
    simpa only [d23, d22, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15042 pattern childGuard
    simpa only [d23, d22, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16766 (pattern : Twelve) (guard : d1848 pattern = 1) : d127 pattern ≤ (0 : Int) + d22 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16765 pattern childGuard
    simpa only [d1848, d127, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16676 pattern childGuard
    simpa only [d1848, d127, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16767 (pattern : Twelve) (guard : d1 pattern = 1) : d20 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15096 pattern childGuard
    simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11032 pattern childGuard
    simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16768 (pattern : Twelve) (guard : d1848 pattern = 1) : d128 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16767 pattern childGuard
    simpa only [d1848, d128, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d1848, d128, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16769 (pattern : Twelve) (guard : d1848 pattern = 1) : d135 pattern ≤ (0 : Int) + d3074 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d135, d3074, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16766 pattern childGuard
    simpa only [d135, d3074, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d135, d3074, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16768 pattern childGuard
    simpa only [d135, d3074, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16770 (pattern : Twelve) (guard : d1848 pattern = 1) : d143 pattern ≤ (0 : Int) + d3075 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d143, d3075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16764 pattern childGuard
    simpa only [d143, d3075, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d143, d3075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16769 pattern childGuard
    simpa only [d143, d3075, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16771 (pattern : Twelve) (guard : d1848 pattern = 1) : d148 pattern ≤ (0 : Int) + d3076 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d148, d3076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16760 pattern childGuard
    simpa only [d148, d3076, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d148, d3076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16770 pattern childGuard
    simpa only [d148, d3076, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16772 (pattern : Twelve) (guard : d1848 pattern = 1) : d151 pattern ≤ (0 : Int) + d3077 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d151, d3077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16750 pattern childGuard
    simpa only [d151, d3077, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d151, d3077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16771 pattern childGuard
    simpa only [d151, d3077, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16773 (pattern : Twelve) (guard : d1848 pattern = 1) : d152 pattern ≤ (0 : Int) + d3078 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d152, d3078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16738 pattern childGuard
    simpa only [d152, d3078, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d152, d3078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4269 pattern childGuard
    simpa only [d152, d3078, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16774 (pattern : Twelve) (guard : d1848 pattern = 1) : d154 pattern ≤ (0 : Int) + d3079 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d154, d3079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16772 pattern childGuard
    simpa only [d154, d3079, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d154, d3079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16773 pattern childGuard
    simpa only [d154, d3079, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16775 (pattern : Twelve) (guard : d1848 pattern = 1) : d155 pattern ≤ (0 : Int) + d3080 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d155, d3080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16740 pattern childGuard
    simpa only [d155, d3080, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d155, d3080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16774 pattern childGuard
    simpa only [d155, d3080, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16776 (pattern : Twelve) (guard : d1848 pattern = 1) : d156 pattern ≤ (0 : Int) + d3081 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d156, d3081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16720 pattern childGuard
    simpa only [d156, d3081, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d156, d3081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16775 pattern childGuard
    simpa only [d156, d3081, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16777 (pattern : Twelve) (guard : d1848 pattern = 1) : d824 pattern ≤ (0 : Int) + d1 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11445 pattern childGuard
    simpa only [d824, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11555 pattern childGuard
    simpa only [d824, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16778 (pattern : Twelve) (guard : d1848 pattern = 1) : d838 pattern ≤ (0 : Int) + d1859 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d838, d1859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1560 pattern childGuard
    simpa only [d838, d1859, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d838, d1859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16777 pattern childGuard
    simpa only [d838, d1859, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16779 (pattern : Twelve) (guard : d1848 pattern = 1) : d825 pattern ≤ (0 : Int) + d1690 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d825, d1690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11655 pattern childGuard
    simpa only [d825, d1690, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d825, d1690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16713 pattern childGuard
    simpa only [d825, d1690, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16780 (pattern : Twelve) (guard : d1848 pattern = 1) : d839 pattern ≤ (0 : Int) + d2291 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d839, d2291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1670 pattern childGuard
    simpa only [d839, d2291, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d839, d2291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16779 pattern childGuard
    simpa only [d839, d2291, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16781 (pattern : Twelve) (guard : d1848 pattern = 1) : d853 pattern ≤ (0 : Int) + d2292 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d853, d2292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16778 pattern childGuard
    simpa only [d853, d2292, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d853, d2292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16780 pattern childGuard
    simpa only [d853, d2292, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16782 (pattern : Twelve) (guard : d1 pattern = 1) : d814 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16687 pattern childGuard
    simpa only [d814, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16654 pattern childGuard
    simpa only [d814, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16783 (pattern : Twelve) (guard : d1848 pattern = 1) : d818 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16782 pattern childGuard
    simpa only [d1848, d818, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d1848, d818, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16784 (pattern : Twelve) (guard : d1848 pattern = 1) : d826 pattern ≤ (0 : Int) + d2284 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d826, d2284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11577 pattern childGuard
    simpa only [d826, d2284, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d826, d2284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16783 pattern childGuard
    simpa only [d826, d2284, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16785 (pattern : Twelve) (guard : d1848 pattern = 1) : d840 pattern ≤ (0 : Int) + d3044 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d840, d3044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16686 pattern childGuard
    simpa only [d840, d3044, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d840, d3044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16784 pattern childGuard
    simpa only [d840, d3044, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16786 (pattern : Twelve) (guard : d1848 pattern = 1) : d827 pattern ≤ (0 : Int) + d2284 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d827, d2284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11577 pattern childGuard
    simpa only [d827, d2284, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d827, d2284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16689 pattern childGuard
    simpa only [d827, d2284, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16787 (pattern : Twelve) (guard : d1848 pattern = 1) : d841 pattern ≤ (0 : Int) + d3082 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d841, d3082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16786 pattern childGuard
    simpa only [d841, d3082, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d841, d3082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16779 pattern childGuard
    simpa only [d841, d3082, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16788 (pattern : Twelve) (guard : d1848 pattern = 1) : d854 pattern ≤ (0 : Int) + d3083 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d854, d3083, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16785 pattern childGuard
    simpa only [d854, d3083, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d854, d3083, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16787 pattern childGuard
    simpa only [d854, d3083, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16789 (pattern : Twelve) (guard : d1848 pattern = 1) : d861 pattern ≤ (0 : Int) + d3084 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d861, d3084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16781 pattern childGuard
    simpa only [d861, d3084, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d861, d3084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16788 pattern childGuard
    simpa only [d861, d3084, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16790 (pattern : Twelve) (guard : d1 pattern = 1) : d814 pattern ≤ (0 : Int) + d3 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16696 pattern childGuard
    simpa only [d814, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10867 pattern childGuard
    simpa only [d814, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16791 (pattern : Twelve) (guard : d1848 pattern = 1) : d819 pattern ≤ (0 : Int) + d3 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16790 pattern childGuard
    simpa only [d1848, d819, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16698 pattern childGuard
    simpa only [d1848, d819, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16792 (pattern : Twelve) (guard : d1848 pattern = 1) : d828 pattern ≤ (0 : Int) + d3085 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d828, d3085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11577 pattern childGuard
    simpa only [d828, d3085, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d828, d3085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16791 pattern childGuard
    simpa only [d828, d3085, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16793 (pattern : Twelve) (guard : d1848 pattern = 1) : d842 pattern ≤ (0 : Int) + d3086 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d842, d3086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11483 pattern childGuard
    simpa only [d842, d3086, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d842, d3086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16792 pattern childGuard
    simpa only [d842, d3086, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16794 (pattern : Twelve) (guard : d1848 pattern = 1) : d843 pattern ≤ (0 : Int) + d3087 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d843, d3087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11577 pattern childGuard
    simpa only [d843, d3087, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d843, d3087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16779 pattern childGuard
    simpa only [d843, d3087, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16795 (pattern : Twelve) (guard : d1848 pattern = 1) : d855 pattern ≤ (0 : Int) + d3088 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d855, d3088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16793 pattern childGuard
    simpa only [d855, d3088, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d855, d3088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16794 pattern childGuard
    simpa only [d855, d3088, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16796 (pattern : Twelve) (guard : d1 pattern = 1) : d815 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15042 pattern childGuard
    simpa only [d815, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15041 pattern childGuard
    simpa only [d815, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16797 (pattern : Twelve) (guard : d1848 pattern = 1) : d820 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16796 pattern childGuard
    simpa only [d1848, d820, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d1848, d820, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16798 (pattern : Twelve) (guard : d1848 pattern = 1) : d829 pattern ≤ (0 : Int) + d3051 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d829, d3051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16712 pattern childGuard
    simpa only [d829, d3051, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d829, d3051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16797 pattern childGuard
    simpa only [d829, d3051, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16799 (pattern : Twelve) (guard : d1848 pattern = 1) : d844 pattern ≤ (0 : Int) + d3052 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d844, d3052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16707 pattern childGuard
    simpa only [d844, d3052, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d844, d3052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16798 pattern childGuard
    simpa only [d844, d3052, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
