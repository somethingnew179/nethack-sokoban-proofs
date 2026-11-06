/- Stage-only soko2-1 exact finite geometry/numeric wrapper. -/
import NetHack.Sokoban21.GoalComparisons04
import NetHack.Sokoban21.Comparisons167
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem goalC650 (pattern : Twelve) (guard : d3252 pattern = 1) : d714 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3248 pattern = 1 := by simpa only [d3252, d714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC649 pattern childGuard
    simpa only [d3252, d714, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3252, d714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC629 pattern childGuard
    simpa only [d3252, d714, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC651 (pattern : Twelve) (guard : d3253 pattern = 1) : d738 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3249 pattern = 1 := by simpa only [d3253, d738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC647 pattern childGuard
    simpa only [d3253, d738, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3252 pattern = 1 := by simpa only [d3253, d738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC650 pattern childGuard
    simpa only [d3253, d738, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC652 (pattern : Twelve) (guard : d1 pattern = 1) : d631 pattern ≤ (0 : Int) + d4 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16664 pattern childGuard
    simpa only [d631, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2933 pattern childGuard
    simpa only [d631, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC653 (pattern : Twelve) (guard : d1866 pattern = 1) : d158 pattern ≤ (0 : Int) + d4 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1866, d158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16664 pattern childGuard
    simpa only [d1866, d158, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1866, d158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5027 pattern childGuard
    simpa only [d1866, d158, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC654 (pattern : Twelve) (guard : d3241 pattern = 1) : d641 pattern ≤ (0 : Int) + d4 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d3241, d641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC652 pattern childGuard
    simpa only [d3241, d641, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d3241, d641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC653 pattern childGuard
    simpa only [d3241, d641, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC655 (pattern : Twelve) (guard : d1866 pattern = 1) : d160 pattern ≤ (0 : Int) + d5 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1866, d160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16751 pattern childGuard
    simpa only [d1866, d160, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1866, d160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5335 pattern childGuard
    simpa only [d1866, d160, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC656 (pattern : Twelve) (guard : d0 pattern = 1) : d160 pattern ≤ (0 : Int) + d5 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC657 (pattern : Twelve) (guard : d1867 pattern = 1) : d160 pattern ≤ (0 : Int) + d5 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC655 pattern childGuard
    simpa only [d1867, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC656 pattern childGuard
    simpa only [d1867, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC658 (pattern : Twelve) (guard : d3244 pattern = 1) : d662 pattern ≤ (0 : Int) + d3282 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d3241 pattern = 1 := by simpa only [d3244, d662, d3282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC654 pattern childGuard
    simpa only [d3244, d662, d3282, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3244, d662, d3282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC657 pattern childGuard
    simpa only [d3244, d662, d3282, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC659 (pattern : Twelve) (guard : d0 pattern = 1) : d158 pattern ≤ (0 : Int) + d4 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC660 (pattern : Twelve) (guard : d1867 pattern = 1) : d158 pattern ≤ (0 : Int) + d4 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC653 pattern childGuard
    simpa only [d1867, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC659 pattern childGuard
    simpa only [d1867, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC661 (pattern : Twelve) (guard : d3247 pattern = 1) : d663 pattern ≤ (0 : Int) + d3282 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3247, d663, d3282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC660 pattern childGuard
    simpa only [d3247, d663, d3282, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3247, d663, d3282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5335 pattern childGuard
    simpa only [d3247, d663, d3282, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC662 (pattern : Twelve) (guard : d3248 pattern = 1) : d691 pattern ≤ (0 : Int) + d3282 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3244 pattern = 1 := by simpa only [d3248, d691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC658 pattern childGuard
    simpa only [d3248, d691, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3248, d691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC661 pattern childGuard
    simpa only [d3248, d691, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC663 (pattern : Twelve) (guard : d3247 pattern = 1) : d657 pattern ≤ (0 : Int) + d3282 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3247, d657, d3282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC660 pattern childGuard
    simpa only [d3247, d657, d3282, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3247, d657, d3282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC656 pattern childGuard
    simpa only [d3247, d657, d3282, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC664 (pattern : Twelve) (guard : d0 pattern = 1) : d663 pattern ≤ (0 : Int) + d3282 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC665 (pattern : Twelve) (guard : d3251 pattern = 1) : d692 pattern ≤ (0 : Int) + d3282 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3251, d692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC663 pattern childGuard
    simpa only [d3251, d692, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3251, d692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC664 pattern childGuard
    simpa only [d3251, d692, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC666 (pattern : Twelve) (guard : d3252 pattern = 1) : d715 pattern ≤ (0 : Int) + d3282 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3248 pattern = 1 := by simpa only [d3252, d715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC662 pattern childGuard
    simpa only [d3252, d715, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3252, d715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC665 pattern childGuard
    simpa only [d3252, d715, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC667 (pattern : Twelve) (guard : d0 pattern = 1) : d687 pattern ≤ (0 : Int) + d3282 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC668 (pattern : Twelve) (guard : d3255 pattern = 1) : d716 pattern ≤ (0 : Int) + d3282 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3255, d716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC665 pattern childGuard
    simpa only [d3255, d716, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3255, d716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC667 pattern childGuard
    simpa only [d3255, d716, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC669 (pattern : Twelve) (guard : d3256 pattern = 1) : d739 pattern ≤ (0 : Int) + d3282 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3252 pattern = 1 := by simpa only [d3256, d739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC666 pattern childGuard
    simpa only [d3256, d739, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3255 pattern = 1 := by simpa only [d3256, d739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC668 pattern childGuard
    simpa only [d3256, d739, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC670 (pattern : Twelve) (guard : d3257 pattern = 1) : d755 pattern ≤ (0 : Int) + d3283 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d3253 pattern = 1 := by simpa only [d3257, d755, d3283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC651 pattern childGuard
    simpa only [d3257, d755, d3283, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3256 pattern = 1 := by simpa only [d3257, d755, d3283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC669 pattern childGuard
    simpa only [d3257, d755, d3283, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC671 (pattern : Twelve) (guard : d3258 pattern = 1) : d766 pattern ≤ (0 : Int) + d3284 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d3254 pattern = 1 := by simpa only [d3258, d766, d3284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC632 pattern childGuard
    simpa only [d3258, d766, d3284, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3257 pattern = 1 := by simpa only [d3258, d766, d3284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC670 pattern childGuard
    simpa only [d3258, d766, d3284, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC672 (pattern : Twelve) (guard : d1866 pattern = 1) : d160 pattern ≤ (0 : Int) + d4 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1866, d160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10874 pattern childGuard
    simpa only [d1866, d160, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1866, d160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5027 pattern childGuard
    simpa only [d1866, d160, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC673 (pattern : Twelve) (guard : d3241 pattern = 1) : d642 pattern ≤ (0 : Int) + d4 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d3241, d642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11500 pattern childGuard
    simpa only [d3241, d642, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d3241, d642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC672 pattern childGuard
    simpa only [d3241, d642, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC674 (pattern : Twelve) (guard : d3242 pattern = 1) : d664 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d3242, d664, d3285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC633 pattern childGuard
    simpa only [d3242, d664, d3285, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3241 pattern = 1 := by simpa only [d3242, d664, d3285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC673 pattern childGuard
    simpa only [d3242, d664, d3285, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC675 (pattern : Twelve) (guard : d0 pattern = 1) : d160 pattern ≤ (0 : Int) + d4 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC676 (pattern : Twelve) (guard : d1867 pattern = 1) : d160 pattern ≤ (0 : Int) + d4 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC672 pattern childGuard
    simpa only [d1867, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC675 pattern childGuard
    simpa only [d1867, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC677 (pattern : Twelve) (guard : d3244 pattern = 1) : d665 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d3241 pattern = 1 := by simpa only [d3244, d665, d3285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC635 pattern childGuard
    simpa only [d3244, d665, d3285, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3244, d665, d3285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC676 pattern childGuard
    simpa only [d3244, d665, d3285, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC678 (pattern : Twelve) (guard : d3245 pattern = 1) : d693 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3242 pattern = 1 := by simpa only [d3245, d693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC674 pattern childGuard
    simpa only [d3245, d693, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3244 pattern = 1 := by simpa only [d3245, d693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC677 pattern childGuard
    simpa only [d3245, d693, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC679 (pattern : Twelve) (guard : d0 pattern = 1) : d159 pattern ≤ (0 : Int) + d4 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC680 (pattern : Twelve) (guard : d3247 pattern = 1) : d666 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3247, d666, d3285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC638 pattern childGuard
    simpa only [d3247, d666, d3285, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3247, d666, d3285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC679 pattern childGuard
    simpa only [d3247, d666, d3285, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC681 (pattern : Twelve) (guard : d3248 pattern = 1) : d694 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3244 pattern = 1 := by simpa only [d3248, d694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC677 pattern childGuard
    simpa only [d3248, d694, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3248, d694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC680 pattern childGuard
    simpa only [d3248, d694, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC682 (pattern : Twelve) (guard : d3249 pattern = 1) : d717 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3245 pattern = 1 := by simpa only [d3249, d717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC678 pattern childGuard
    simpa only [d3249, d717, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3248 pattern = 1 := by simpa only [d3249, d717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC681 pattern childGuard
    simpa only [d3249, d717, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC683 (pattern : Twelve) (guard : d3247 pattern = 1) : d657 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3247, d657, d3285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC638 pattern childGuard
    simpa only [d3247, d657, d3285, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3247, d657, d3285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC675 pattern childGuard
    simpa only [d3247, d657, d3285, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC684 (pattern : Twelve) (guard : d3248 pattern = 1) : d695 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3244 pattern = 1 := by simpa only [d3248, d695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC677 pattern childGuard
    simpa only [d3248, d695, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3248, d695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC683 pattern childGuard
    simpa only [d3248, d695, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC685 (pattern : Twelve) (guard : d0 pattern = 1) : d651 pattern ≤ (0 : Int) + d3285 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC686 (pattern : Twelve) (guard : d3251 pattern = 1) : d687 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3251, d687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC683 pattern childGuard
    simpa only [d3251, d687, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3251, d687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC685 pattern childGuard
    simpa only [d3251, d687, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC687 (pattern : Twelve) (guard : d3252 pattern = 1) : d718 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3248 pattern = 1 := by simpa only [d3252, d718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC684 pattern childGuard
    simpa only [d3252, d718, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3252, d718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC686 pattern childGuard
    simpa only [d3252, d718, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC688 (pattern : Twelve) (guard : d3253 pattern = 1) : d740 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3249 pattern = 1 := by simpa only [d3253, d740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC682 pattern childGuard
    simpa only [d3253, d740, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3252 pattern = 1 := by simpa only [d3253, d740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC687 pattern childGuard
    simpa only [d3253, d740, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC689 (pattern : Twelve) (guard : d1 pattern = 1) : d632 pattern ≤ (0 : Int) + d5 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16751 pattern childGuard
    simpa only [d632, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3017 pattern childGuard
    simpa only [d632, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC690 (pattern : Twelve) (guard : d3241 pattern = 1) : d643 pattern ≤ (0 : Int) + d5 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d3241, d643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC689 pattern childGuard
    simpa only [d3241, d643, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d3241, d643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC655 pattern childGuard
    simpa only [d3241, d643, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC691 (pattern : Twelve) (guard : d1867 pattern = 1) : d13 pattern ≤ (0 : Int) + d6 pattern := by
  have upper := (range13 pattern).2
  change d13 pattern ≤ (0 : Int) + 6
  omega
theorem goalC692 (pattern : Twelve) (guard : d3244 pattern = 1) : d667 pattern ≤ (0 : Int) + d781 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d3241 pattern = 1 := by simpa only [d3244, d667, d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC690 pattern childGuard
    simpa only [d3244, d667, d781, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3244, d667, d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC691 pattern childGuard
    simpa only [d3244, d667, d781, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC693 (pattern : Twelve) (guard : d3247 pattern = 1) : d668 pattern ≤ (0 : Int) + d781 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3247, d668, d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC657 pattern childGuard
    simpa only [d3247, d668, d781, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3247, d668, d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d3247, d668, d781, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC694 (pattern : Twelve) (guard : d3248 pattern = 1) : d696 pattern ≤ (0 : Int) + d781 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3244 pattern = 1 := by simpa only [d3248, d696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC692 pattern childGuard
    simpa only [d3248, d696, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3248, d696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC693 pattern childGuard
    simpa only [d3248, d696, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC695 (pattern : Twelve) (guard : d3247 pattern = 1) : d669 pattern ≤ (0 : Int) + d781 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3247, d669, d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC657 pattern childGuard
    simpa only [d3247, d669, d781, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3247, d669, d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2866 pattern childGuard
    simpa only [d3247, d669, d781, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC696 (pattern : Twelve) (guard : d0 pattern = 1) : d668 pattern ≤ (0 : Int) + d781 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC697 (pattern : Twelve) (guard : d3251 pattern = 1) : d697 pattern ≤ (0 : Int) + d781 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3251, d697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC695 pattern childGuard
    simpa only [d3251, d697, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3251, d697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC696 pattern childGuard
    simpa only [d3251, d697, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC698 (pattern : Twelve) (guard : d3252 pattern = 1) : d719 pattern ≤ (0 : Int) + d781 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3248 pattern = 1 := by simpa only [d3252, d719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC694 pattern childGuard
    simpa only [d3252, d719, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3252, d719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC697 pattern childGuard
    simpa only [d3252, d719, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC699 (pattern : Twelve) (guard : d0 pattern = 1) : d698 pattern ≤ (0 : Int) + d781 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC700 (pattern : Twelve) (guard : d3255 pattern = 1) : d720 pattern ≤ (0 : Int) + d781 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3255, d720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC697 pattern childGuard
    simpa only [d3255, d720, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3255, d720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC699 pattern childGuard
    simpa only [d3255, d720, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC701 (pattern : Twelve) (guard : d3256 pattern = 1) : d741 pattern ≤ (0 : Int) + d781 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3252 pattern = 1 := by simpa only [d3256, d741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC698 pattern childGuard
    simpa only [d3256, d741, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3255 pattern = 1 := by simpa only [d3256, d741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC700 pattern childGuard
    simpa only [d3256, d741, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC702 (pattern : Twelve) (guard : d3257 pattern = 1) : d756 pattern ≤ (0 : Int) + d3286 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d3253 pattern = 1 := by simpa only [d3257, d756, d3286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC688 pattern childGuard
    simpa only [d3257, d756, d3286, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3256 pattern = 1 := by simpa only [d3257, d756, d3286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC701 pattern childGuard
    simpa only [d3257, d756, d3286, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC703 (pattern : Twelve) (guard : d1 pattern = 1) : d633 pattern ≤ (0 : Int) + d5 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16662 pattern childGuard
    simpa only [d633, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3017 pattern childGuard
    simpa only [d633, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC704 (pattern : Twelve) (guard : d1866 pattern = 1) : d158 pattern ≤ (0 : Int) + d5 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1866, d158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16662 pattern childGuard
    simpa only [d1866, d158, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1866, d158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5335 pattern childGuard
    simpa only [d1866, d158, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC705 (pattern : Twelve) (guard : d3241 pattern = 1) : d645 pattern ≤ (0 : Int) + d5 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d3241, d645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC703 pattern childGuard
    simpa only [d3241, d645, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d3241, d645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC704 pattern childGuard
    simpa only [d3241, d645, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC706 (pattern : Twelve) (guard : d1867 pattern = 1) : d160 pattern ≤ (0 : Int) + d6 pattern := by
  have upper := (range160 pattern).2
  change d160 pattern ≤ (0 : Int) + 6
  omega
theorem goalC707 (pattern : Twelve) (guard : d3244 pattern = 1) : d671 pattern ≤ (0 : Int) + d781 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d3241 pattern = 1 := by simpa only [d3244, d671, d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC705 pattern childGuard
    simpa only [d3244, d671, d781, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3244, d671, d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC706 pattern childGuard
    simpa only [d3244, d671, d781, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC708 (pattern : Twelve) (guard : d0 pattern = 1) : d158 pattern ≤ (0 : Int) + d5 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC709 (pattern : Twelve) (guard : d1867 pattern = 1) : d158 pattern ≤ (0 : Int) + d5 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC704 pattern childGuard
    simpa only [d1867, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC708 pattern childGuard
    simpa only [d1867, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC710 (pattern : Twelve) (guard : d3247 pattern = 1) : d663 pattern ≤ (0 : Int) + d781 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3247, d663, d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC709 pattern childGuard
    simpa only [d3247, d663, d781, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3247, d663, d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d3247, d663, d781, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC711 (pattern : Twelve) (guard : d3248 pattern = 1) : d699 pattern ≤ (0 : Int) + d781 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3244 pattern = 1 := by simpa only [d3248, d699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC707 pattern childGuard
    simpa only [d3248, d699, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3248, d699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC710 pattern childGuard
    simpa only [d3248, d699, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC712 (pattern : Twelve) (guard : d3247 pattern = 1) : d657 pattern ≤ (0 : Int) + d781 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3247, d657, d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC709 pattern childGuard
    simpa only [d3247, d657, d781, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3247, d657, d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8138 pattern childGuard
    simpa only [d3247, d657, d781, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC713 (pattern : Twelve) (guard : d0 pattern = 1) : d663 pattern ≤ (0 : Int) + d781 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC714 (pattern : Twelve) (guard : d3251 pattern = 1) : d692 pattern ≤ (0 : Int) + d781 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3251, d692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC712 pattern childGuard
    simpa only [d3251, d692, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3251, d692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC713 pattern childGuard
    simpa only [d3251, d692, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC715 (pattern : Twelve) (guard : d3252 pattern = 1) : d721 pattern ≤ (0 : Int) + d781 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3248 pattern = 1 := by simpa only [d3252, d721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC711 pattern childGuard
    simpa only [d3252, d721, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3252, d721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC714 pattern childGuard
    simpa only [d3252, d721, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC716 (pattern : Twelve) (guard : d0 pattern = 1) : d687 pattern ≤ (0 : Int) + d781 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC717 (pattern : Twelve) (guard : d3255 pattern = 1) : d716 pattern ≤ (0 : Int) + d781 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3255, d716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC714 pattern childGuard
    simpa only [d3255, d716, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3255, d716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC716 pattern childGuard
    simpa only [d3255, d716, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC718 (pattern : Twelve) (guard : d3256 pattern = 1) : d742 pattern ≤ (0 : Int) + d781 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3252 pattern = 1 := by simpa only [d3256, d742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC715 pattern childGuard
    simpa only [d3256, d742, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3255 pattern = 1 := by simpa only [d3256, d742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC717 pattern childGuard
    simpa only [d3256, d742, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC719 (pattern : Twelve) (guard : d3260 pattern = 1) : d757 pattern ≤ (0 : Int) + d3287 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d3256 pattern = 1 := by simpa only [d3260, d757, d3287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC718 pattern childGuard
    simpa only [d3260, d757, d3287, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3259 pattern = 1 := by simpa only [d3260, d757, d3287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC134 pattern childGuard
    simpa only [d3260, d757, d3287, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC720 (pattern : Twelve) (guard : d3261 pattern = 1) : d767 pattern ≤ (0 : Int) + d3288 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d3257 pattern = 1 := by simpa only [d3261, d767, d3288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC702 pattern childGuard
    simpa only [d3261, d767, d3288, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3260 pattern = 1 := by simpa only [d3261, d767, d3288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC719 pattern childGuard
    simpa only [d3261, d767, d3288, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC721 (pattern : Twelve) (guard : d3262 pattern = 1) : d772 pattern ≤ (0 : Int) + d3289 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d3258 pattern = 1 := by simpa only [d3262, d772, d3289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC671 pattern childGuard
    simpa only [d3262, d772, d3289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3261 pattern = 1 := by simpa only [d3262, d772, d3289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC720 pattern childGuard
    simpa only [d3262, d772, d3289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC722 (pattern : Twelve) (guard : d3265 pattern = 1) : d773 pattern ≤ (0 : Int) + d6 pattern := by
  have upper := (range773 pattern).2
  change d773 pattern ≤ (0 : Int) + 6
  omega
theorem goalC723 (pattern : Twelve) (guard : d3266 pattern = 1) : d775 pattern ≤ (0 : Int) + d3290 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d3262 pattern = 1 := by simpa only [d3266, d775, d3290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC721 pattern childGuard
    simpa only [d3266, d775, d3290, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3265 pattern = 1 := by simpa only [d3266, d775, d3290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC722 pattern childGuard
    simpa only [d3266, d775, d3290, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC724 (pattern : Twelve) (guard : d3269 pattern = 1) : d773 pattern ≤ (0 : Int) + d6 pattern := by
  have upper := (range773 pattern).2
  change d773 pattern ≤ (0 : Int) + 6
  omega
theorem goalC725 (pattern : Twelve) (guard : d3270 pattern = 1) : d776 pattern ≤ (0 : Int) + d3291 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d3266 pattern = 1 := by simpa only [d3270, d776, d3291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC723 pattern childGuard
    simpa only [d3270, d776, d3291, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3269 pattern = 1 := by simpa only [d3270, d776, d3291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC724 pattern childGuard
    simpa only [d3270, d776, d3291, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC726 (pattern : Twelve) (guard : d3273 pattern = 1) : d774 pattern ≤ (0 : Int) + d6 pattern := by
  have upper := (range774 pattern).2
  change d774 pattern ≤ (0 : Int) + 6
  omega
theorem goalC727 (pattern : Twelve) (guard : d3274 pattern = 1) : d777 pattern ≤ (0 : Int) + d3292 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d3270 pattern = 1 := by simpa only [d3274, d777, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC725 pattern childGuard
    simpa only [d3274, d777, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3273 pattern = 1 := by simpa only [d3274, d777, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC726 pattern childGuard
    simpa only [d3274, d777, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC728 (pattern : Twelve) (guard : d3273 pattern = 1) : d805 pattern ≤ (0 : Int) + d6 pattern := by
  have upper := (range805 pattern).2
  change d805 pattern ≤ (0 : Int) + 6
  omega
theorem goalC729 (pattern : Twelve) (guard : d3274 pattern = 1) : d806 pattern ≤ (0 : Int) + d3292 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d3270 pattern = 1 := by simpa only [d3274, d806, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC141 pattern childGuard
    simpa only [d3274, d806, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3273 pattern = 1 := by simpa only [d3274, d806, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC728 pattern childGuard
    simpa only [d3274, d806, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC730 (pattern : Twelve) (guard : d3266 pattern = 1) : d807 pattern ≤ (0 : Int) + d3290 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d3262 pattern = 1 := by simpa only [d3266, d807, d3290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC137 pattern childGuard
    simpa only [d3266, d807, d3290, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3265 pattern = 1 := by simpa only [d3266, d807, d3290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC214 pattern childGuard
    simpa only [d3266, d807, d3290, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC731 (pattern : Twelve) (guard : d3269 pattern = 1) : d807 pattern ≤ (0 : Int) + d6 pattern := by
  have upper := (range807 pattern).2
  change d807 pattern ≤ (0 : Int) + 6
  omega
theorem goalC732 (pattern : Twelve) (guard : d3270 pattern = 1) : d807 pattern ≤ (0 : Int) + d3291 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d3266 pattern = 1 := by simpa only [d3270, d3291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC730 pattern childGuard
    simpa only [d3270, d3291, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3269 pattern = 1 := by simpa only [d3270, d3291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC731 pattern childGuard
    simpa only [d3270, d3291, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC733 (pattern : Twelve) (guard : d3273 pattern = 1) : d808 pattern ≤ (0 : Int) + d6 pattern := by
  have upper := (range808 pattern).2
  change d808 pattern ≤ (0 : Int) + 6
  omega
theorem goalC734 (pattern : Twelve) (guard : d3274 pattern = 1) : d809 pattern ≤ (0 : Int) + d3292 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d3270 pattern = 1 := by simpa only [d3274, d809, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC732 pattern childGuard
    simpa only [d3274, d809, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3273 pattern = 1 := by simpa only [d3274, d809, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC733 pattern childGuard
    simpa only [d3274, d809, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC735 (pattern : Twelve) (guard : d3270 pattern = 1) : d810 pattern ≤ (0 : Int) + d3291 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d3266 pattern = 1 := by simpa only [d3270, d810, d3291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC139 pattern childGuard
    simpa only [d3270, d810, d3291, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3269 pattern = 1 := by simpa only [d3270, d810, d3291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC216 pattern childGuard
    simpa only [d3270, d810, d3291, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC736 (pattern : Twelve) (guard : d3273 pattern = 1) : d811 pattern ≤ (0 : Int) + d6 pattern := by
  have upper := (range811 pattern).2
  change d811 pattern ≤ (0 : Int) + 6
  omega
theorem goalC737 (pattern : Twelve) (guard : d3274 pattern = 1) : d812 pattern ≤ (0 : Int) + d3292 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d3270 pattern = 1 := by simpa only [d3274, d812, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC735 pattern childGuard
    simpa only [d3274, d812, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3273 pattern = 1 := by simpa only [d3274, d812, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC736 pattern childGuard
    simpa only [d3274, d812, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC738 (pattern : Twelve) (guard : d3274 pattern = 1) : d813 pattern ≤ (0 : Int) + d3292 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d3270 pattern = 1 := by simpa only [d3274, d813, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC141 pattern childGuard
    simpa only [d3274, d813, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3273 pattern = 1 := by simpa only [d3274, d813, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC218 pattern childGuard
    simpa only [d3274, d813, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC739 (pattern : Twelve) (guard : d1867 pattern = 1) : d814 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7730 pattern childGuard
    simpa only [d1867, d814, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4957 pattern childGuard
    simpa only [d1867, d814, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC740 (pattern : Twelve) (guard : d3247 pattern = 1) : d816 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3247, d816, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC739 pattern childGuard
    simpa only [d3247, d816, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3247, d816, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11444 pattern childGuard
    simpa only [d3247, d816, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC741 (pattern : Twelve) (guard : d3248 pattern = 1) : d824 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3244 pattern = 1 := by simpa only [d3248, d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC7 pattern childGuard
    simpa only [d3248, d824, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3248, d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC740 pattern childGuard
    simpa only [d3248, d824, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC742 (pattern : Twelve) (guard : d3249 pattern = 1) : d838 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3245 pattern = 1 := by simpa only [d3249, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC13 pattern childGuard
    simpa only [d3249, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3248 pattern = 1 := by simpa only [d3249, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC741 pattern childGuard
    simpa only [d3249, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC743 (pattern : Twelve) (guard : d1867 pattern = 1) : d17 pattern ≤ (0 : Int) + d1 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC462 pattern childGuard
    simpa only [d1867, d17, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8122 pattern childGuard
    simpa only [d1867, d17, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC744 (pattern : Twelve) (guard : d3244 pattern = 1) : d17 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d3241 pattern = 1 := by simpa only [d3244, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC5 pattern childGuard
    simpa only [d3244, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3244, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC743 pattern childGuard
    simpa only [d3244, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC745 (pattern : Twelve) (guard : d1867 pattern = 1) : d17 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3256 pattern childGuard
    simpa only [d1867, d17, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8471 pattern childGuard
    simpa only [d1867, d17, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC746 (pattern : Twelve) (guard : d0 pattern = 1) : d17 pattern ≤ (0 : Int) + d1 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC747 (pattern : Twelve) (guard : d3247 pattern = 1) : d17 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3247, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC745 pattern childGuard
    simpa only [d3247, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3247, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC746 pattern childGuard
    simpa only [d3247, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC748 (pattern : Twelve) (guard : d3248 pattern = 1) : d17 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3244 pattern = 1 := by simpa only [d3248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC744 pattern childGuard
    simpa only [d3248, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC747 pattern childGuard
    simpa only [d3248, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC749 (pattern : Twelve) (guard : d0 pattern = 1) : d25 pattern ≤ (0 : Int) + d1 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC750 (pattern : Twelve) (guard : d3247 pattern = 1) : d817 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3247, d817, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC19 pattern childGuard
    simpa only [d3247, d817, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3247, d817, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC749 pattern childGuard
    simpa only [d3247, d817, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC751 (pattern : Twelve) (guard : d0 pattern = 1) : d42 pattern ≤ (0 : Int) + d26 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC752 (pattern : Twelve) (guard : d3251 pattern = 1) : d825 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3251, d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC750 pattern childGuard
    simpa only [d3251, d825, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3251, d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC751 pattern childGuard
    simpa only [d3251, d825, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC753 (pattern : Twelve) (guard : d3252 pattern = 1) : d839 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3248 pattern = 1 := by simpa only [d3252, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC748 pattern childGuard
    simpa only [d3252, d839, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3252, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC752 pattern childGuard
    simpa only [d3252, d839, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC754 (pattern : Twelve) (guard : d3253 pattern = 1) : d853 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3249 pattern = 1 := by simpa only [d3253, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC742 pattern childGuard
    simpa only [d3253, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3252 pattern = 1 := by simpa only [d3253, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC753 pattern childGuard
    simpa only [d3253, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC755 (pattern : Twelve) (guard : d3248 pattern = 1) : d56 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3244 pattern = 1 := by simpa only [d3248, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC34 pattern childGuard
    simpa only [d3248, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3248, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC366 pattern childGuard
    simpa only [d3248, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC756 (pattern : Twelve) (guard : d0 pattern = 1) : d818 pattern ≤ (0 : Int) + d778 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC757 (pattern : Twelve) (guard : d3251 pattern = 1) : d826 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3251, d826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC47 pattern childGuard
    simpa only [d3251, d826, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3251, d826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC756 pattern childGuard
    simpa only [d3251, d826, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC758 (pattern : Twelve) (guard : d3252 pattern = 1) : d840 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3248 pattern = 1 := by simpa only [d3252, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC755 pattern childGuard
    simpa only [d3252, d840, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3252, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC757 pattern childGuard
    simpa only [d3252, d840, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC759 (pattern : Twelve) (guard : d0 pattern = 1) : d36 pattern ≤ (0 : Int) + d778 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC760 (pattern : Twelve) (guard : d3251 pattern = 1) : d827 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3251, d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC47 pattern childGuard
    simpa only [d3251, d827, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3251, d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC759 pattern childGuard
    simpa only [d3251, d827, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC761 (pattern : Twelve) (guard : d0 pattern = 1) : d825 pattern ≤ (0 : Int) + d778 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC762 (pattern : Twelve) (guard : d3255 pattern = 1) : d841 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3255, d841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC760 pattern childGuard
    simpa only [d3255, d841, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3255, d841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC761 pattern childGuard
    simpa only [d3255, d841, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC763 (pattern : Twelve) (guard : d3256 pattern = 1) : d854 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3252 pattern = 1 := by simpa only [d3256, d854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC758 pattern childGuard
    simpa only [d3256, d854, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3255 pattern = 1 := by simpa only [d3256, d854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC762 pattern childGuard
    simpa only [d3256, d854, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC764 (pattern : Twelve) (guard : d3257 pattern = 1) : d861 pattern ≤ (0 : Int) + d3281 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d3253 pattern = 1 := by simpa only [d3257, d861, d3281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC754 pattern childGuard
    simpa only [d3257, d861, d3281, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3256 pattern = 1 := by simpa only [d3257, d861, d3281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC763 pattern childGuard
    simpa only [d3257, d861, d3281, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC765 (pattern : Twelve) (guard : d0 pattern = 1) : d816 pattern ≤ (0 : Int) + d778 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC766 (pattern : Twelve) (guard : d3251 pattern = 1) : d824 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3251, d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC60 pattern childGuard
    simpa only [d3251, d824, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3251, d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC765 pattern childGuard
    simpa only [d3251, d824, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC767 (pattern : Twelve) (guard : d3252 pattern = 1) : d838 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3248 pattern = 1 := by simpa only [d3252, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC64 pattern childGuard
    simpa only [d3252, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3252, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC766 pattern childGuard
    simpa only [d3252, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC768 (pattern : Twelve) (guard : d0 pattern = 1) : d17 pattern ≤ (0 : Int) + d3 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC769 (pattern : Twelve) (guard : d3247 pattern = 1) : d17 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3247, d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC37 pattern childGuard
    simpa only [d3247, d778, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3247, d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC768 pattern childGuard
    simpa only [d3247, d778, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC770 (pattern : Twelve) (guard : d0 pattern = 1) : d17 pattern ≤ (0 : Int) + d778 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC771 (pattern : Twelve) (guard : d3251 pattern = 1) : d17 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC769 pattern childGuard
    simpa only [d3251, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC770 pattern childGuard
    simpa only [d3251, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC772 (pattern : Twelve) (guard : d3255 pattern = 1) : d839 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3255, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC771 pattern childGuard
    simpa only [d3255, d839, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3255, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC761 pattern childGuard
    simpa only [d3255, d839, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC773 (pattern : Twelve) (guard : d3256 pattern = 1) : d853 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3252 pattern = 1 := by simpa only [d3256, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC767 pattern childGuard
    simpa only [d3256, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3255 pattern = 1 := by simpa only [d3256, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC772 pattern childGuard
    simpa only [d3256, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC774 (pattern : Twelve) (guard : d0 pattern = 1) : d826 pattern ≤ (0 : Int) + d3282 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC775 (pattern : Twelve) (guard : d3255 pattern = 1) : d840 pattern ≤ (0 : Int) + d3282 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3255, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC78 pattern childGuard
    simpa only [d3255, d840, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3255, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC774 pattern childGuard
    simpa only [d3255, d840, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC776 (pattern : Twelve) (guard : d0 pattern = 1) : d841 pattern ≤ (0 : Int) + d3282 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC777 (pattern : Twelve) (guard : d3259 pattern = 1) : d854 pattern ≤ (0 : Int) + d3282 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3255 pattern = 1 := by simpa only [d3259, d854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC775 pattern childGuard
    simpa only [d3259, d854, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3259, d854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC776 pattern childGuard
    simpa only [d3259, d854, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC778 (pattern : Twelve) (guard : d3260 pattern = 1) : d861 pattern ≤ (0 : Int) + d3283 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d3256 pattern = 1 := by simpa only [d3260, d861, d3283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC773 pattern childGuard
    simpa only [d3260, d861, d3283, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3259 pattern = 1 := by simpa only [d3260, d861, d3283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC777 pattern childGuard
    simpa only [d3260, d861, d3283, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC779 (pattern : Twelve) (guard : d3261 pattern = 1) : d861 pattern ≤ (0 : Int) + d3284 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d3257 pattern = 1 := by simpa only [d3261, d3284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC764 pattern childGuard
    simpa only [d3261, d3284, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3260 pattern = 1 := by simpa only [d3261, d3284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC778 pattern childGuard
    simpa only [d3261, d3284, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
