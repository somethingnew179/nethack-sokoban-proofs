/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons032
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c4620 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d96 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4621 (pattern : Twelve) (guard : d1869 pattern = 1) : d356 pattern ≤ (0 : Int) + d104 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d356, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4619 pattern childGuard
    simpa only [d1869, d356, d104, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d356, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4620 pattern childGuard
    simpa only [d1869, d356, d104, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4622 (pattern : Twelve) (guard : d1848 pattern = 1) : d30 pattern ≤ (0 : Int) + d56 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1567 pattern childGuard
    simpa only [d56, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1312 pattern childGuard
    simpa only [d56, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4623 (pattern : Twelve) (guard : d1848 pattern = 1) : d80 pattern ≤ (0 : Int) + d78 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d80, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4622 pattern childGuard
    simpa only [d80, d78, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d80, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4603 pattern childGuard
    simpa only [d80, d78, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4624 (pattern : Twelve) (guard : d1848 pattern = 1) : d97 pattern ≤ (0 : Int) + d94 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d97, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4602 pattern childGuard
    simpa only [d97, d94, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d97, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4623 pattern childGuard
    simpa only [d97, d94, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4625 (pattern : Twelve) (guard : d1869 pattern = 1) : d356 pattern ≤ (0 : Int) + d105 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d356, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4624 pattern childGuard
    simpa only [d1869, d356, d105, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d356, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d1869, d356, d105, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4626 (pattern : Twelve) (guard : d1869 pattern = 1) : d356 pattern ≤ (0 : Int) + d111 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4621 pattern childGuard
    simpa only [d111, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4625 pattern childGuard
    simpa only [d111, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4627 (pattern : Twelve) (guard : d1869 pattern = 1) : d356 pattern ≤ (0 : Int) + d114 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4617 pattern childGuard
    simpa only [d114, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4626 pattern childGuard
    simpa only [d114, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4628 (pattern : Twelve) (guard : d1869 pattern = 1) : d362 pattern ≤ (0 : Int) + d114 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4608 pattern childGuard
    simpa only [d362, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4627 pattern childGuard
    simpa only [d362, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4629 (pattern : Twelve) (guard : d1869 pattern = 1) : d357 pattern ≤ (0 : Int) + d102 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d357, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4586 pattern childGuard
    simpa only [d1869, d357, d102, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d357, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4334 pattern childGuard
    simpa only [d1869, d357, d102, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4630 (pattern : Twelve) (guard : d1869 pattern = 1) : d355 pattern ≤ (0 : Int) + d103 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d355, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4588 pattern childGuard
    simpa only [d1869, d355, d103, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d355, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4336 pattern childGuard
    simpa only [d1869, d355, d103, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4631 (pattern : Twelve) (guard : d1869 pattern = 1) : d360 pattern ≤ (0 : Int) + d110 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d360, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4629 pattern childGuard
    simpa only [d360, d110, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d360, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4630 pattern childGuard
    simpa only [d360, d110, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4632 (pattern : Twelve) (guard : d1869 pattern = 1) : d357 pattern ≤ (0 : Int) + d104 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d357, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4597 pattern childGuard
    simpa only [d1869, d357, d104, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d357, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4620 pattern childGuard
    simpa only [d1869, d357, d104, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4633 (pattern : Twelve) (guard : d1869 pattern = 1) : d360 pattern ≤ (0 : Int) + d111 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d360, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4632 pattern childGuard
    simpa only [d360, d111, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d360, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4606 pattern childGuard
    simpa only [d360, d111, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4634 (pattern : Twelve) (guard : d1869 pattern = 1) : d360 pattern ≤ (0 : Int) + d114 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4631 pattern childGuard
    simpa only [d114, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4633 pattern childGuard
    simpa only [d114, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4635 (pattern : Twelve) (guard : d1869 pattern = 1) : d363 pattern ≤ (0 : Int) + d114 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4634 pattern childGuard
    simpa only [d363, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4627 pattern childGuard
    simpa only [d363, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4636 (pattern : Twelve) (guard : d1869 pattern = 1) : d364 pattern ≤ (0 : Int) + d114 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4628 pattern childGuard
    simpa only [d364, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4635 pattern childGuard
    simpa only [d364, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4637 (pattern : Twelve) (guard : d0 pattern = 1) : d18 pattern ≤ (0 : Int) + d25 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4638 (pattern : Twelve) (guard : d1848 pattern = 1) : d28 pattern ≤ (0 : Int) + d120 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d28, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c240 pattern childGuard
    simpa only [d1848, d28, d120, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d28, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4637 pattern childGuard
    simpa only [d1848, d28, d120, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4639 (pattern : Twelve) (guard : d1848 pattern = 1) : d51 pattern ≤ (0 : Int) + d129 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d51, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4638 pattern childGuard
    simpa only [d51, d129, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d51, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2795 pattern childGuard
    simpa only [d51, d129, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4640 (pattern : Twelve) (guard : d1848 pattern = 1) : d73 pattern ≤ (0 : Int) + d136 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d73, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1560 pattern childGuard
    simpa only [d73, d136, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d73, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4639 pattern childGuard
    simpa only [d73, d136, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4641 (pattern : Twelve) (guard : d1848 pattern = 1) : d91 pattern ≤ (0 : Int) + d144 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d91, d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4609 pattern childGuard
    simpa only [d91, d144, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d91, d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4640 pattern childGuard
    simpa only [d91, d144, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4642 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d145 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4643 (pattern : Twelve) (guard : d1869 pattern = 1) : d357 pattern ≤ (0 : Int) + d149 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d357, d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4641 pattern childGuard
    simpa only [d1869, d357, d149, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d357, d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4642 pattern childGuard
    simpa only [d1869, d357, d149, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4644 (pattern : Twelve) (guard : d1848 pattern = 1) : d34 pattern ≤ (0 : Int) + d120 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d34, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c240 pattern childGuard
    simpa only [d1848, d34, d120, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d34, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4551 pattern childGuard
    simpa only [d1848, d34, d120, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4645 (pattern : Twelve) (guard : d1848 pattern = 1) : d55 pattern ≤ (0 : Int) + d129 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d55, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4644 pattern childGuard
    simpa only [d55, d129, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d55, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2795 pattern childGuard
    simpa only [d55, d129, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4646 (pattern : Twelve) (guard : d1848 pattern = 1) : d76 pattern ≤ (0 : Int) + d136 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d76, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1560 pattern childGuard
    simpa only [d76, d136, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d76, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4645 pattern childGuard
    simpa only [d76, d136, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4647 (pattern : Twelve) (guard : d1848 pattern = 1) : d93 pattern ≤ (0 : Int) + d144 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d93, d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4609 pattern childGuard
    simpa only [d93, d144, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d93, d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4646 pattern childGuard
    simpa only [d93, d144, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4648 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d146 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4649 (pattern : Twelve) (guard : d1869 pattern = 1) : d355 pattern ≤ (0 : Int) + d150 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d355, d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4647 pattern childGuard
    simpa only [d1869, d355, d150, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d355, d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4648 pattern childGuard
    simpa only [d1869, d355, d150, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4650 (pattern : Twelve) (guard : d1869 pattern = 1) : d360 pattern ≤ (0 : Int) + d153 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d360, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4643 pattern childGuard
    simpa only [d360, d153, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d360, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4649 pattern childGuard
    simpa only [d360, d153, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4651 (pattern : Twelve) (guard : d1848 pattern = 1) : d26 pattern ≤ (0 : Int) + d121 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d26, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1848, d26, d121, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d26, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4480 pattern childGuard
    simpa only [d1848, d26, d121, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4652 (pattern : Twelve) (guard : d0 pattern = 1) : d1 pattern ≤ (0 : Int) + d4 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4653 (pattern : Twelve) (guard : d1848 pattern = 1) : d27 pattern ≤ (0 : Int) + d122 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d27, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c240 pattern childGuard
    simpa only [d1848, d27, d122, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d27, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4652 pattern childGuard
    simpa only [d1848, d27, d122, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4654 (pattern : Twelve) (guard : d1848 pattern = 1) : d50 pattern ≤ (0 : Int) + d131 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d50, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4651 pattern childGuard
    simpa only [d50, d131, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d50, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4653 pattern childGuard
    simpa only [d50, d131, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4655 (pattern : Twelve) (guard : d1848 pattern = 1) : d72 pattern ≤ (0 : Int) + d140 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d72, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4403 pattern childGuard
    simpa only [d72, d140, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d72, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4654 pattern childGuard
    simpa only [d72, d140, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4656 (pattern : Twelve) (guard : d1848 pattern = 1) : d0 pattern ≤ (0 : Int) + d123 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1848, d123, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2915 pattern childGuard
    simpa only [d1848, d123, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4657 (pattern : Twelve) (guard : d1848 pattern = 1) : d0 pattern ≤ (0 : Int) + d132 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4403 pattern childGuard
    simpa only [d132, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4656 pattern childGuard
    simpa only [d132, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4658 (pattern : Twelve) (guard : d1848 pattern = 1) : d73 pattern ≤ (0 : Int) + d141 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d73, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4657 pattern childGuard
    simpa only [d73, d141, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d73, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4639 pattern childGuard
    simpa only [d73, d141, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4659 (pattern : Twelve) (guard : d1848 pattern = 1) : d91 pattern ≤ (0 : Int) + d147 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d91, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4655 pattern childGuard
    simpa only [d91, d147, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d91, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4658 pattern childGuard
    simpa only [d91, d147, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4660 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d148 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4661 (pattern : Twelve) (guard : d1869 pattern = 1) : d357 pattern ≤ (0 : Int) + d151 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d357, d151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4659 pattern childGuard
    simpa only [d1869, d357, d151, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d357, d151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4660 pattern childGuard
    simpa only [d1869, d357, d151, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4662 (pattern : Twelve) (guard : d1848 pattern = 1) : d50 pattern ≤ (0 : Int) + d130 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d50, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4651 pattern childGuard
    simpa only [d50, d130, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d50, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1415 pattern childGuard
    simpa only [d50, d130, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4663 (pattern : Twelve) (guard : d1848 pattern = 1) : d72 pattern ≤ (0 : Int) + d139 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d72, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4600 pattern childGuard
    simpa only [d72, d139, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d72, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4662 pattern childGuard
    simpa only [d72, d139, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4664 (pattern : Twelve) (guard : d1848 pattern = 1) : d76 pattern ≤ (0 : Int) + d138 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d76, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4600 pattern childGuard
    simpa only [d76, d138, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d76, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4645 pattern childGuard
    simpa only [d76, d138, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4665 (pattern : Twelve) (guard : d1848 pattern = 1) : d93 pattern ≤ (0 : Int) + d146 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d93, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4663 pattern childGuard
    simpa only [d93, d146, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d93, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4664 pattern childGuard
    simpa only [d93, d146, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4666 (pattern : Twelve) (guard : d1869 pattern = 1) : d355 pattern ≤ (0 : Int) + d152 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d355, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4665 pattern childGuard
    simpa only [d1869, d355, d152, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d355, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d1869, d355, d152, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4667 (pattern : Twelve) (guard : d1869 pattern = 1) : d360 pattern ≤ (0 : Int) + d154 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d360, d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4661 pattern childGuard
    simpa only [d360, d154, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d360, d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4666 pattern childGuard
    simpa only [d360, d154, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4668 (pattern : Twelve) (guard : d1869 pattern = 1) : d360 pattern ≤ (0 : Int) + d155 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4650 pattern childGuard
    simpa only [d155, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4667 pattern childGuard
    simpa only [d155, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4669 (pattern : Twelve) (guard : d1848 pattern = 1) : d80 pattern ≤ (0 : Int) + d136 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d80, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1610 pattern childGuard
    simpa only [d80, d136, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d80, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4645 pattern childGuard
    simpa only [d80, d136, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4670 (pattern : Twelve) (guard : d1848 pattern = 1) : d97 pattern ≤ (0 : Int) + d144 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d97, d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4609 pattern childGuard
    simpa only [d97, d144, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d97, d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4669 pattern childGuard
    simpa only [d97, d144, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4671 (pattern : Twelve) (guard : d1869 pattern = 1) : d356 pattern ≤ (0 : Int) + d149 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d356, d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4670 pattern childGuard
    simpa only [d1869, d356, d149, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d356, d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4642 pattern childGuard
    simpa only [d1869, d356, d149, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4672 (pattern : Twelve) (guard : d1869 pattern = 1) : d356 pattern ≤ (0 : Int) + d150 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d356, d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4670 pattern childGuard
    simpa only [d1869, d356, d150, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d356, d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4648 pattern childGuard
    simpa only [d1869, d356, d150, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4673 (pattern : Twelve) (guard : d1869 pattern = 1) : d356 pattern ≤ (0 : Int) + d153 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4671 pattern childGuard
    simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4672 pattern childGuard
    simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4674 (pattern : Twelve) (guard : d1848 pattern = 1) : d30 pattern ≤ (0 : Int) + d123 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d30, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1848, d30, d123, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d30, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3283 pattern childGuard
    simpa only [d1848, d30, d123, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4675 (pattern : Twelve) (guard : d1848 pattern = 1) : d30 pattern ≤ (0 : Int) + d132 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1567 pattern childGuard
    simpa only [d132, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4674 pattern childGuard
    simpa only [d132, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4676 (pattern : Twelve) (guard : d1848 pattern = 1) : d80 pattern ≤ (0 : Int) + d141 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d80, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4675 pattern childGuard
    simpa only [d80, d141, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d80, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4645 pattern childGuard
    simpa only [d80, d141, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4677 (pattern : Twelve) (guard : d1848 pattern = 1) : d97 pattern ≤ (0 : Int) + d147 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d97, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4655 pattern childGuard
    simpa only [d97, d147, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d97, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4676 pattern childGuard
    simpa only [d97, d147, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4678 (pattern : Twelve) (guard : d1869 pattern = 1) : d356 pattern ≤ (0 : Int) + d151 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d356, d151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4677 pattern childGuard
    simpa only [d1869, d356, d151, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d356, d151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4660 pattern childGuard
    simpa only [d1869, d356, d151, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4679 (pattern : Twelve) (guard : d1848 pattern = 1) : d80 pattern ≤ (0 : Int) + d138 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d80, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4622 pattern childGuard
    simpa only [d80, d138, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d80, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4645 pattern childGuard
    simpa only [d80, d138, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4680 (pattern : Twelve) (guard : d1848 pattern = 1) : d97 pattern ≤ (0 : Int) + d146 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d97, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4663 pattern childGuard
    simpa only [d97, d146, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d97, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4679 pattern childGuard
    simpa only [d97, d146, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4681 (pattern : Twelve) (guard : d1869 pattern = 1) : d356 pattern ≤ (0 : Int) + d152 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d356, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4680 pattern childGuard
    simpa only [d1869, d356, d152, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d356, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d1869, d356, d152, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4682 (pattern : Twelve) (guard : d1869 pattern = 1) : d356 pattern ≤ (0 : Int) + d154 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4678 pattern childGuard
    simpa only [d154, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4681 pattern childGuard
    simpa only [d154, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4683 (pattern : Twelve) (guard : d1869 pattern = 1) : d356 pattern ≤ (0 : Int) + d155 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4673 pattern childGuard
    simpa only [d155, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4682 pattern childGuard
    simpa only [d155, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4684 (pattern : Twelve) (guard : d1869 pattern = 1) : d363 pattern ≤ (0 : Int) + d155 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4668 pattern childGuard
    simpa only [d363, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4683 pattern childGuard
    simpa only [d363, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4685 (pattern : Twelve) (guard : d1869 pattern = 1) : d365 pattern ≤ (0 : Int) + d156 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d365, d156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4636 pattern childGuard
    simpa only [d365, d156, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d365, d156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4684 pattern childGuard
    simpa only [d365, d156, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4686 (pattern : Twelve) (guard : d1848 pattern = 1) : d853 pattern ≤ (0 : Int) + d853 pattern := by
  omega
theorem c4687 (pattern : Twelve) (guard : d1869 pattern = 1) : d1018 pattern ≤ (0 : Int) + d861 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d1018, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4686 pattern childGuard
    simpa only [d1869, d1018, d861, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d1018, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4344 pattern childGuard
    simpa only [d1869, d1018, d861, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4688 (pattern : Twelve) (guard : d1869 pattern = 1) : d1019 pattern ≤ (0 : Int) + d861 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d1019, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4686 pattern childGuard
    simpa only [d1869, d1019, d861, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d1019, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4346 pattern childGuard
    simpa only [d1869, d1019, d861, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4689 (pattern : Twelve) (guard : d1869 pattern = 1) : d1023 pattern ≤ (0 : Int) + d861 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4687 pattern childGuard
    simpa only [d1023, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4688 pattern childGuard
    simpa only [d1023, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4690 (pattern : Twelve) (guard : d1848 pattern = 1) : d816 pattern ≤ (0 : Int) + d819 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d816, d819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4215 pattern childGuard
    simpa only [d1848, d816, d819, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d816, d819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4591 pattern childGuard
    simpa only [d1848, d816, d819, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4691 (pattern : Twelve) (guard : d1848 pattern = 1) : d824 pattern ≤ (0 : Int) + d828 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d824, d828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4481 pattern childGuard
    simpa only [d824, d828, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d824, d828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4690 pattern childGuard
    simpa only [d824, d828, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4692 (pattern : Twelve) (guard : d1848 pattern = 1) : d838 pattern ≤ (0 : Int) + d842 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d838, d842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4403 pattern childGuard
    simpa only [d838, d842, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d838, d842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4691 pattern childGuard
    simpa only [d838, d842, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4693 (pattern : Twelve) (guard : d1848 pattern = 1) : d825 pattern ≤ (0 : Int) + d825 pattern := by
  omega
theorem c4694 (pattern : Twelve) (guard : d1848 pattern = 1) : d839 pattern ≤ (0 : Int) + d843 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d839, d843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4485 pattern childGuard
    simpa only [d839, d843, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d839, d843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4693 pattern childGuard
    simpa only [d839, d843, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4695 (pattern : Twelve) (guard : d1848 pattern = 1) : d853 pattern ≤ (0 : Int) + d855 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d853, d855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4692 pattern childGuard
    simpa only [d853, d855, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d853, d855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4694 pattern childGuard
    simpa only [d853, d855, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4696 (pattern : Twelve) (guard : d0 pattern = 1) : d916 pattern ≤ (0 : Int) + d856 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4697 (pattern : Twelve) (guard : d1869 pattern = 1) : d1020 pattern ≤ (0 : Int) + d862 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d1020, d862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4695 pattern childGuard
    simpa only [d1869, d1020, d862, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d1020, d862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4696 pattern childGuard
    simpa only [d1869, d1020, d862, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4698 (pattern : Twelve) (guard : d1848 pattern = 1) : d824 pattern ≤ (0 : Int) + d826 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d824, d826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4481 pattern childGuard
    simpa only [d824, d826, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d824, d826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4216 pattern childGuard
    simpa only [d824, d826, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4699 (pattern : Twelve) (guard : d1848 pattern = 1) : d838 pattern ≤ (0 : Int) + d840 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d838, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4600 pattern childGuard
    simpa only [d838, d840, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d838, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4698 pattern childGuard
    simpa only [d838, d840, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4700 (pattern : Twelve) (guard : d1848 pattern = 1) : d17 pattern ≤ (0 : Int) + d827 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4485 pattern childGuard
    simpa only [d827, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1418 pattern childGuard
    simpa only [d827, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4701 (pattern : Twelve) (guard : d1848 pattern = 1) : d839 pattern ≤ (0 : Int) + d841 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d839, d841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4700 pattern childGuard
    simpa only [d839, d841, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d839, d841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4693 pattern childGuard
    simpa only [d839, d841, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4702 (pattern : Twelve) (guard : d1848 pattern = 1) : d853 pattern ≤ (0 : Int) + d854 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d853, d854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4699 pattern childGuard
    simpa only [d853, d854, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d853, d854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4701 pattern childGuard
    simpa only [d853, d854, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4703 (pattern : Twelve) (guard : d1869 pattern = 1) : d1021 pattern ≤ (0 : Int) + d863 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d1021, d863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4702 pattern childGuard
    simpa only [d1869, d1021, d863, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d1021, d863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d1869, d1021, d863, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4704 (pattern : Twelve) (guard : d1869 pattern = 1) : d1024 pattern ≤ (0 : Int) + d867 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1024, d867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4697 pattern childGuard
    simpa only [d1024, d867, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1024, d867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4703 pattern childGuard
    simpa only [d1024, d867, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4705 (pattern : Twelve) (guard : d1869 pattern = 1) : d1025 pattern ≤ (0 : Int) + d869 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1025, d869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4689 pattern childGuard
    simpa only [d1025, d869, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1025, d869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4704 pattern childGuard
    simpa only [d1025, d869, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4706 (pattern : Twelve) (guard : d1848 pattern = 1) : d838 pattern ≤ (0 : Int) + d838 pattern := by
  omega
theorem c4707 (pattern : Twelve) (guard : d1848 pattern = 1) : d846 pattern ≤ (0 : Int) + d839 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d846, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1708 pattern childGuard
    simpa only [d846, d839, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d846, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4693 pattern childGuard
    simpa only [d846, d839, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4708 (pattern : Twelve) (guard : d1848 pattern = 1) : d857 pattern ≤ (0 : Int) + d853 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d857, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4706 pattern childGuard
    simpa only [d857, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d857, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4707 pattern childGuard
    simpa only [d857, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4709 (pattern : Twelve) (guard : d1869 pattern = 1) : d1022 pattern ≤ (0 : Int) + d861 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d1022, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4708 pattern childGuard
    simpa only [d1869, d1022, d861, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d1022, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4356 pattern childGuard
    simpa only [d1869, d1022, d861, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4710 (pattern : Twelve) (guard : d1848 pattern = 1) : d846 pattern ≤ (0 : Int) + d843 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d846, d843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4503 pattern childGuard
    simpa only [d846, d843, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d846, d843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4693 pattern childGuard
    simpa only [d846, d843, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4711 (pattern : Twelve) (guard : d1848 pattern = 1) : d857 pattern ≤ (0 : Int) + d855 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d857, d855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4692 pattern childGuard
    simpa only [d857, d855, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d857, d855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4710 pattern childGuard
    simpa only [d857, d855, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4712 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d856 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4713 (pattern : Twelve) (guard : d1869 pattern = 1) : d1022 pattern ≤ (0 : Int) + d862 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d1022, d862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4711 pattern childGuard
    simpa only [d1869, d1022, d862, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d1022, d862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4712 pattern childGuard
    simpa only [d1869, d1022, d862, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4714 (pattern : Twelve) (guard : d1848 pattern = 1) : d823 pattern ≤ (0 : Int) + d827 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4503 pattern childGuard
    simpa only [d827, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1441 pattern childGuard
    simpa only [d827, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4715 (pattern : Twelve) (guard : d1848 pattern = 1) : d846 pattern ≤ (0 : Int) + d841 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d846, d841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4714 pattern childGuard
    simpa only [d846, d841, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d846, d841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4693 pattern childGuard
    simpa only [d846, d841, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4716 (pattern : Twelve) (guard : d1848 pattern = 1) : d857 pattern ≤ (0 : Int) + d854 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d857, d854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4699 pattern childGuard
    simpa only [d857, d854, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d857, d854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4715 pattern childGuard
    simpa only [d857, d854, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4717 (pattern : Twelve) (guard : d1869 pattern = 1) : d1022 pattern ≤ (0 : Int) + d863 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d1022, d863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4716 pattern childGuard
    simpa only [d1869, d1022, d863, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d1022, d863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d1869, d1022, d863, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4718 (pattern : Twelve) (guard : d1869 pattern = 1) : d1022 pattern ≤ (0 : Int) + d867 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4713 pattern childGuard
    simpa only [d867, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4717 pattern childGuard
    simpa only [d867, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4719 (pattern : Twelve) (guard : d1869 pattern = 1) : d1022 pattern ≤ (0 : Int) + d869 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4709 pattern childGuard
    simpa only [d869, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4718 pattern childGuard
    simpa only [d869, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4720 (pattern : Twelve) (guard : d1869 pattern = 1) : d1026 pattern ≤ (0 : Int) + d869 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4705 pattern childGuard
    simpa only [d1026, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4719 pattern childGuard
    simpa only [d1026, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4721 (pattern : Twelve) (guard : d1869 pattern = 1) : d1021 pattern ≤ (0 : Int) + d861 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d1021, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4686 pattern childGuard
    simpa only [d1869, d1021, d861, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d1021, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4356 pattern childGuard
    simpa only [d1869, d1021, d861, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4722 (pattern : Twelve) (guard : d1869 pattern = 1) : d1021 pattern ≤ (0 : Int) + d862 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d1021, d862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4695 pattern childGuard
    simpa only [d1869, d1021, d862, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d1021, d862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4712 pattern childGuard
    simpa only [d1869, d1021, d862, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4723 (pattern : Twelve) (guard : d1869 pattern = 1) : d1021 pattern ≤ (0 : Int) + d867 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4722 pattern childGuard
    simpa only [d867, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4703 pattern childGuard
    simpa only [d867, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4724 (pattern : Twelve) (guard : d1869 pattern = 1) : d1021 pattern ≤ (0 : Int) + d869 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4721 pattern childGuard
    simpa only [d869, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4723 pattern childGuard
    simpa only [d869, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4725 (pattern : Twelve) (guard : d1869 pattern = 1) : d1027 pattern ≤ (0 : Int) + d869 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4724 pattern childGuard
    simpa only [d1027, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4719 pattern childGuard
    simpa only [d1027, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4726 (pattern : Twelve) (guard : d1869 pattern = 1) : d1028 pattern ≤ (0 : Int) + d869 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4720 pattern childGuard
    simpa only [d1028, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4725 pattern childGuard
    simpa only [d1028, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4727 (pattern : Twelve) (guard : d0 pattern = 1) : d1 pattern ≤ (0 : Int) + d872 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4728 (pattern : Twelve) (guard : d1848 pattern = 1) : d27 pattern ≤ (0 : Int) + d874 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d27, d874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c240 pattern childGuard
    simpa only [d1848, d27, d874, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d27, d874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4727 pattern childGuard
    simpa only [d1848, d27, d874, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4729 (pattern : Twelve) (guard : d1848 pattern = 1) : d816 pattern ≤ (0 : Int) + d875 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d816, d875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4215 pattern childGuard
    simpa only [d1848, d816, d875, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d816, d875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4727 pattern childGuard
    simpa only [d1848, d816, d875, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4730 (pattern : Twelve) (guard : d1848 pattern = 1) : d824 pattern ≤ (0 : Int) + d882 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d824, d882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4728 pattern childGuard
    simpa only [d824, d882, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d824, d882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4729 pattern childGuard
    simpa only [d824, d882, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4731 (pattern : Twelve) (guard : d1848 pattern = 1) : d838 pattern ≤ (0 : Int) + d890 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d838, d890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1560 pattern childGuard
    simpa only [d838, d890, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d838, d890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4730 pattern childGuard
    simpa only [d838, d890, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4732 (pattern : Twelve) (guard : d1848 pattern = 1) : d817 pattern ≤ (0 : Int) + d876 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d817, d876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c328 pattern childGuard
    simpa only [d1848, d817, d876, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d817, d876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4576 pattern childGuard
    simpa only [d1848, d817, d876, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4733 (pattern : Twelve) (guard : d1848 pattern = 1) : d825 pattern ≤ (0 : Int) + d883 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d825, d883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4732 pattern childGuard
    simpa only [d825, d883, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d825, d883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2806 pattern childGuard
    simpa only [d825, d883, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4734 (pattern : Twelve) (guard : d1848 pattern = 1) : d839 pattern ≤ (0 : Int) + d891 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d839, d891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1670 pattern childGuard
    simpa only [d839, d891, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d839, d891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4733 pattern childGuard
    simpa only [d839, d891, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4735 (pattern : Twelve) (guard : d1848 pattern = 1) : d853 pattern ≤ (0 : Int) + d898 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d853, d898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4731 pattern childGuard
    simpa only [d853, d898, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d853, d898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4734 pattern childGuard
    simpa only [d853, d898, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4736 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d899 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4737 (pattern : Twelve) (guard : d1869 pattern = 1) : d1021 pattern ≤ (0 : Int) + d902 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d1021, d902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4735 pattern childGuard
    simpa only [d1869, d1021, d902, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d1021, d902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4736 pattern childGuard
    simpa only [d1869, d1021, d902, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4738 (pattern : Twelve) (guard : d0 pattern = 1) : d1 pattern ≤ (0 : Int) + d815 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4739 (pattern : Twelve) (guard : d1848 pattern = 1) : d27 pattern ≤ (0 : Int) + d877 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d27, d877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c240 pattern childGuard
    simpa only [d1848, d27, d877, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d27, d877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4738 pattern childGuard
    simpa only [d1848, d27, d877, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4740 (pattern : Twelve) (guard : d0 pattern = 1) : d1 pattern ≤ (0 : Int) + d24 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4741 (pattern : Twelve) (guard : d1848 pattern = 1) : d816 pattern ≤ (0 : Int) + d878 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d816, d878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4215 pattern childGuard
    simpa only [d1848, d816, d878, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d816, d878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4740 pattern childGuard
    simpa only [d1848, d816, d878, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4742 (pattern : Twelve) (guard : d1848 pattern = 1) : d824 pattern ≤ (0 : Int) + d885 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d824, d885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4739 pattern childGuard
    simpa only [d824, d885, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d824, d885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4741 pattern childGuard
    simpa only [d824, d885, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4743 (pattern : Twelve) (guard : d1848 pattern = 1) : d838 pattern ≤ (0 : Int) + d894 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d838, d894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4403 pattern childGuard
    simpa only [d838, d894, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d838, d894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4742 pattern childGuard
    simpa only [d838, d894, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4744 (pattern : Twelve) (guard : d0 pattern = 1) : d17 pattern ≤ (0 : Int) + d119 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4745 (pattern : Twelve) (guard : d1848 pattern = 1) : d17 pattern ≤ (0 : Int) + d879 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c240 pattern childGuard
    simpa only [d1848, d879, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4744 pattern childGuard
    simpa only [d1848, d879, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4746 (pattern : Twelve) (guard : d1848 pattern = 1) : d17 pattern ≤ (0 : Int) + d886 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4485 pattern childGuard
    simpa only [d886, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4745 pattern childGuard
    simpa only [d886, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4747 (pattern : Twelve) (guard : d1848 pattern = 1) : d839 pattern ≤ (0 : Int) + d895 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d839, d895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4746 pattern childGuard
    simpa only [d839, d895, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d839, d895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4733 pattern childGuard
    simpa only [d839, d895, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4748 (pattern : Twelve) (guard : d1848 pattern = 1) : d853 pattern ≤ (0 : Int) + d900 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d853, d900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4743 pattern childGuard
    simpa only [d853, d900, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d853, d900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4747 pattern childGuard
    simpa only [d853, d900, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4749 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d901 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4750 (pattern : Twelve) (guard : d1869 pattern = 1) : d1021 pattern ≤ (0 : Int) + d903 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d1021, d903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4748 pattern childGuard
    simpa only [d1869, d1021, d903, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d1021, d903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4749 pattern childGuard
    simpa only [d1869, d1021, d903, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4751 (pattern : Twelve) (guard : d1848 pattern = 1) : d824 pattern ≤ (0 : Int) + d884 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d824, d884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4739 pattern childGuard
    simpa only [d824, d884, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d824, d884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4216 pattern childGuard
    simpa only [d824, d884, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4752 (pattern : Twelve) (guard : d1848 pattern = 1) : d838 pattern ≤ (0 : Int) + d892 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d838, d892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4600 pattern childGuard
    simpa only [d838, d892, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d838, d892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4751 pattern childGuard
    simpa only [d838, d892, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4753 (pattern : Twelve) (guard : d1848 pattern = 1) : d839 pattern ≤ (0 : Int) + d893 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d839, d893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4700 pattern childGuard
    simpa only [d839, d893, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d839, d893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4733 pattern childGuard
    simpa only [d839, d893, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4754 (pattern : Twelve) (guard : d1848 pattern = 1) : d853 pattern ≤ (0 : Int) + d899 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d853, d899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4752 pattern childGuard
    simpa only [d853, d899, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d853, d899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4753 pattern childGuard
    simpa only [d853, d899, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4755 (pattern : Twelve) (guard : d1869 pattern = 1) : d1021 pattern ≤ (0 : Int) + d904 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d1021, d904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4754 pattern childGuard
    simpa only [d1869, d1021, d904, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d1021, d904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d1869, d1021, d904, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4756 (pattern : Twelve) (guard : d1869 pattern = 1) : d1021 pattern ≤ (0 : Int) + d905 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4750 pattern childGuard
    simpa only [d905, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4755 pattern childGuard
    simpa only [d905, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4757 (pattern : Twelve) (guard : d1869 pattern = 1) : d1021 pattern ≤ (0 : Int) + d906 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4737 pattern childGuard
    simpa only [d906, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4756 pattern childGuard
    simpa only [d906, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4758 (pattern : Twelve) (guard : d1848 pattern = 1) : d846 pattern ≤ (0 : Int) + d891 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d846, d891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1708 pattern childGuard
    simpa only [d846, d891, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d846, d891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4733 pattern childGuard
    simpa only [d846, d891, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4759 (pattern : Twelve) (guard : d1848 pattern = 1) : d857 pattern ≤ (0 : Int) + d898 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d857, d898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4731 pattern childGuard
    simpa only [d857, d898, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d857, d898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4758 pattern childGuard
    simpa only [d857, d898, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
