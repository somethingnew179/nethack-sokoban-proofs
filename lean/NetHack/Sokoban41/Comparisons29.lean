/- Staged soko4-1 certificate. No result until all kernel checks pass. -/
import NetHack.Sokoban41.Comparisons28
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban41.Diagram
theorem c4640 (pattern : Ten) (guard : d606 pattern = 1) : d138 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d359 pattern = 1 := by simpa only [d606, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c157 pattern childGuard
    simpa only [d606, d138, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d606, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1108 pattern childGuard
    simpa only [d606, d138, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4641 (pattern : Ten) (guard : d607 pattern = 1) : d139 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d606 pattern = 1 := by simpa only [d607, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4640 pattern childGuard
    simpa only [d607, d139, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d607, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2784 pattern childGuard
    simpa only [d607, d139, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4642 (pattern : Ten) (guard : d608 pattern = 1) : d142 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d607 pattern = 1 := by simpa only [d608, d142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4641 pattern childGuard
    simpa only [d608, d142, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d608, d142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4566 pattern childGuard
    simpa only [d608, d142, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4643 (pattern : Ten) (guard : d0 pattern = 1) : d143 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4644 (pattern : Ten) (guard : d609 pattern = 1) : d145 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d608 pattern = 1 := by simpa only [d609, d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4642 pattern childGuard
    simpa only [d609, d145, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d609, d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4643 pattern childGuard
    simpa only [d609, d145, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4645 (pattern : Ten) (guard : d0 pattern = 1) : d146 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4646 (pattern : Ten) (guard : d610 pattern = 1) : d147 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d609 pattern = 1 := by simpa only [d610, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4644 pattern childGuard
    simpa only [d610, d147, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d610, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4645 pattern childGuard
    simpa only [d610, d147, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4647 (pattern : Ten) (guard : d611 pattern = 1) : d148 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d610 pattern = 1 := by simpa only [d611, d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4646 pattern childGuard
    simpa only [d611, d148, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d611, d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4572 pattern childGuard
    simpa only [d611, d148, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4648 (pattern : Ten) (guard : d612 pattern = 1) : d149 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d611 pattern = 1 := by simpa only [d612, d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4647 pattern childGuard
    simpa only [d612, d149, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d612, d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4574 pattern childGuard
    simpa only [d612, d149, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4649 (pattern : Ten) (guard : d0 pattern = 1) : d9 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4650 (pattern : Ten) (guard : d609 pattern = 1) : d150 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d608 pattern = 1 := by simpa only [d609, d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4580 pattern childGuard
    simpa only [d609, d150, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d609, d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4649 pattern childGuard
    simpa only [d609, d150, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4651 (pattern : Ten) (guard : d610 pattern = 1) : d151 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d609 pattern = 1 := by simpa only [d610, d151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4650 pattern childGuard
    simpa only [d610, d151, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d610, d151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4581 pattern childGuard
    simpa only [d610, d151, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4652 (pattern : Ten) (guard : d0 pattern = 1) : d152 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4653 (pattern : Ten) (guard : d611 pattern = 1) : d154 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d610 pattern = 1 := by simpa only [d611, d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4651 pattern childGuard
    simpa only [d611, d154, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d611, d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4652 pattern childGuard
    simpa only [d611, d154, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4654 (pattern : Ten) (guard : d0 pattern = 1) : d155 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4655 (pattern : Ten) (guard : d612 pattern = 1) : d156 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d611 pattern = 1 := by simpa only [d612, d156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4653 pattern childGuard
    simpa only [d612, d156, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d612, d156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4654 pattern childGuard
    simpa only [d612, d156, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4656 (pattern : Ten) (guard : d0 pattern = 1) : d55 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4657 (pattern : Ten) (guard : d609 pattern = 1) : d160 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d608 pattern = 1 := by simpa only [d609, d160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4580 pattern childGuard
    simpa only [d609, d160, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d609, d160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4656 pattern childGuard
    simpa only [d609, d160, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4658 (pattern : Ten) (guard : d0 pattern = 1) : d161 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4659 (pattern : Ten) (guard : d610 pattern = 1) : d165 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d609 pattern = 1 := by simpa only [d610, d165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4657 pattern childGuard
    simpa only [d610, d165, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d610, d165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4658 pattern childGuard
    simpa only [d610, d165, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4660 (pattern : Ten) (guard : d0 pattern = 1) : d166 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4661 (pattern : Ten) (guard : d611 pattern = 1) : d168 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d610 pattern = 1 := by simpa only [d611, d168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4659 pattern childGuard
    simpa only [d611, d168, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d611, d168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4660 pattern childGuard
    simpa only [d611, d168, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4662 (pattern : Ten) (guard : d0 pattern = 1) : d169 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4663 (pattern : Ten) (guard : d612 pattern = 1) : d170 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d611 pattern = 1 := by simpa only [d612, d170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4661 pattern childGuard
    simpa only [d612, d170, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d612, d170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4662 pattern childGuard
    simpa only [d612, d170, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4664 (pattern : Ten) (guard : d635 pattern = 1) : d0 pattern ≤ (0 : Int) + d0 pattern := by
  omega
theorem c4665 (pattern : Ten) (guard : d636 pattern = 1) : d17 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d635 pattern = 1 := by simpa only [d636, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4664 pattern childGuard
    simpa only [d636, d17, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d636, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2784 pattern childGuard
    simpa only [d636, d17, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4666 (pattern : Ten) (guard : d637 pattern = 1) : d23 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d636 pattern = 1 := by simpa only [d637, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4665 pattern childGuard
    simpa only [d637, d23, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d637, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4566 pattern childGuard
    simpa only [d637, d23, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4667 (pattern : Ten) (guard : d638 pattern = 1) : d29 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d637 pattern = 1 := by simpa only [d638, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4666 pattern childGuard
    simpa only [d638, d29, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d638, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4568 pattern childGuard
    simpa only [d638, d29, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4668 (pattern : Ten) (guard : d639 pattern = 1) : d33 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d638 pattern = 1 := by simpa only [d639, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4667 pattern childGuard
    simpa only [d639, d33, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d639, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4570 pattern childGuard
    simpa only [d639, d33, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4669 (pattern : Ten) (guard : d640 pattern = 1) : d35 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d639 pattern = 1 := by simpa only [d640, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4668 pattern childGuard
    simpa only [d640, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d640, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4572 pattern childGuard
    simpa only [d640, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4670 (pattern : Ten) (guard : d641 pattern = 1) : d37 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d640 pattern = 1 := by simpa only [d641, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4669 pattern childGuard
    simpa only [d641, d37, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d641, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4574 pattern childGuard
    simpa only [d641, d37, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4671 (pattern : Ten) (guard : d407 pattern = 1) : d0 pattern ≤ (0 : Int) + d0 pattern := by
  omega
theorem c4672 (pattern : Ten) (guard : d635 pattern = 1) : d15 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d407 pattern = 1 := by simpa only [d635, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4671 pattern childGuard
    simpa only [d635, d15, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d635, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c410 pattern childGuard
    simpa only [d635, d15, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4673 (pattern : Ten) (guard : d636 pattern = 1) : d48 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d635 pattern = 1 := by simpa only [d636, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4672 pattern childGuard
    simpa only [d636, d48, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d636, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4577 pattern childGuard
    simpa only [d636, d48, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4674 (pattern : Ten) (guard : d637 pattern = 1) : d54 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d636 pattern = 1 := by simpa only [d637, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4673 pattern childGuard
    simpa only [d637, d54, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d637, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4579 pattern childGuard
    simpa only [d637, d54, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4675 (pattern : Ten) (guard : d638 pattern = 1) : d54 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d637 pattern = 1 := by simpa only [d638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4674 pattern childGuard
    simpa only [d638, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4581 pattern childGuard
    simpa only [d638, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4676 (pattern : Ten) (guard : d639 pattern = 1) : d54 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d638 pattern = 1 := by simpa only [d639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4675 pattern childGuard
    simpa only [d639, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4581 pattern childGuard
    simpa only [d639, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4677 (pattern : Ten) (guard : d640 pattern = 1) : d64 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d639 pattern = 1 := by simpa only [d640, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4676 pattern childGuard
    simpa only [d640, d64, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d640, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4584 pattern childGuard
    simpa only [d640, d64, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4678 (pattern : Ten) (guard : d641 pattern = 1) : d66 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d640 pattern = 1 := by simpa only [d641, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4677 pattern childGuard
    simpa only [d641, d66, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d641, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4586 pattern childGuard
    simpa only [d641, d66, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4679 (pattern : Ten) (guard : d638 pattern = 1) : d73 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d637 pattern = 1 := by simpa only [d638, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4666 pattern childGuard
    simpa only [d638, d73, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d638, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4588 pattern childGuard
    simpa only [d638, d73, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4680 (pattern : Ten) (guard : d639 pattern = 1) : d77 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d638 pattern = 1 := by simpa only [d639, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4679 pattern childGuard
    simpa only [d639, d77, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d639, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4590 pattern childGuard
    simpa only [d639, d77, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4681 (pattern : Ten) (guard : d640 pattern = 1) : d79 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d639 pattern = 1 := by simpa only [d640, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4680 pattern childGuard
    simpa only [d640, d79, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d640, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4592 pattern childGuard
    simpa only [d640, d79, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4682 (pattern : Ten) (guard : d641 pattern = 1) : d81 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d640 pattern = 1 := by simpa only [d641, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4681 pattern childGuard
    simpa only [d641, d81, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d641, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4594 pattern childGuard
    simpa only [d641, d81, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4683 (pattern : Ten) (guard : d639 pattern = 1) : d82 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d638 pattern = 1 := by simpa only [d639, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4675 pattern childGuard
    simpa only [d639, d82, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d639, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4596 pattern childGuard
    simpa only [d639, d82, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4684 (pattern : Ten) (guard : d640 pattern = 1) : d83 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d639 pattern = 1 := by simpa only [d640, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4683 pattern childGuard
    simpa only [d640, d83, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d640, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4598 pattern childGuard
    simpa only [d640, d83, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4685 (pattern : Ten) (guard : d641 pattern = 1) : d85 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d640 pattern = 1 := by simpa only [d641, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4684 pattern childGuard
    simpa only [d641, d85, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d641, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4600 pattern childGuard
    simpa only [d641, d85, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4686 (pattern : Ten) (guard : d635 pattern = 1) : d86 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d407 pattern = 1 := by simpa only [d635, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4671 pattern childGuard
    simpa only [d635, d86, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d635, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c603 pattern childGuard
    simpa only [d635, d86, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4687 (pattern : Ten) (guard : d636 pattern = 1) : d87 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d635 pattern = 1 := by simpa only [d636, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4686 pattern childGuard
    simpa only [d636, d87, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d636, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4603 pattern childGuard
    simpa only [d636, d87, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4688 (pattern : Ten) (guard : d637 pattern = 1) : d93 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d636 pattern = 1 := by simpa only [d637, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4687 pattern childGuard
    simpa only [d637, d93, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d637, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4605 pattern childGuard
    simpa only [d637, d93, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4689 (pattern : Ten) (guard : d638 pattern = 1) : d99 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d637 pattern = 1 := by simpa only [d638, d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4688 pattern childGuard
    simpa only [d638, d99, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d638, d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4607 pattern childGuard
    simpa only [d638, d99, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4690 (pattern : Ten) (guard : d639 pattern = 1) : d103 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d638 pattern = 1 := by simpa only [d639, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4689 pattern childGuard
    simpa only [d639, d103, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d639, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4609 pattern childGuard
    simpa only [d639, d103, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4691 (pattern : Ten) (guard : d640 pattern = 1) : d105 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d639 pattern = 1 := by simpa only [d640, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4690 pattern childGuard
    simpa only [d640, d105, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d640, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4611 pattern childGuard
    simpa only [d640, d105, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4692 (pattern : Ten) (guard : d641 pattern = 1) : d107 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d640 pattern = 1 := by simpa only [d641, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4691 pattern childGuard
    simpa only [d641, d107, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d641, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4613 pattern childGuard
    simpa only [d641, d107, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4693 (pattern : Ten) (guard : d636 pattern = 1) : d108 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d635 pattern = 1 := by simpa only [d636, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4672 pattern childGuard
    simpa only [d636, d108, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d636, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c686 pattern childGuard
    simpa only [d636, d108, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4694 (pattern : Ten) (guard : d637 pattern = 1) : d109 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d636 pattern = 1 := by simpa only [d637, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4693 pattern childGuard
    simpa only [d637, d109, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d637, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4616 pattern childGuard
    simpa only [d637, d109, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4695 (pattern : Ten) (guard : d638 pattern = 1) : d115 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d637 pattern = 1 := by simpa only [d638, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4694 pattern childGuard
    simpa only [d638, d115, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d638, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4618 pattern childGuard
    simpa only [d638, d115, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4696 (pattern : Ten) (guard : d639 pattern = 1) : d119 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d638 pattern = 1 := by simpa only [d639, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4695 pattern childGuard
    simpa only [d639, d119, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d639, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4620 pattern childGuard
    simpa only [d639, d119, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4697 (pattern : Ten) (guard : d640 pattern = 1) : d121 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d639 pattern = 1 := by simpa only [d640, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4696 pattern childGuard
    simpa only [d640, d121, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d640, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4622 pattern childGuard
    simpa only [d640, d121, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4698 (pattern : Ten) (guard : d641 pattern = 1) : d123 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d640 pattern = 1 := by simpa only [d641, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4697 pattern childGuard
    simpa only [d641, d123, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d641, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4624 pattern childGuard
    simpa only [d641, d123, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4699 (pattern : Ten) (guard : d637 pattern = 1) : d124 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d636 pattern = 1 := by simpa only [d637, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4673 pattern childGuard
    simpa only [d637, d124, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d637, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4626 pattern childGuard
    simpa only [d637, d124, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4700 (pattern : Ten) (guard : d638 pattern = 1) : d125 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d637 pattern = 1 := by simpa only [d638, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4699 pattern childGuard
    simpa only [d638, d125, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d638, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4628 pattern childGuard
    simpa only [d638, d125, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4701 (pattern : Ten) (guard : d639 pattern = 1) : d128 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d638 pattern = 1 := by simpa only [d639, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4700 pattern childGuard
    simpa only [d639, d128, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d639, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4628 pattern childGuard
    simpa only [d639, d128, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4702 (pattern : Ten) (guard : d640 pattern = 1) : d130 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d639 pattern = 1 := by simpa only [d640, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4701 pattern childGuard
    simpa only [d640, d130, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d640, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4631 pattern childGuard
    simpa only [d640, d130, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4703 (pattern : Ten) (guard : d641 pattern = 1) : d132 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d640 pattern = 1 := by simpa only [d641, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4702 pattern childGuard
    simpa only [d641, d132, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d641, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4633 pattern childGuard
    simpa only [d641, d132, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4704 (pattern : Ten) (guard : d641 pattern = 1) : d133 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d640 pattern = 1 := by simpa only [d641, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4677 pattern childGuard
    simpa only [d641, d133, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d641, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4596 pattern childGuard
    simpa only [d641, d133, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4705 (pattern : Ten) (guard : d640 pattern = 1) : d134 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d639 pattern = 1 := by simpa only [d640, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4676 pattern childGuard
    simpa only [d640, d134, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d640, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4636 pattern childGuard
    simpa only [d640, d134, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4706 (pattern : Ten) (guard : d641 pattern = 1) : d135 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d640 pattern = 1 := by simpa only [d641, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4705 pattern childGuard
    simpa only [d641, d135, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d641, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4638 pattern childGuard
    simpa only [d641, d135, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4707 (pattern : Ten) (guard : d635 pattern = 1) : d138 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d407 pattern = 1 := by simpa only [d635, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4671 pattern childGuard
    simpa only [d635, d138, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d635, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1108 pattern childGuard
    simpa only [d635, d138, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4708 (pattern : Ten) (guard : d636 pattern = 1) : d139 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d635 pattern = 1 := by simpa only [d636, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4707 pattern childGuard
    simpa only [d636, d139, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d636, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2784 pattern childGuard
    simpa only [d636, d139, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4709 (pattern : Ten) (guard : d637 pattern = 1) : d142 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d636 pattern = 1 := by simpa only [d637, d142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4708 pattern childGuard
    simpa only [d637, d142, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d637, d142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4566 pattern childGuard
    simpa only [d637, d142, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4710 (pattern : Ten) (guard : d638 pattern = 1) : d145 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d637 pattern = 1 := by simpa only [d638, d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4709 pattern childGuard
    simpa only [d638, d145, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d638, d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4643 pattern childGuard
    simpa only [d638, d145, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4711 (pattern : Ten) (guard : d639 pattern = 1) : d147 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d638 pattern = 1 := by simpa only [d639, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4710 pattern childGuard
    simpa only [d639, d147, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d639, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4645 pattern childGuard
    simpa only [d639, d147, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4712 (pattern : Ten) (guard : d640 pattern = 1) : d148 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d639 pattern = 1 := by simpa only [d640, d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4711 pattern childGuard
    simpa only [d640, d148, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d640, d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4572 pattern childGuard
    simpa only [d640, d148, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4713 (pattern : Ten) (guard : d641 pattern = 1) : d149 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d640 pattern = 1 := by simpa only [d641, d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4712 pattern childGuard
    simpa only [d641, d149, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d641, d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4574 pattern childGuard
    simpa only [d641, d149, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4714 (pattern : Ten) (guard : d638 pattern = 1) : d150 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d637 pattern = 1 := by simpa only [d638, d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4674 pattern childGuard
    simpa only [d638, d150, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d638, d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4649 pattern childGuard
    simpa only [d638, d150, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4715 (pattern : Ten) (guard : d639 pattern = 1) : d151 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d638 pattern = 1 := by simpa only [d639, d151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4714 pattern childGuard
    simpa only [d639, d151, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d639, d151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4581 pattern childGuard
    simpa only [d639, d151, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4716 (pattern : Ten) (guard : d640 pattern = 1) : d154 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d639 pattern = 1 := by simpa only [d640, d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4715 pattern childGuard
    simpa only [d640, d154, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d640, d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4652 pattern childGuard
    simpa only [d640, d154, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4717 (pattern : Ten) (guard : d641 pattern = 1) : d156 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d640 pattern = 1 := by simpa only [d641, d156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4716 pattern childGuard
    simpa only [d641, d156, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d641, d156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4654 pattern childGuard
    simpa only [d641, d156, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4718 (pattern : Ten) (guard : d638 pattern = 1) : d160 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d637 pattern = 1 := by simpa only [d638, d160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4674 pattern childGuard
    simpa only [d638, d160, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d638, d160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4656 pattern childGuard
    simpa only [d638, d160, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4719 (pattern : Ten) (guard : d639 pattern = 1) : d165 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d638 pattern = 1 := by simpa only [d639, d165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4718 pattern childGuard
    simpa only [d639, d165, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d639, d165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4658 pattern childGuard
    simpa only [d639, d165, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4720 (pattern : Ten) (guard : d640 pattern = 1) : d168 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d639 pattern = 1 := by simpa only [d640, d168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4719 pattern childGuard
    simpa only [d640, d168, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d640, d168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4660 pattern childGuard
    simpa only [d640, d168, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4721 (pattern : Ten) (guard : d641 pattern = 1) : d170 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d640 pattern = 1 := by simpa only [d641, d170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4720 pattern childGuard
    simpa only [d641, d170, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d641, d170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4662 pattern childGuard
    simpa only [d641, d170, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4722 (pattern : Ten) (guard : d664 pattern = 1) : d0 pattern ≤ (0 : Int) + d0 pattern := by
  omega
theorem c4723 (pattern : Ten) (guard : d665 pattern = 1) : d17 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d664 pattern = 1 := by simpa only [d665, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4722 pattern childGuard
    simpa only [d665, d17, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d665, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2784 pattern childGuard
    simpa only [d665, d17, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4724 (pattern : Ten) (guard : d666 pattern = 1) : d23 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d665 pattern = 1 := by simpa only [d666, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4723 pattern childGuard
    simpa only [d666, d23, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d666, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4566 pattern childGuard
    simpa only [d666, d23, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4725 (pattern : Ten) (guard : d667 pattern = 1) : d29 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d666 pattern = 1 := by simpa only [d667, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4724 pattern childGuard
    simpa only [d667, d29, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d667, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4568 pattern childGuard
    simpa only [d667, d29, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4726 (pattern : Ten) (guard : d668 pattern = 1) : d33 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d667 pattern = 1 := by simpa only [d668, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4725 pattern childGuard
    simpa only [d668, d33, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d668, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4570 pattern childGuard
    simpa only [d668, d33, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4727 (pattern : Ten) (guard : d669 pattern = 1) : d35 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d668 pattern = 1 := by simpa only [d669, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4726 pattern childGuard
    simpa only [d669, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d669, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4572 pattern childGuard
    simpa only [d669, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4728 (pattern : Ten) (guard : d670 pattern = 1) : d37 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d669 pattern = 1 := by simpa only [d670, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4727 pattern childGuard
    simpa only [d670, d37, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d670, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4574 pattern childGuard
    simpa only [d670, d37, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4729 (pattern : Ten) (guard : d447 pattern = 1) : d0 pattern ≤ (0 : Int) + d0 pattern := by
  omega
theorem c4730 (pattern : Ten) (guard : d664 pattern = 1) : d15 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d447 pattern = 1 := by simpa only [d664, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4729 pattern childGuard
    simpa only [d664, d15, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d664, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c410 pattern childGuard
    simpa only [d664, d15, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4731 (pattern : Ten) (guard : d665 pattern = 1) : d48 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d664 pattern = 1 := by simpa only [d665, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4730 pattern childGuard
    simpa only [d665, d48, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d665, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4577 pattern childGuard
    simpa only [d665, d48, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4732 (pattern : Ten) (guard : d666 pattern = 1) : d54 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d665 pattern = 1 := by simpa only [d666, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4731 pattern childGuard
    simpa only [d666, d54, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d666, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4579 pattern childGuard
    simpa only [d666, d54, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4733 (pattern : Ten) (guard : d667 pattern = 1) : d54 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d666 pattern = 1 := by simpa only [d667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4732 pattern childGuard
    simpa only [d667, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4581 pattern childGuard
    simpa only [d667, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4734 (pattern : Ten) (guard : d668 pattern = 1) : d54 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d667 pattern = 1 := by simpa only [d668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4733 pattern childGuard
    simpa only [d668, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4581 pattern childGuard
    simpa only [d668, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4735 (pattern : Ten) (guard : d669 pattern = 1) : d64 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d668 pattern = 1 := by simpa only [d669, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4734 pattern childGuard
    simpa only [d669, d64, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d669, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4584 pattern childGuard
    simpa only [d669, d64, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4736 (pattern : Ten) (guard : d670 pattern = 1) : d66 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d669 pattern = 1 := by simpa only [d670, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4735 pattern childGuard
    simpa only [d670, d66, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d670, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4586 pattern childGuard
    simpa only [d670, d66, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4737 (pattern : Ten) (guard : d667 pattern = 1) : d73 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d666 pattern = 1 := by simpa only [d667, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4724 pattern childGuard
    simpa only [d667, d73, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d667, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4588 pattern childGuard
    simpa only [d667, d73, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4738 (pattern : Ten) (guard : d668 pattern = 1) : d77 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d667 pattern = 1 := by simpa only [d668, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4737 pattern childGuard
    simpa only [d668, d77, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d668, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4590 pattern childGuard
    simpa only [d668, d77, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4739 (pattern : Ten) (guard : d669 pattern = 1) : d79 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d668 pattern = 1 := by simpa only [d669, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4738 pattern childGuard
    simpa only [d669, d79, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d669, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4592 pattern childGuard
    simpa only [d669, d79, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4740 (pattern : Ten) (guard : d670 pattern = 1) : d81 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d669 pattern = 1 := by simpa only [d670, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4739 pattern childGuard
    simpa only [d670, d81, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d670, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4594 pattern childGuard
    simpa only [d670, d81, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4741 (pattern : Ten) (guard : d668 pattern = 1) : d82 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d667 pattern = 1 := by simpa only [d668, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4733 pattern childGuard
    simpa only [d668, d82, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d668, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4596 pattern childGuard
    simpa only [d668, d82, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4742 (pattern : Ten) (guard : d669 pattern = 1) : d83 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d668 pattern = 1 := by simpa only [d669, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4741 pattern childGuard
    simpa only [d669, d83, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d669, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4598 pattern childGuard
    simpa only [d669, d83, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4743 (pattern : Ten) (guard : d670 pattern = 1) : d85 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d669 pattern = 1 := by simpa only [d670, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4742 pattern childGuard
    simpa only [d670, d85, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d670, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4600 pattern childGuard
    simpa only [d670, d85, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4744 (pattern : Ten) (guard : d664 pattern = 1) : d86 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d447 pattern = 1 := by simpa only [d664, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4729 pattern childGuard
    simpa only [d664, d86, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d664, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c603 pattern childGuard
    simpa only [d664, d86, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4745 (pattern : Ten) (guard : d665 pattern = 1) : d87 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d664 pattern = 1 := by simpa only [d665, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4744 pattern childGuard
    simpa only [d665, d87, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d665, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4603 pattern childGuard
    simpa only [d665, d87, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4746 (pattern : Ten) (guard : d666 pattern = 1) : d93 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d665 pattern = 1 := by simpa only [d666, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4745 pattern childGuard
    simpa only [d666, d93, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d666, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4605 pattern childGuard
    simpa only [d666, d93, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4747 (pattern : Ten) (guard : d667 pattern = 1) : d99 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d666 pattern = 1 := by simpa only [d667, d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4746 pattern childGuard
    simpa only [d667, d99, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d667, d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4607 pattern childGuard
    simpa only [d667, d99, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4748 (pattern : Ten) (guard : d668 pattern = 1) : d103 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d667 pattern = 1 := by simpa only [d668, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4747 pattern childGuard
    simpa only [d668, d103, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d668, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4609 pattern childGuard
    simpa only [d668, d103, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4749 (pattern : Ten) (guard : d669 pattern = 1) : d105 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d668 pattern = 1 := by simpa only [d669, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4748 pattern childGuard
    simpa only [d669, d105, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d669, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4611 pattern childGuard
    simpa only [d669, d105, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4750 (pattern : Ten) (guard : d670 pattern = 1) : d107 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d669 pattern = 1 := by simpa only [d670, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4749 pattern childGuard
    simpa only [d670, d107, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d670, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4613 pattern childGuard
    simpa only [d670, d107, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4751 (pattern : Ten) (guard : d665 pattern = 1) : d108 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d664 pattern = 1 := by simpa only [d665, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4730 pattern childGuard
    simpa only [d665, d108, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d665, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c686 pattern childGuard
    simpa only [d665, d108, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4752 (pattern : Ten) (guard : d666 pattern = 1) : d109 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d665 pattern = 1 := by simpa only [d666, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4751 pattern childGuard
    simpa only [d666, d109, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d666, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4616 pattern childGuard
    simpa only [d666, d109, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4753 (pattern : Ten) (guard : d667 pattern = 1) : d115 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d666 pattern = 1 := by simpa only [d667, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4752 pattern childGuard
    simpa only [d667, d115, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d667, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4618 pattern childGuard
    simpa only [d667, d115, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4754 (pattern : Ten) (guard : d668 pattern = 1) : d119 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d667 pattern = 1 := by simpa only [d668, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4753 pattern childGuard
    simpa only [d668, d119, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d668, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4620 pattern childGuard
    simpa only [d668, d119, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4755 (pattern : Ten) (guard : d669 pattern = 1) : d121 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d668 pattern = 1 := by simpa only [d669, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4754 pattern childGuard
    simpa only [d669, d121, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d669, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4622 pattern childGuard
    simpa only [d669, d121, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4756 (pattern : Ten) (guard : d670 pattern = 1) : d123 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d669 pattern = 1 := by simpa only [d670, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4755 pattern childGuard
    simpa only [d670, d123, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d670, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4624 pattern childGuard
    simpa only [d670, d123, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4757 (pattern : Ten) (guard : d666 pattern = 1) : d124 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d665 pattern = 1 := by simpa only [d666, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4731 pattern childGuard
    simpa only [d666, d124, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d666, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4626 pattern childGuard
    simpa only [d666, d124, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4758 (pattern : Ten) (guard : d667 pattern = 1) : d125 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d666 pattern = 1 := by simpa only [d667, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4757 pattern childGuard
    simpa only [d667, d125, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d667, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4628 pattern childGuard
    simpa only [d667, d125, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4759 (pattern : Ten) (guard : d668 pattern = 1) : d128 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d667 pattern = 1 := by simpa only [d668, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4758 pattern childGuard
    simpa only [d668, d128, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d668, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4628 pattern childGuard
    simpa only [d668, d128, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4760 (pattern : Ten) (guard : d669 pattern = 1) : d130 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d668 pattern = 1 := by simpa only [d669, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4759 pattern childGuard
    simpa only [d669, d130, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d669, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4631 pattern childGuard
    simpa only [d669, d130, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4761 (pattern : Ten) (guard : d670 pattern = 1) : d132 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d669 pattern = 1 := by simpa only [d670, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4760 pattern childGuard
    simpa only [d670, d132, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d670, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4633 pattern childGuard
    simpa only [d670, d132, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4762 (pattern : Ten) (guard : d670 pattern = 1) : d133 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d669 pattern = 1 := by simpa only [d670, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4735 pattern childGuard
    simpa only [d670, d133, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d670, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4596 pattern childGuard
    simpa only [d670, d133, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4763 (pattern : Ten) (guard : d669 pattern = 1) : d134 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d668 pattern = 1 := by simpa only [d669, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4734 pattern childGuard
    simpa only [d669, d134, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d669, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4636 pattern childGuard
    simpa only [d669, d134, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4764 (pattern : Ten) (guard : d670 pattern = 1) : d135 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d669 pattern = 1 := by simpa only [d670, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4763 pattern childGuard
    simpa only [d670, d135, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d670, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4638 pattern childGuard
    simpa only [d670, d135, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4765 (pattern : Ten) (guard : d664 pattern = 1) : d138 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d447 pattern = 1 := by simpa only [d664, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4729 pattern childGuard
    simpa only [d664, d138, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d664, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1108 pattern childGuard
    simpa only [d664, d138, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4766 (pattern : Ten) (guard : d665 pattern = 1) : d139 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d664 pattern = 1 := by simpa only [d665, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4765 pattern childGuard
    simpa only [d665, d139, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d665, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2784 pattern childGuard
    simpa only [d665, d139, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4767 (pattern : Ten) (guard : d666 pattern = 1) : d142 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d665 pattern = 1 := by simpa only [d666, d142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4766 pattern childGuard
    simpa only [d666, d142, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d666, d142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4566 pattern childGuard
    simpa only [d666, d142, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4768 (pattern : Ten) (guard : d667 pattern = 1) : d145 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d666 pattern = 1 := by simpa only [d667, d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4767 pattern childGuard
    simpa only [d667, d145, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d667, d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4643 pattern childGuard
    simpa only [d667, d145, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4769 (pattern : Ten) (guard : d668 pattern = 1) : d147 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d667 pattern = 1 := by simpa only [d668, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4768 pattern childGuard
    simpa only [d668, d147, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d668, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4645 pattern childGuard
    simpa only [d668, d147, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4770 (pattern : Ten) (guard : d669 pattern = 1) : d148 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d668 pattern = 1 := by simpa only [d669, d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4769 pattern childGuard
    simpa only [d669, d148, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d669, d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4572 pattern childGuard
    simpa only [d669, d148, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4771 (pattern : Ten) (guard : d670 pattern = 1) : d149 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d669 pattern = 1 := by simpa only [d670, d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4770 pattern childGuard
    simpa only [d670, d149, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d670, d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4574 pattern childGuard
    simpa only [d670, d149, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4772 (pattern : Ten) (guard : d667 pattern = 1) : d150 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d666 pattern = 1 := by simpa only [d667, d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4732 pattern childGuard
    simpa only [d667, d150, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d667, d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4649 pattern childGuard
    simpa only [d667, d150, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4773 (pattern : Ten) (guard : d668 pattern = 1) : d151 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d667 pattern = 1 := by simpa only [d668, d151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4772 pattern childGuard
    simpa only [d668, d151, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d668, d151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4581 pattern childGuard
    simpa only [d668, d151, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4774 (pattern : Ten) (guard : d669 pattern = 1) : d154 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d668 pattern = 1 := by simpa only [d669, d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4773 pattern childGuard
    simpa only [d669, d154, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d669, d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4652 pattern childGuard
    simpa only [d669, d154, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4775 (pattern : Ten) (guard : d670 pattern = 1) : d156 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d669 pattern = 1 := by simpa only [d670, d156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4774 pattern childGuard
    simpa only [d670, d156, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d670, d156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4654 pattern childGuard
    simpa only [d670, d156, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4776 (pattern : Ten) (guard : d667 pattern = 1) : d160 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d666 pattern = 1 := by simpa only [d667, d160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4732 pattern childGuard
    simpa only [d667, d160, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d667, d160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4656 pattern childGuard
    simpa only [d667, d160, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4777 (pattern : Ten) (guard : d668 pattern = 1) : d165 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d667 pattern = 1 := by simpa only [d668, d165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4776 pattern childGuard
    simpa only [d668, d165, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d668, d165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4658 pattern childGuard
    simpa only [d668, d165, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4778 (pattern : Ten) (guard : d669 pattern = 1) : d168 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d668 pattern = 1 := by simpa only [d669, d168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4777 pattern childGuard
    simpa only [d669, d168, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d669, d168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4660 pattern childGuard
    simpa only [d669, d168, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4779 (pattern : Ten) (guard : d670 pattern = 1) : d170 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d669 pattern = 1 := by simpa only [d670, d170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4778 pattern childGuard
    simpa only [d670, d170, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d670, d170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4662 pattern childGuard
    simpa only [d670, d170, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4780 (pattern : Ten) (guard : d0 pattern = 1) : d29 pattern ≤ (0 : Int) + d7 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4781 (pattern : Ten) (guard : d359 pattern = 1) : d0 pattern ≤ (0 : Int) + d7 pattern := by
  change (0 : Int) ≤ (0 : Int) + 7
  decide
theorem c4782 (pattern : Ten) (guard : d0 pattern = 1) : d2 pattern ≤ (0 : Int) + d7 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4783 (pattern : Ten) (guard : d606 pattern = 1) : d15 pattern ≤ (0 : Int) + d7 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d359 pattern = 1 := by simpa only [d606, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4781 pattern childGuard
    simpa only [d606, d15, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d606, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4782 pattern childGuard
    simpa only [d606, d15, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4784 (pattern : Ten) (guard : d0 pattern = 1) : d16 pattern ≤ (0 : Int) + d7 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4785 (pattern : Ten) (guard : d607 pattern = 1) : d21 pattern ≤ (0 : Int) + d7 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d606 pattern = 1 := by simpa only [d607, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4783 pattern childGuard
    simpa only [d607, d21, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d607, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4784 pattern childGuard
    simpa only [d607, d21, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4786 (pattern : Ten) (guard : d0 pattern = 1) : d22 pattern ≤ (0 : Int) + d7 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4787 (pattern : Ten) (guard : d608 pattern = 1) : d25 pattern ≤ (0 : Int) + d7 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d607 pattern = 1 := by simpa only [d608, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4785 pattern childGuard
    simpa only [d608, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d608, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4786 pattern childGuard
    simpa only [d608, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4788 (pattern : Ten) (guard : d0 pattern = 1) : d24 pattern ≤ (0 : Int) + d7 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4789 (pattern : Ten) (guard : d609 pattern = 1) : d30 pattern ≤ (0 : Int) + d7 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d608 pattern = 1 := by simpa only [d609, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4787 pattern childGuard
    simpa only [d609, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d609, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4788 pattern childGuard
    simpa only [d609, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4790 (pattern : Ten) (guard : d687 pattern = 1) : d33 pattern ≤ (0 : Int) + d7 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d687, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4780 pattern childGuard
    simpa only [d687, d33, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d609 pattern = 1 := by simpa only [d687, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4789 pattern childGuard
    simpa only [d687, d33, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4791 (pattern : Ten) (guard : d0 pattern = 1) : d34 pattern ≤ (0 : Int) + d7 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4792 (pattern : Ten) (guard : d688 pattern = 1) : d35 pattern ≤ (0 : Int) + d7 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d687 pattern = 1 := by simpa only [d688, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4790 pattern childGuard
    simpa only [d688, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d688, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4791 pattern childGuard
    simpa only [d688, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4793 (pattern : Ten) (guard : d0 pattern = 1) : d36 pattern ≤ (0 : Int) + d7 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4794 (pattern : Ten) (guard : d689 pattern = 1) : d37 pattern ≤ (0 : Int) + d7 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d688 pattern = 1 := by simpa only [d689, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4792 pattern childGuard
    simpa only [d689, d37, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d689, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4793 pattern childGuard
    simpa only [d689, d37, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4795 (pattern : Ten) (guard : d0 pattern = 1) : d42 pattern ≤ (0 : Int) + d7 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4796 (pattern : Ten) (guard : d607 pattern = 1) : d48 pattern ≤ (0 : Int) + d7 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d606 pattern = 1 := by simpa only [d607, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4783 pattern childGuard
    simpa only [d607, d48, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d607, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4795 pattern childGuard
    simpa only [d607, d48, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4797 (pattern : Ten) (guard : d0 pattern = 1) : d49 pattern ≤ (0 : Int) + d7 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4798 (pattern : Ten) (guard : d608 pattern = 1) : d54 pattern ≤ (0 : Int) + d7 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d607 pattern = 1 := by simpa only [d608, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4796 pattern childGuard
    simpa only [d608, d54, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d608, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4797 pattern childGuard
    simpa only [d608, d54, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4799 (pattern : Ten) (guard : d609 pattern = 1) : d54 pattern ≤ (0 : Int) + d7 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d608 pattern = 1 := by simpa only [d609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4798 pattern childGuard
    simpa only [d609, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c62 pattern childGuard
    simpa only [d609, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban41.Diagram
