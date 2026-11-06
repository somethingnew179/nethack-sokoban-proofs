/- Staged soko4-1 certificate. No result until all kernel checks pass. -/
import NetHack.Sokoban41.Comparisons29
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban41.Diagram
theorem c4800 (pattern : Ten) (guard : d687 pattern = 1) : d54 pattern ≤ (0 : Int) + d7 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c62 pattern childGuard
    simpa only [d687, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d609 pattern = 1 := by simpa only [d687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4799 pattern childGuard
    simpa only [d687, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4801 (pattern : Ten) (guard : d0 pattern = 1) : d62 pattern ≤ (0 : Int) + d7 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4802 (pattern : Ten) (guard : d688 pattern = 1) : d64 pattern ≤ (0 : Int) + d7 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d687 pattern = 1 := by simpa only [d688, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4800 pattern childGuard
    simpa only [d688, d64, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d688, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4801 pattern childGuard
    simpa only [d688, d64, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4803 (pattern : Ten) (guard : d689 pattern = 1) : d66 pattern ≤ (0 : Int) + d7 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d688 pattern = 1 := by simpa only [d689, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4802 pattern childGuard
    simpa only [d689, d66, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d689, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c209 pattern childGuard
    simpa only [d689, d66, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4804 (pattern : Ten) (guard : d0 pattern = 1) : d73 pattern ≤ (0 : Int) + d7 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4805 (pattern : Ten) (guard : d0 pattern = 1) : d71 pattern ≤ (0 : Int) + d7 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4806 (pattern : Ten) (guard : d609 pattern = 1) : d74 pattern ≤ (0 : Int) + d7 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d608 pattern = 1 := by simpa only [d609, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4787 pattern childGuard
    simpa only [d609, d74, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d609, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4805 pattern childGuard
    simpa only [d609, d74, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4807 (pattern : Ten) (guard : d687 pattern = 1) : d77 pattern ≤ (0 : Int) + d7 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d687, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4804 pattern childGuard
    simpa only [d687, d77, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d609 pattern = 1 := by simpa only [d687, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4806 pattern childGuard
    simpa only [d687, d77, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4808 (pattern : Ten) (guard : d0 pattern = 1) : d78 pattern ≤ (0 : Int) + d7 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4809 (pattern : Ten) (guard : d688 pattern = 1) : d79 pattern ≤ (0 : Int) + d7 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d687 pattern = 1 := by simpa only [d688, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4807 pattern childGuard
    simpa only [d688, d79, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d688, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4808 pattern childGuard
    simpa only [d688, d79, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4810 (pattern : Ten) (guard : d0 pattern = 1) : d80 pattern ≤ (0 : Int) + d7 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4811 (pattern : Ten) (guard : d689 pattern = 1) : d81 pattern ≤ (0 : Int) + d7 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d688 pattern = 1 := by simpa only [d689, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4809 pattern childGuard
    simpa only [d689, d81, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d689, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4810 pattern childGuard
    simpa only [d689, d81, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4812 (pattern : Ten) (guard : d609 pattern = 1) : d7 pattern ≤ (0 : Int) + d7 pattern := by
  omega
theorem c4813 (pattern : Ten) (guard : d687 pattern = 1) : d82 pattern ≤ (0 : Int) + d7 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d687, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c62 pattern childGuard
    simpa only [d687, d82, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d609 pattern = 1 := by simpa only [d687, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4812 pattern childGuard
    simpa only [d687, d82, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4814 (pattern : Ten) (guard : d0 pattern = 1) : d58 pattern ≤ (0 : Int) + d7 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4815 (pattern : Ten) (guard : d688 pattern = 1) : d83 pattern ≤ (0 : Int) + d7 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d687 pattern = 1 := by simpa only [d688, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4813 pattern childGuard
    simpa only [d688, d83, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d688, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4814 pattern childGuard
    simpa only [d688, d83, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4816 (pattern : Ten) (guard : d689 pattern = 1) : d85 pattern ≤ (0 : Int) + d7 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d688 pattern = 1 := by simpa only [d689, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4815 pattern childGuard
    simpa only [d689, d85, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d689, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c311 pattern childGuard
    simpa only [d689, d85, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4817 (pattern : Ten) (guard : d0 pattern = 1) : d99 pattern ≤ (0 : Int) + d7 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4818 (pattern : Ten) (guard : d606 pattern = 1) : d0 pattern ≤ (0 : Int) + d7 pattern := by
  change (0 : Int) ≤ (0 : Int) + 7
  decide
theorem c4819 (pattern : Ten) (guard : d607 pattern = 1) : d91 pattern ≤ (0 : Int) + d7 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d606 pattern = 1 := by simpa only [d607, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4818 pattern childGuard
    simpa only [d607, d91, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d607, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4782 pattern childGuard
    simpa only [d607, d91, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4820 (pattern : Ten) (guard : d0 pattern = 1) : d92 pattern ≤ (0 : Int) + d7 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4821 (pattern : Ten) (guard : d608 pattern = 1) : d95 pattern ≤ (0 : Int) + d7 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d607 pattern = 1 := by simpa only [d608, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4819 pattern childGuard
    simpa only [d608, d95, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d608, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4820 pattern childGuard
    simpa only [d608, d95, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4822 (pattern : Ten) (guard : d0 pattern = 1) : d94 pattern ≤ (0 : Int) + d7 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4823 (pattern : Ten) (guard : d609 pattern = 1) : d100 pattern ≤ (0 : Int) + d7 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d608 pattern = 1 := by simpa only [d609, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4821 pattern childGuard
    simpa only [d609, d100, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d609, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4822 pattern childGuard
    simpa only [d609, d100, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4824 (pattern : Ten) (guard : d687 pattern = 1) : d103 pattern ≤ (0 : Int) + d7 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d687, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4817 pattern childGuard
    simpa only [d687, d103, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d609 pattern = 1 := by simpa only [d687, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4823 pattern childGuard
    simpa only [d687, d103, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4825 (pattern : Ten) (guard : d0 pattern = 1) : d104 pattern ≤ (0 : Int) + d7 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4826 (pattern : Ten) (guard : d688 pattern = 1) : d105 pattern ≤ (0 : Int) + d7 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d687 pattern = 1 := by simpa only [d688, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4824 pattern childGuard
    simpa only [d688, d105, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d688, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4825 pattern childGuard
    simpa only [d688, d105, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4827 (pattern : Ten) (guard : d0 pattern = 1) : d106 pattern ≤ (0 : Int) + d7 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4828 (pattern : Ten) (guard : d689 pattern = 1) : d107 pattern ≤ (0 : Int) + d7 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d688 pattern = 1 := by simpa only [d689, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4826 pattern childGuard
    simpa only [d689, d107, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d689, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4827 pattern childGuard
    simpa only [d689, d107, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4829 (pattern : Ten) (guard : d0 pattern = 1) : d115 pattern ≤ (0 : Int) + d7 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4830 (pattern : Ten) (guard : d0 pattern = 1) : d15 pattern ≤ (0 : Int) + d7 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4831 (pattern : Ten) (guard : d607 pattern = 1) : d15 pattern ≤ (0 : Int) + d7 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d606 pattern = 1 := by simpa only [d607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4783 pattern childGuard
    simpa only [d607, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4830 pattern childGuard
    simpa only [d607, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4832 (pattern : Ten) (guard : d0 pattern = 1) : d44 pattern ≤ (0 : Int) + d7 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4833 (pattern : Ten) (guard : d608 pattern = 1) : d111 pattern ≤ (0 : Int) + d7 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d607 pattern = 1 := by simpa only [d608, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4831 pattern childGuard
    simpa only [d608, d111, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d608, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4832 pattern childGuard
    simpa only [d608, d111, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4834 (pattern : Ten) (guard : d0 pattern = 1) : d110 pattern ≤ (0 : Int) + d7 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4835 (pattern : Ten) (guard : d609 pattern = 1) : d116 pattern ≤ (0 : Int) + d7 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d608 pattern = 1 := by simpa only [d609, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4833 pattern childGuard
    simpa only [d609, d116, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d609, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4834 pattern childGuard
    simpa only [d609, d116, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4836 (pattern : Ten) (guard : d687 pattern = 1) : d119 pattern ≤ (0 : Int) + d7 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d687, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4829 pattern childGuard
    simpa only [d687, d119, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d609 pattern = 1 := by simpa only [d687, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4835 pattern childGuard
    simpa only [d687, d119, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4837 (pattern : Ten) (guard : d0 pattern = 1) : d120 pattern ≤ (0 : Int) + d7 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4838 (pattern : Ten) (guard : d688 pattern = 1) : d121 pattern ≤ (0 : Int) + d7 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d687 pattern = 1 := by simpa only [d688, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4836 pattern childGuard
    simpa only [d688, d121, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d688, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4837 pattern childGuard
    simpa only [d688, d121, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4839 (pattern : Ten) (guard : d0 pattern = 1) : d122 pattern ≤ (0 : Int) + d7 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4840 (pattern : Ten) (guard : d689 pattern = 1) : d123 pattern ≤ (0 : Int) + d7 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d688 pattern = 1 := by simpa only [d689, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4838 pattern childGuard
    simpa only [d689, d123, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d689, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4839 pattern childGuard
    simpa only [d689, d123, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4841 (pattern : Ten) (guard : d0 pattern = 1) : d125 pattern ≤ (0 : Int) + d7 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4842 (pattern : Ten) (guard : d0 pattern = 1) : d48 pattern ≤ (0 : Int) + d7 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4843 (pattern : Ten) (guard : d608 pattern = 1) : d48 pattern ≤ (0 : Int) + d7 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d607 pattern = 1 := by simpa only [d608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4796 pattern childGuard
    simpa only [d608, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4842 pattern childGuard
    simpa only [d608, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4844 (pattern : Ten) (guard : d609 pattern = 1) : d48 pattern ≤ (0 : Int) + d7 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d608 pattern = 1 := by simpa only [d609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4843 pattern childGuard
    simpa only [d609, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4842 pattern childGuard
    simpa only [d609, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4845 (pattern : Ten) (guard : d687 pattern = 1) : d128 pattern ≤ (0 : Int) + d7 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d687, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4841 pattern childGuard
    simpa only [d687, d128, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d609 pattern = 1 := by simpa only [d687, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4844 pattern childGuard
    simpa only [d687, d128, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4846 (pattern : Ten) (guard : d0 pattern = 1) : d129 pattern ≤ (0 : Int) + d7 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4847 (pattern : Ten) (guard : d688 pattern = 1) : d130 pattern ≤ (0 : Int) + d7 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d687 pattern = 1 := by simpa only [d688, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4845 pattern childGuard
    simpa only [d688, d130, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d688, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4846 pattern childGuard
    simpa only [d688, d130, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4848 (pattern : Ten) (guard : d689 pattern = 1) : d132 pattern ≤ (0 : Int) + d7 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d688 pattern = 1 := by simpa only [d689, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4847 pattern childGuard
    simpa only [d689, d132, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d689, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c797 pattern childGuard
    simpa only [d689, d132, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4849 (pattern : Ten) (guard : d0 pattern = 1) : d7 pattern ≤ (0 : Int) + d7 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4850 (pattern : Ten) (guard : d689 pattern = 1) : d133 pattern ≤ (0 : Int) + d7 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d688 pattern = 1 := by simpa only [d689, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4802 pattern childGuard
    simpa only [d689, d133, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d689, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4849 pattern childGuard
    simpa only [d689, d133, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4851 (pattern : Ten) (guard : d0 pattern = 1) : d8 pattern ≤ (0 : Int) + d7 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4852 (pattern : Ten) (guard : d688 pattern = 1) : d134 pattern ≤ (0 : Int) + d7 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d687 pattern = 1 := by simpa only [d688, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4800 pattern childGuard
    simpa only [d688, d134, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d688, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4851 pattern childGuard
    simpa only [d688, d134, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4853 (pattern : Ten) (guard : d689 pattern = 1) : d135 pattern ≤ (0 : Int) + d7 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d688 pattern = 1 := by simpa only [d689, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4852 pattern childGuard
    simpa only [d689, d135, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d689, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c929 pattern childGuard
    simpa only [d689, d135, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4854 (pattern : Ten) (guard : d0 pattern = 1) : d145 pattern ≤ (0 : Int) + d7 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4855 (pattern : Ten) (guard : d0 pattern = 1) : d10 pattern ≤ (0 : Int) + d7 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4856 (pattern : Ten) (guard : d606 pattern = 1) : d12 pattern ≤ (0 : Int) + d7 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d359 pattern = 1 := by simpa only [d606, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4781 pattern childGuard
    simpa only [d606, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d606, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4855 pattern childGuard
    simpa only [d606, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4857 (pattern : Ten) (guard : d607 pattern = 1) : d141 pattern ≤ (0 : Int) + d7 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d606 pattern = 1 := by simpa only [d607, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4856 pattern childGuard
    simpa only [d607, d141, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d607, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4784 pattern childGuard
    simpa only [d607, d141, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4858 (pattern : Ten) (guard : d608 pattern = 1) : d144 pattern ≤ (0 : Int) + d7 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d607 pattern = 1 := by simpa only [d608, d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4857 pattern childGuard
    simpa only [d608, d144, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d608, d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4786 pattern childGuard
    simpa only [d608, d144, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4859 (pattern : Ten) (guard : d0 pattern = 1) : d143 pattern ≤ (0 : Int) + d7 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4860 (pattern : Ten) (guard : d609 pattern = 1) : d146 pattern ≤ (0 : Int) + d7 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d608 pattern = 1 := by simpa only [d609, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4858 pattern childGuard
    simpa only [d609, d146, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d609, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4859 pattern childGuard
    simpa only [d609, d146, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4861 (pattern : Ten) (guard : d687 pattern = 1) : d147 pattern ≤ (0 : Int) + d7 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d687, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4854 pattern childGuard
    simpa only [d687, d147, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d609 pattern = 1 := by simpa only [d687, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4860 pattern childGuard
    simpa only [d687, d147, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4862 (pattern : Ten) (guard : d688 pattern = 1) : d148 pattern ≤ (0 : Int) + d7 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d687 pattern = 1 := by simpa only [d688, d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4861 pattern childGuard
    simpa only [d688, d148, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d688, d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4791 pattern childGuard
    simpa only [d688, d148, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4863 (pattern : Ten) (guard : d689 pattern = 1) : d149 pattern ≤ (0 : Int) + d7 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d688 pattern = 1 := by simpa only [d689, d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4862 pattern childGuard
    simpa only [d689, d149, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d689, d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4793 pattern childGuard
    simpa only [d689, d149, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4864 (pattern : Ten) (guard : d0 pattern = 1) : d150 pattern ≤ (0 : Int) + d7 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4865 (pattern : Ten) (guard : d687 pattern = 1) : d151 pattern ≤ (0 : Int) + d7 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d687, d151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4864 pattern childGuard
    simpa only [d687, d151, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d609 pattern = 1 := by simpa only [d687, d151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4799 pattern childGuard
    simpa only [d687, d151, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4866 (pattern : Ten) (guard : d0 pattern = 1) : d152 pattern ≤ (0 : Int) + d7 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4867 (pattern : Ten) (guard : d688 pattern = 1) : d154 pattern ≤ (0 : Int) + d7 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d687 pattern = 1 := by simpa only [d688, d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4865 pattern childGuard
    simpa only [d688, d154, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d688, d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4866 pattern childGuard
    simpa only [d688, d154, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4868 (pattern : Ten) (guard : d689 pattern = 1) : d156 pattern ≤ (0 : Int) + d7 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d688 pattern = 1 := by simpa only [d689, d156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4867 pattern childGuard
    simpa only [d689, d156, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d689, d156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1233 pattern childGuard
    simpa only [d689, d156, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4869 (pattern : Ten) (guard : d0 pattern = 1) : d160 pattern ≤ (0 : Int) + d7 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4870 (pattern : Ten) (guard : d0 pattern = 1) : d159 pattern ≤ (0 : Int) + d7 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4871 (pattern : Ten) (guard : d609 pattern = 1) : d161 pattern ≤ (0 : Int) + d7 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d608 pattern = 1 := by simpa only [d609, d161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4798 pattern childGuard
    simpa only [d609, d161, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d609, d161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4870 pattern childGuard
    simpa only [d609, d161, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4872 (pattern : Ten) (guard : d687 pattern = 1) : d165 pattern ≤ (0 : Int) + d7 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d687, d165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4869 pattern childGuard
    simpa only [d687, d165, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d609 pattern = 1 := by simpa only [d687, d165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4871 pattern childGuard
    simpa only [d687, d165, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4873 (pattern : Ten) (guard : d0 pattern = 1) : d166 pattern ≤ (0 : Int) + d7 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4874 (pattern : Ten) (guard : d688 pattern = 1) : d168 pattern ≤ (0 : Int) + d7 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d687 pattern = 1 := by simpa only [d688, d168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4872 pattern childGuard
    simpa only [d688, d168, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d688, d168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4873 pattern childGuard
    simpa only [d688, d168, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4875 (pattern : Ten) (guard : d0 pattern = 1) : d169 pattern ≤ (0 : Int) + d7 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4876 (pattern : Ten) (guard : d689 pattern = 1) : d170 pattern ≤ (0 : Int) + d7 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d688 pattern = 1 := by simpa only [d689, d170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4874 pattern childGuard
    simpa only [d689, d170, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d689, d170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4875 pattern childGuard
    simpa only [d689, d170, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4877 (pattern : Ten) (guard : d0 pattern = 1) : d35 pattern ≤ (0 : Int) + d7 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4878 (pattern : Ten) (guard : d607 pattern = 1) : d18 pattern ≤ (0 : Int) + d7 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d606 pattern = 1 := by simpa only [d607, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4856 pattern childGuard
    simpa only [d607, d18, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d607, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4855 pattern childGuard
    simpa only [d607, d18, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4879 (pattern : Ten) (guard : d608 pattern = 1) : d26 pattern ≤ (0 : Int) + d7 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d607 pattern = 1 := by simpa only [d608, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4878 pattern childGuard
    simpa only [d608, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d608, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4855 pattern childGuard
    simpa only [d608, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4880 (pattern : Ten) (guard : d0 pattern = 1) : d27 pattern ≤ (0 : Int) + d7 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4881 (pattern : Ten) (guard : d609 pattern = 1) : d31 pattern ≤ (0 : Int) + d7 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d608 pattern = 1 := by simpa only [d609, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4879 pattern childGuard
    simpa only [d609, d31, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d609, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4880 pattern childGuard
    simpa only [d609, d31, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4882 (pattern : Ten) (guard : d0 pattern = 1) : d32 pattern ≤ (0 : Int) + d7 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4883 (pattern : Ten) (guard : d610 pattern = 1) : d34 pattern ≤ (0 : Int) + d7 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d609 pattern = 1 := by simpa only [d610, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4881 pattern childGuard
    simpa only [d610, d34, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d610, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4882 pattern childGuard
    simpa only [d610, d34, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4884 (pattern : Ten) (guard : d611 pattern = 1) : d36 pattern ≤ (0 : Int) + d7 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d610 pattern = 1 := by simpa only [d611, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4883 pattern childGuard
    simpa only [d611, d36, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d611, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4855 pattern childGuard
    simpa only [d611, d36, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4885 (pattern : Ten) (guard : d696 pattern = 1) : d37 pattern ≤ (0 : Int) + d7 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d696, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4877 pattern childGuard
    simpa only [d696, d37, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d611 pattern = 1 := by simpa only [d696, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4884 pattern childGuard
    simpa only [d696, d37, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4886 (pattern : Ten) (guard : d0 pattern = 1) : d64 pattern ≤ (0 : Int) + d7 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4887 (pattern : Ten) (guard : d1 pattern = 1) : d7 pattern ≤ (0 : Int) + d7 pattern := by
  omega
theorem c4888 (pattern : Ten) (guard : d356 pattern = 1) : d38 pattern ≤ (0 : Int) + d7 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d356, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4887 pattern childGuard
    simpa only [d356, d38, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d356, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4851 pattern childGuard
    simpa only [d356, d38, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4889 (pattern : Ten) (guard : d358 pattern = 1) : d40 pattern ≤ (0 : Int) + d7 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d356 pattern = 1 := by simpa only [d358, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4888 pattern childGuard
    simpa only [d358, d40, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d358, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4851 pattern childGuard
    simpa only [d358, d40, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4890 (pattern : Ten) (guard : d0 pattern = 1) : d40 pattern ≤ (0 : Int) + d7 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4891 (pattern : Ten) (guard : d359 pattern = 1) : d40 pattern ≤ (0 : Int) + d7 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d358 pattern = 1 := by simpa only [d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4889 pattern childGuard
    simpa only [d359, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4890 pattern childGuard
    simpa only [d359, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4892 (pattern : Ten) (guard : d606 pattern = 1) : d46 pattern ≤ (0 : Int) + d7 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d359 pattern = 1 := by simpa only [d606, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4891 pattern childGuard
    simpa only [d606, d46, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d606, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4855 pattern childGuard
    simpa only [d606, d46, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4893 (pattern : Ten) (guard : d607 pattern = 1) : d52 pattern ≤ (0 : Int) + d7 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d606 pattern = 1 := by simpa only [d607, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4892 pattern childGuard
    simpa only [d607, d52, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d607, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4855 pattern childGuard
    simpa only [d607, d52, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4894 (pattern : Ten) (guard : d608 pattern = 1) : d56 pattern ≤ (0 : Int) + d7 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d607 pattern = 1 := by simpa only [d608, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4893 pattern childGuard
    simpa only [d608, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d608, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4855 pattern childGuard
    simpa only [d608, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4895 (pattern : Ten) (guard : d609 pattern = 1) : d56 pattern ≤ (0 : Int) + d7 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d608 pattern = 1 := by simpa only [d609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4894 pattern childGuard
    simpa only [d609, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c929 pattern childGuard
    simpa only [d609, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4896 (pattern : Ten) (guard : d610 pattern = 1) : d56 pattern ≤ (0 : Int) + d7 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d609 pattern = 1 := by simpa only [d610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4895 pattern childGuard
    simpa only [d610, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c929 pattern childGuard
    simpa only [d610, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4897 (pattern : Ten) (guard : d0 pattern = 1) : d63 pattern ≤ (0 : Int) + d7 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4898 (pattern : Ten) (guard : d611 pattern = 1) : d65 pattern ≤ (0 : Int) + d7 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d610 pattern = 1 := by simpa only [d611, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4896 pattern childGuard
    simpa only [d611, d65, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d611, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4897 pattern childGuard
    simpa only [d611, d65, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4899 (pattern : Ten) (guard : d696 pattern = 1) : d66 pattern ≤ (0 : Int) + d7 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d696, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4886 pattern childGuard
    simpa only [d696, d66, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d611 pattern = 1 := by simpa only [d696, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4898 pattern childGuard
    simpa only [d696, d66, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4900 (pattern : Ten) (guard : d0 pattern = 1) : d79 pattern ≤ (0 : Int) + d7 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4901 (pattern : Ten) (guard : d0 pattern = 1) : d72 pattern ≤ (0 : Int) + d7 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4902 (pattern : Ten) (guard : d609 pattern = 1) : d75 pattern ≤ (0 : Int) + d7 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d608 pattern = 1 := by simpa only [d609, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4879 pattern childGuard
    simpa only [d609, d75, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d609, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4901 pattern childGuard
    simpa only [d609, d75, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4903 (pattern : Ten) (guard : d0 pattern = 1) : d76 pattern ≤ (0 : Int) + d7 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4904 (pattern : Ten) (guard : d610 pattern = 1) : d78 pattern ≤ (0 : Int) + d7 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d609 pattern = 1 := by simpa only [d610, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4902 pattern childGuard
    simpa only [d610, d78, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d610, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4903 pattern childGuard
    simpa only [d610, d78, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4905 (pattern : Ten) (guard : d611 pattern = 1) : d80 pattern ≤ (0 : Int) + d7 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d610 pattern = 1 := by simpa only [d611, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4904 pattern childGuard
    simpa only [d611, d80, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d611, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4855 pattern childGuard
    simpa only [d611, d80, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4906 (pattern : Ten) (guard : d696 pattern = 1) : d81 pattern ≤ (0 : Int) + d7 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d696, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4900 pattern childGuard
    simpa only [d696, d81, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d611 pattern = 1 := by simpa only [d696, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4905 pattern childGuard
    simpa only [d696, d81, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4907 (pattern : Ten) (guard : d0 pattern = 1) : d83 pattern ≤ (0 : Int) + d7 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4908 (pattern : Ten) (guard : d0 pattern = 1) : d60 pattern ≤ (0 : Int) + d7 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4909 (pattern : Ten) (guard : d611 pattern = 1) : d84 pattern ≤ (0 : Int) + d7 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d610 pattern = 1 := by simpa only [d611, d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4896 pattern childGuard
    simpa only [d611, d84, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d611, d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4908 pattern childGuard
    simpa only [d611, d84, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4910 (pattern : Ten) (guard : d696 pattern = 1) : d85 pattern ≤ (0 : Int) + d7 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d696, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4907 pattern childGuard
    simpa only [d696, d85, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d611 pattern = 1 := by simpa only [d696, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4909 pattern childGuard
    simpa only [d696, d85, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4911 (pattern : Ten) (guard : d0 pattern = 1) : d105 pattern ≤ (0 : Int) + d7 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4912 (pattern : Ten) (guard : d607 pattern = 1) : d88 pattern ≤ (0 : Int) + d7 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d606 pattern = 1 := by simpa only [d607, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4818 pattern childGuard
    simpa only [d607, d88, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d607, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4855 pattern childGuard
    simpa only [d607, d88, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4913 (pattern : Ten) (guard : d608 pattern = 1) : d96 pattern ≤ (0 : Int) + d7 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d607 pattern = 1 := by simpa only [d608, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4912 pattern childGuard
    simpa only [d608, d96, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d608, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4855 pattern childGuard
    simpa only [d608, d96, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4914 (pattern : Ten) (guard : d0 pattern = 1) : d97 pattern ≤ (0 : Int) + d7 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4915 (pattern : Ten) (guard : d609 pattern = 1) : d101 pattern ≤ (0 : Int) + d7 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d608 pattern = 1 := by simpa only [d609, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4913 pattern childGuard
    simpa only [d609, d101, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d609, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4914 pattern childGuard
    simpa only [d609, d101, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4916 (pattern : Ten) (guard : d0 pattern = 1) : d102 pattern ≤ (0 : Int) + d7 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4917 (pattern : Ten) (guard : d610 pattern = 1) : d104 pattern ≤ (0 : Int) + d7 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d609 pattern = 1 := by simpa only [d610, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4915 pattern childGuard
    simpa only [d610, d104, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d610, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4916 pattern childGuard
    simpa only [d610, d104, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4918 (pattern : Ten) (guard : d611 pattern = 1) : d106 pattern ≤ (0 : Int) + d7 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d610 pattern = 1 := by simpa only [d611, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4917 pattern childGuard
    simpa only [d611, d106, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d611, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4855 pattern childGuard
    simpa only [d611, d106, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4919 (pattern : Ten) (guard : d696 pattern = 1) : d107 pattern ≤ (0 : Int) + d7 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d696, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4911 pattern childGuard
    simpa only [d696, d107, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d611 pattern = 1 := by simpa only [d696, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4918 pattern childGuard
    simpa only [d696, d107, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4920 (pattern : Ten) (guard : d0 pattern = 1) : d121 pattern ≤ (0 : Int) + d7 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4921 (pattern : Ten) (guard : d608 pattern = 1) : d112 pattern ≤ (0 : Int) + d7 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d607 pattern = 1 := by simpa only [d608, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4831 pattern childGuard
    simpa only [d608, d112, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d608, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4855 pattern childGuard
    simpa only [d608, d112, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4922 (pattern : Ten) (guard : d0 pattern = 1) : d113 pattern ≤ (0 : Int) + d7 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4923 (pattern : Ten) (guard : d609 pattern = 1) : d117 pattern ≤ (0 : Int) + d7 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d608 pattern = 1 := by simpa only [d609, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4921 pattern childGuard
    simpa only [d609, d117, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d609, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4922 pattern childGuard
    simpa only [d609, d117, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4924 (pattern : Ten) (guard : d0 pattern = 1) : d118 pattern ≤ (0 : Int) + d7 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4925 (pattern : Ten) (guard : d610 pattern = 1) : d120 pattern ≤ (0 : Int) + d7 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d609 pattern = 1 := by simpa only [d610, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4923 pattern childGuard
    simpa only [d610, d120, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d610, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4924 pattern childGuard
    simpa only [d610, d120, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4926 (pattern : Ten) (guard : d611 pattern = 1) : d122 pattern ≤ (0 : Int) + d7 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d610 pattern = 1 := by simpa only [d611, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4925 pattern childGuard
    simpa only [d611, d122, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d611, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4855 pattern childGuard
    simpa only [d611, d122, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4927 (pattern : Ten) (guard : d696 pattern = 1) : d123 pattern ≤ (0 : Int) + d7 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d696, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4920 pattern childGuard
    simpa only [d696, d123, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d611 pattern = 1 := by simpa only [d696, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4926 pattern childGuard
    simpa only [d696, d123, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4928 (pattern : Ten) (guard : d0 pattern = 1) : d130 pattern ≤ (0 : Int) + d7 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4929 (pattern : Ten) (guard : d0 pattern = 1) : d20 pattern ≤ (0 : Int) + d7 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4930 (pattern : Ten) (guard : d609 pattern = 1) : d126 pattern ≤ (0 : Int) + d7 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d608 pattern = 1 := by simpa only [d609, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4843 pattern childGuard
    simpa only [d609, d126, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d609, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4929 pattern childGuard
    simpa only [d609, d126, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4931 (pattern : Ten) (guard : d0 pattern = 1) : d127 pattern ≤ (0 : Int) + d7 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4932 (pattern : Ten) (guard : d610 pattern = 1) : d129 pattern ≤ (0 : Int) + d7 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d609 pattern = 1 := by simpa only [d610, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4930 pattern childGuard
    simpa only [d610, d129, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d610, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4931 pattern childGuard
    simpa only [d610, d129, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4933 (pattern : Ten) (guard : d611 pattern = 1) : d131 pattern ≤ (0 : Int) + d7 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d610 pattern = 1 := by simpa only [d611, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4932 pattern childGuard
    simpa only [d611, d131, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d611, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4855 pattern childGuard
    simpa only [d611, d131, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4934 (pattern : Ten) (guard : d696 pattern = 1) : d132 pattern ≤ (0 : Int) + d7 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d696, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4928 pattern childGuard
    simpa only [d696, d132, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d611 pattern = 1 := by simpa only [d696, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4933 pattern childGuard
    simpa only [d696, d132, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4935 (pattern : Ten) (guard : d611 pattern = 1) : d7 pattern ≤ (0 : Int) + d7 pattern := by
  omega
theorem c4936 (pattern : Ten) (guard : d696 pattern = 1) : d133 pattern ≤ (0 : Int) + d7 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d696, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4886 pattern childGuard
    simpa only [d696, d133, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d611 pattern = 1 := by simpa only [d696, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4935 pattern childGuard
    simpa only [d696, d133, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4937 (pattern : Ten) (guard : d0 pattern = 1) : d134 pattern ≤ (0 : Int) + d7 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4938 (pattern : Ten) (guard : d611 pattern = 1) : d56 pattern ≤ (0 : Int) + d7 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d610 pattern = 1 := by simpa only [d611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4896 pattern childGuard
    simpa only [d611, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c929 pattern childGuard
    simpa only [d611, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4939 (pattern : Ten) (guard : d696 pattern = 1) : d135 pattern ≤ (0 : Int) + d7 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d696, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4937 pattern childGuard
    simpa only [d696, d135, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d611 pattern = 1 := by simpa only [d696, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4938 pattern childGuard
    simpa only [d696, d135, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4940 (pattern : Ten) (guard : d0 pattern = 1) : d148 pattern ≤ (0 : Int) + d7 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4941 (pattern : Ten) (guard : d696 pattern = 1) : d149 pattern ≤ (0 : Int) + d7 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d696, d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4940 pattern childGuard
    simpa only [d696, d149, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d611 pattern = 1 := by simpa only [d696, d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4884 pattern childGuard
    simpa only [d696, d149, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4942 (pattern : Ten) (guard : d0 pattern = 1) : d154 pattern ≤ (0 : Int) + d7 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4943 (pattern : Ten) (guard : d0 pattern = 1) : d153 pattern ≤ (0 : Int) + d7 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4944 (pattern : Ten) (guard : d611 pattern = 1) : d155 pattern ≤ (0 : Int) + d7 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d610 pattern = 1 := by simpa only [d611, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4896 pattern childGuard
    simpa only [d611, d155, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d611, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4943 pattern childGuard
    simpa only [d611, d155, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4945 (pattern : Ten) (guard : d696 pattern = 1) : d156 pattern ≤ (0 : Int) + d7 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d696, d156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4942 pattern childGuard
    simpa only [d696, d156, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d611 pattern = 1 := by simpa only [d696, d156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4944 pattern childGuard
    simpa only [d696, d156, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4946 (pattern : Ten) (guard : d0 pattern = 1) : d168 pattern ≤ (0 : Int) + d7 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4947 (pattern : Ten) (guard : d0 pattern = 1) : d57 pattern ≤ (0 : Int) + d7 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4948 (pattern : Ten) (guard : d609 pattern = 1) : d164 pattern ≤ (0 : Int) + d7 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d608 pattern = 1 := by simpa only [d609, d164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4894 pattern childGuard
    simpa only [d609, d164, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d609, d164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4947 pattern childGuard
    simpa only [d609, d164, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4949 (pattern : Ten) (guard : d610 pattern = 1) : d167 pattern ≤ (0 : Int) + d7 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d609 pattern = 1 := by simpa only [d610, d167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4948 pattern childGuard
    simpa only [d610, d167, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d610, d167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4908 pattern childGuard
    simpa only [d610, d167, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4950 (pattern : Ten) (guard : d611 pattern = 1) : d169 pattern ≤ (0 : Int) + d7 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d610 pattern = 1 := by simpa only [d611, d169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4949 pattern childGuard
    simpa only [d611, d169, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d611, d169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4897 pattern childGuard
    simpa only [d611, d169, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4951 (pattern : Ten) (guard : d696 pattern = 1) : d170 pattern ≤ (0 : Int) + d7 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d696, d170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4946 pattern childGuard
    simpa only [d696, d170, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d611 pattern = 1 := by simpa only [d696, d170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4950 pattern childGuard
    simpa only [d696, d170, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4952 (pattern : Ten) (guard : d0 pattern = 1) : d33 pattern ≤ (0 : Int) + d8 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4953 (pattern : Ten) (guard : d359 pattern = 1) : d0 pattern ≤ (0 : Int) + d8 pattern := by
  change (0 : Int) ≤ (0 : Int) + 8
  decide
theorem c4954 (pattern : Ten) (guard : d0 pattern = 1) : d10 pattern ≤ (0 : Int) + d8 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4955 (pattern : Ten) (guard : d606 pattern = 1) : d12 pattern ≤ (0 : Int) + d8 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d359 pattern = 1 := by simpa only [d606, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4953 pattern childGuard
    simpa only [d606, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d606, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4954 pattern childGuard
    simpa only [d606, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4956 (pattern : Ten) (guard : d607 pattern = 1) : d18 pattern ≤ (0 : Int) + d8 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d606 pattern = 1 := by simpa only [d607, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4955 pattern childGuard
    simpa only [d607, d18, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d607, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4954 pattern childGuard
    simpa only [d607, d18, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4957 (pattern : Ten) (guard : d608 pattern = 1) : d26 pattern ≤ (0 : Int) + d8 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d607 pattern = 1 := by simpa only [d608, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4956 pattern childGuard
    simpa only [d608, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d608, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4954 pattern childGuard
    simpa only [d608, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4958 (pattern : Ten) (guard : d0 pattern = 1) : d27 pattern ≤ (0 : Int) + d8 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4959 (pattern : Ten) (guard : d609 pattern = 1) : d31 pattern ≤ (0 : Int) + d8 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d608 pattern = 1 := by simpa only [d609, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4957 pattern childGuard
    simpa only [d609, d31, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d609, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4958 pattern childGuard
    simpa only [d609, d31, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban41.Diagram
