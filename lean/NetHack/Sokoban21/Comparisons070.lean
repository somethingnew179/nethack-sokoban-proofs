/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons069
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c9800 (pattern : Twelve) (guard : d0 pattern = 1) : d805 pattern ≤ (0 : Int) + d116 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9801 (pattern : Twelve) (guard : d1878 pattern = 1) : d806 pattern ≤ (0 : Int) + d116 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1878, d806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c0 pattern childGuard
    simpa only [d1878, d806, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1878, d806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9800 pattern childGuard
    simpa only [d1878, d806, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9802 (pattern : Twelve) (guard : d0 pattern = 1) : d1266 pattern ≤ (0 : Int) + d871 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9803 (pattern : Twelve) (guard : d1878 pattern = 1) : d1267 pattern ≤ (0 : Int) + d871 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1878, d1267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1 pattern childGuard
    simpa only [d1878, d1267, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1878, d1267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9802 pattern childGuard
    simpa only [d1878, d1267, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9804 (pattern : Twelve) (guard : d0 pattern = 1) : d1635 pattern ≤ (0 : Int) + d1323 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9805 (pattern : Twelve) (guard : d1878 pattern = 1) : d1636 pattern ≤ (0 : Int) + d1323 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1878, d1636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2 pattern childGuard
    simpa only [d1878, d1636, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1878, d1636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9804 pattern childGuard
    simpa only [d1878, d1636, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9806 (pattern : Twelve) (guard : d0 pattern = 1) : d1826 pattern ≤ (0 : Int) + d1664 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9807 (pattern : Twelve) (guard : d1878 pattern = 1) : d1827 pattern ≤ (0 : Int) + d1664 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1878, d1827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3 pattern childGuard
    simpa only [d1878, d1827, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1878, d1827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9806 pattern childGuard
    simpa only [d1878, d1827, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9808 (pattern : Twelve) (guard : d1 pattern = 1) : d871 pattern ≤ (1 : Int) + d871 pattern := by
  omega
theorem c9809 (pattern : Twelve) (guard : d1 pattern = 1) : d1323 pattern ≤ (1 : Int) + d1323 pattern := by
  omega
theorem c9810 (pattern : Twelve) (guard : d1 pattern = 1) : d1664 pattern ≤ (1 : Int) + d1664 pattern := by
  omega
theorem c9811 (pattern : Twelve) (guard : d1 pattern = 1) : d907 pattern ≤ (1 : Int) + d907 pattern := by
  omega
theorem c9812 (pattern : Twelve) (guard : d1 pattern = 1) : d1354 pattern ≤ (1 : Int) + d1354 pattern := by
  omega
theorem c9813 (pattern : Twelve) (guard : d1 pattern = 1) : d1678 pattern ≤ (1 : Int) + d1678 pattern := by
  omega
theorem c9814 (pattern : Twelve) (guard : d1 pattern = 1) : d926 pattern ≤ (1 : Int) + d926 pattern := by
  omega
theorem c9815 (pattern : Twelve) (guard : d1 pattern = 1) : d1367 pattern ≤ (1 : Int) + d1367 pattern := by
  omega
theorem c9816 (pattern : Twelve) (guard : d1 pattern = 1) : d1685 pattern ≤ (1 : Int) + d1685 pattern := by
  omega
theorem c9817 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (8 : Int) + d0 pattern := by
  omega
theorem c9818 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (8 : Int) + d1 pattern := by
  change (0 : Int) ≤ (8 : Int) + 1
  decide
theorem c9819 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (8 : Int) + d7 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9817 pattern childGuard
    simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9818 pattern childGuard
    simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9820 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (8 : Int) + d17 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9817 pattern childGuard
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9819 pattern childGuard
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9821 (pattern : Twelve) (guard : d1 pattern = 1) : d1 pattern ≤ (8 : Int) + d1 pattern := by
  omega
theorem c9822 (pattern : Twelve) (guard : d1 pattern = 1) : d26 pattern ≤ (8 : Int) + d27 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d26, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9820 pattern childGuard
    simpa only [d26, d27, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d26, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9821 pattern childGuard
    simpa only [d26, d27, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9823 (pattern : Twelve) (guard : d1 pattern = 1) : d7 pattern ≤ (8 : Int) + d1 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9818 pattern childGuard
    simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9821 pattern childGuard
    simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9824 (pattern : Twelve) (guard : d1 pattern = 1) : d17 pattern ≤ (8 : Int) + d814 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9819 pattern childGuard
    simpa only [d17, d814, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9823 pattern childGuard
    simpa only [d17, d814, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9825 (pattern : Twelve) (guard : d1 pattern = 1) : d27 pattern ≤ (8 : Int) + d816 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d27, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9824 pattern childGuard
    simpa only [d27, d816, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d27, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9821 pattern childGuard
    simpa only [d27, d816, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9826 (pattern : Twelve) (guard : d1 pattern = 1) : d50 pattern ≤ (8 : Int) + d824 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d50, d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9822 pattern childGuard
    simpa only [d50, d824, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d50, d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9825 pattern childGuard
    simpa only [d50, d824, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9827 (pattern : Twelve) (guard : d1 pattern = 1) : d72 pattern ≤ (8 : Int) + d838 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d72, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9817 pattern childGuard
    simpa only [d72, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d72, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9826 pattern childGuard
    simpa only [d72, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9828 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (8 : Int) + d2 pattern := by
  change (0 : Int) ≤ (8 : Int) + 2
  decide
theorem c9829 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (8 : Int) + d10 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9817 pattern childGuard
    simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9828 pattern childGuard
    simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9830 (pattern : Twelve) (guard : d1 pattern = 1) : d1 pattern ≤ (8 : Int) + d3 pattern := by
  change (1 : Int) ≤ (8 : Int) + 3
  decide
theorem c9831 (pattern : Twelve) (guard : d1 pattern = 1) : d7 pattern ≤ (8 : Int) + d11 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9818 pattern childGuard
    simpa only [d7, d11, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9830 pattern childGuard
    simpa only [d7, d11, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9832 (pattern : Twelve) (guard : d1 pattern = 1) : d17 pattern ≤ (8 : Int) + d19 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9829 pattern childGuard
    simpa only [d17, d19, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9831 pattern childGuard
    simpa only [d17, d19, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9833 (pattern : Twelve) (guard : d1 pattern = 1) : d1 pattern ≤ (8 : Int) + d2 pattern := by
  change (1 : Int) ≤ (8 : Int) + 2
  decide
theorem c9834 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (8 : Int) + d4 pattern := by
  change (2 : Int) ≤ (8 : Int) + 4
  decide
theorem c9835 (pattern : Twelve) (guard : d1 pattern = 1) : d8 pattern ≤ (8 : Int) + d16 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d8, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9833 pattern childGuard
    simpa only [d8, d16, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d8, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9834 pattern childGuard
    simpa only [d8, d16, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9836 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (8 : Int) + d3 pattern := by
  change (2 : Int) ≤ (8 : Int) + 3
  decide
theorem c9837 (pattern : Twelve) (guard : d1 pattern = 1) : d3 pattern ≤ (8 : Int) + d5 pattern := by
  change (3 : Int) ≤ (8 : Int) + 5
  decide
theorem c9838 (pattern : Twelve) (guard : d1 pattern = 1) : d9 pattern ≤ (8 : Int) + d12 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9836 pattern childGuard
    simpa only [d9, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9837 pattern childGuard
    simpa only [d9, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9839 (pattern : Twelve) (guard : d1 pattern = 1) : d18 pattern ≤ (8 : Int) + d25 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d18, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9835 pattern childGuard
    simpa only [d18, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d18, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9838 pattern childGuard
    simpa only [d18, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9840 (pattern : Twelve) (guard : d1 pattern = 1) : d28 pattern ≤ (8 : Int) + d817 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d28, d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9832 pattern childGuard
    simpa only [d28, d817, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d28, d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9839 pattern childGuard
    simpa only [d28, d817, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9841 (pattern : Twelve) (guard : d1 pattern = 1) : d10 pattern ≤ (8 : Int) + d16 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d10, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9828 pattern childGuard
    simpa only [d10, d16, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d10, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9834 pattern childGuard
    simpa only [d10, d16, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9842 (pattern : Twelve) (guard : d1 pattern = 1) : d11 pattern ≤ (8 : Int) + d12 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9830 pattern childGuard
    simpa only [d11, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9837 pattern childGuard
    simpa only [d11, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9843 (pattern : Twelve) (guard : d1 pattern = 1) : d19 pattern ≤ (8 : Int) + d25 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d19, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9841 pattern childGuard
    simpa only [d19, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d19, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9842 pattern childGuard
    simpa only [d19, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9844 (pattern : Twelve) (guard : d1 pattern = 1) : d6 pattern ≤ (8 : Int) + d6 pattern := by
  omega
theorem c9845 (pattern : Twelve) (guard : d1 pattern = 1) : d29 pattern ≤ (8 : Int) + d42 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d29, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9843 pattern childGuard
    simpa only [d29, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d29, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9844 pattern childGuard
    simpa only [d29, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9846 (pattern : Twelve) (guard : d1 pattern = 1) : d51 pattern ≤ (8 : Int) + d825 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d51, d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9840 pattern childGuard
    simpa only [d51, d825, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d51, d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9845 pattern childGuard
    simpa only [d51, d825, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9847 (pattern : Twelve) (guard : d1 pattern = 1) : d73 pattern ≤ (8 : Int) + d839 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d73, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9820 pattern childGuard
    simpa only [d73, d839, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d73, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9846 pattern childGuard
    simpa only [d73, d839, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9848 (pattern : Twelve) (guard : d1 pattern = 1) : d91 pattern ≤ (8 : Int) + d853 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d91, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9827 pattern childGuard
    simpa only [d91, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d91, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9847 pattern childGuard
    simpa only [d91, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9849 (pattern : Twelve) (guard : d1 pattern = 1) : d30 pattern ≤ (8 : Int) + d30 pattern := by
  omega
theorem c9850 (pattern : Twelve) (guard : d1 pattern = 1) : d3 pattern ≤ (8 : Int) + d6 pattern := by
  change (3 : Int) ≤ (8 : Int) + 6
  decide
theorem c9851 (pattern : Twelve) (guard : d1 pattern = 1) : d5 pattern ≤ (8 : Int) + d6 pattern := by
  change (5 : Int) ≤ (8 : Int) + 6
  decide
theorem c9852 (pattern : Twelve) (guard : d1 pattern = 1) : d12 pattern ≤ (8 : Int) + d6 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9850 pattern childGuard
    simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9851 pattern childGuard
    simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9853 (pattern : Twelve) (guard : d1 pattern = 1) : d4 pattern ≤ (8 : Int) + d6 pattern := by
  change (4 : Int) ≤ (8 : Int) + 6
  decide
theorem c9854 (pattern : Twelve) (guard : d1 pattern = 1) : d13 pattern ≤ (8 : Int) + d6 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9853 pattern childGuard
    simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9844 pattern childGuard
    simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9855 (pattern : Twelve) (guard : d1 pattern = 1) : d20 pattern ≤ (8 : Int) + d6 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9852 pattern childGuard
    simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9854 pattern childGuard
    simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9856 (pattern : Twelve) (guard : d1 pattern = 1) : d31 pattern ≤ (8 : Int) + d35 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d31, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9817 pattern childGuard
    simpa only [d31, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d31, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9855 pattern childGuard
    simpa only [d31, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9857 (pattern : Twelve) (guard : d1 pattern = 1) : d52 pattern ≤ (8 : Int) + d56 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d52, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9849 pattern childGuard
    simpa only [d52, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d52, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9856 pattern childGuard
    simpa only [d52, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9858 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (8 : Int) + d2 pattern := by
  omega
theorem c9859 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (8 : Int) + d9 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9858 pattern childGuard
    simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9836 pattern childGuard
    simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9860 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (8 : Int) + d23 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9858 pattern childGuard
    simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9859 pattern childGuard
    simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9861 (pattern : Twelve) (guard : d1 pattern = 1) : d30 pattern ≤ (8 : Int) + d34 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d30, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9820 pattern childGuard
    simpa only [d30, d34, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d30, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9860 pattern childGuard
    simpa only [d30, d34, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9862 (pattern : Twelve) (guard : d1 pattern = 1) : d14 pattern ≤ (8 : Int) + d6 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9851 pattern childGuard
    simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9844 pattern childGuard
    simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9863 (pattern : Twelve) (guard : d1 pattern = 1) : d21 pattern ≤ (8 : Int) + d6 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9854 pattern childGuard
    simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9862 pattern childGuard
    simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9864 (pattern : Twelve) (guard : d1 pattern = 1) : d32 pattern ≤ (8 : Int) + d818 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d32, d818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9824 pattern childGuard
    simpa only [d32, d818, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d32, d818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9863 pattern childGuard
    simpa only [d32, d818, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9865 (pattern : Twelve) (guard : d1 pattern = 1) : d53 pattern ≤ (8 : Int) + d826 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d53, d826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9861 pattern childGuard
    simpa only [d53, d826, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d53, d826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9864 pattern childGuard
    simpa only [d53, d826, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9866 (pattern : Twelve) (guard : d1 pattern = 1) : d74 pattern ≤ (8 : Int) + d840 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d74, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9857 pattern childGuard
    simpa only [d74, d840, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d74, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9865 pattern childGuard
    simpa only [d74, d840, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9867 (pattern : Twelve) (guard : d1 pattern = 1) : d22 pattern ≤ (8 : Int) + d6 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9862 pattern childGuard
    simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9844 pattern childGuard
    simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9868 (pattern : Twelve) (guard : d1 pattern = 1) : d33 pattern ≤ (8 : Int) + d36 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d33, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9820 pattern childGuard
    simpa only [d33, d36, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d33, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9867 pattern childGuard
    simpa only [d33, d36, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9869 (pattern : Twelve) (guard : d1 pattern = 1) : d54 pattern ≤ (8 : Int) + d827 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d54, d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9861 pattern childGuard
    simpa only [d54, d827, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d54, d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9868 pattern childGuard
    simpa only [d54, d827, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9870 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (8 : Int) + d16 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9858 pattern childGuard
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9834 pattern childGuard
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9871 (pattern : Twelve) (guard : d1 pattern = 1) : d23 pattern ≤ (8 : Int) + d25 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9870 pattern childGuard
    simpa only [d23, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9838 pattern childGuard
    simpa only [d23, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9872 (pattern : Twelve) (guard : d1 pattern = 1) : d34 pattern ≤ (8 : Int) + d817 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d34, d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9832 pattern childGuard
    simpa only [d34, d817, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d34, d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9871 pattern childGuard
    simpa only [d34, d817, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9873 (pattern : Twelve) (guard : d1 pattern = 1) : d55 pattern ≤ (8 : Int) + d825 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d55, d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9872 pattern childGuard
    simpa only [d55, d825, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d55, d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9845 pattern childGuard
    simpa only [d55, d825, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9874 (pattern : Twelve) (guard : d1 pattern = 1) : d75 pattern ≤ (8 : Int) + d841 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d75, d841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9869 pattern childGuard
    simpa only [d75, d841, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d75, d841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9873 pattern childGuard
    simpa only [d75, d841, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9875 (pattern : Twelve) (guard : d1 pattern = 1) : d92 pattern ≤ (8 : Int) + d854 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d92, d854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9866 pattern childGuard
    simpa only [d92, d854, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d92, d854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9874 pattern childGuard
    simpa only [d92, d854, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9876 (pattern : Twelve) (guard : d1 pattern = 1) : d102 pattern ≤ (8 : Int) + d861 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d102, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9848 pattern childGuard
    simpa only [d102, d861, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d102, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9875 pattern childGuard
    simpa only [d102, d861, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9877 (pattern : Twelve) (guard : d1 pattern = 1) : d76 pattern ≤ (8 : Int) + d839 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d76, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9820 pattern childGuard
    simpa only [d76, d839, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d76, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9873 pattern childGuard
    simpa only [d76, d839, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9878 (pattern : Twelve) (guard : d1 pattern = 1) : d93 pattern ≤ (8 : Int) + d853 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d93, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9827 pattern childGuard
    simpa only [d93, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d93, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9877 pattern childGuard
    simpa only [d93, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9879 (pattern : Twelve) (guard : d1 pattern = 1) : d56 pattern ≤ (8 : Int) + d56 pattern := by
  omega
theorem c9880 (pattern : Twelve) (guard : d1 pattern = 1) : d36 pattern ≤ (8 : Int) + d818 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d36, d818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9824 pattern childGuard
    simpa only [d36, d818, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d36, d818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9844 pattern childGuard
    simpa only [d36, d818, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9881 (pattern : Twelve) (guard : d1 pattern = 1) : d57 pattern ≤ (8 : Int) + d826 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d57, d826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9861 pattern childGuard
    simpa only [d57, d826, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d57, d826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9880 pattern childGuard
    simpa only [d57, d826, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9882 (pattern : Twelve) (guard : d1 pattern = 1) : d77 pattern ≤ (8 : Int) + d840 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d77, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9879 pattern childGuard
    simpa only [d77, d840, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d77, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9881 pattern childGuard
    simpa only [d77, d840, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9883 (pattern : Twelve) (guard : d1 pattern = 1) : d35 pattern ≤ (8 : Int) + d36 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d35, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9820 pattern childGuard
    simpa only [d35, d36, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d35, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9844 pattern childGuard
    simpa only [d35, d36, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9884 (pattern : Twelve) (guard : d1 pattern = 1) : d56 pattern ≤ (8 : Int) + d827 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d56, d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9861 pattern childGuard
    simpa only [d56, d827, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d56, d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9883 pattern childGuard
    simpa only [d56, d827, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9885 (pattern : Twelve) (guard : d1 pattern = 1) : d78 pattern ≤ (8 : Int) + d841 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d78, d841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9884 pattern childGuard
    simpa only [d78, d841, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d78, d841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9873 pattern childGuard
    simpa only [d78, d841, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9886 (pattern : Twelve) (guard : d1 pattern = 1) : d94 pattern ≤ (8 : Int) + d854 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d94, d854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9882 pattern childGuard
    simpa only [d94, d854, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d94, d854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9885 pattern childGuard
    simpa only [d94, d854, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9887 (pattern : Twelve) (guard : d1 pattern = 1) : d103 pattern ≤ (8 : Int) + d861 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d103, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9878 pattern childGuard
    simpa only [d103, d861, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d103, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9886 pattern childGuard
    simpa only [d103, d861, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9888 (pattern : Twelve) (guard : d1 pattern = 1) : d110 pattern ≤ (8 : Int) + d861 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9876 pattern childGuard
    simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9887 pattern childGuard
    simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9889 (pattern : Twelve) (guard : d1 pattern = 1) : d3 pattern ≤ (8 : Int) + d3 pattern := by
  omega
theorem c9890 (pattern : Twelve) (guard : d1 pattern = 1) : d37 pattern ≤ (8 : Int) + d819 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d37, d819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9824 pattern childGuard
    simpa only [d37, d819, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d37, d819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9889 pattern childGuard
    simpa only [d37, d819, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9891 (pattern : Twelve) (guard : d1 pattern = 1) : d58 pattern ≤ (8 : Int) + d828 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d58, d828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9861 pattern childGuard
    simpa only [d58, d828, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d58, d828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9890 pattern childGuard
    simpa only [d58, d828, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9892 (pattern : Twelve) (guard : d1 pattern = 1) : d79 pattern ≤ (8 : Int) + d842 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d79, d842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9849 pattern childGuard
    simpa only [d79, d842, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d79, d842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9891 pattern childGuard
    simpa only [d79, d842, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9893 (pattern : Twelve) (guard : d1 pattern = 1) : d80 pattern ≤ (8 : Int) + d843 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d80, d843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9861 pattern childGuard
    simpa only [d80, d843, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d80, d843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9873 pattern childGuard
    simpa only [d80, d843, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9894 (pattern : Twelve) (guard : d1 pattern = 1) : d95 pattern ≤ (8 : Int) + d855 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d95, d855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9892 pattern childGuard
    simpa only [d95, d855, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d95, d855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9893 pattern childGuard
    simpa only [d95, d855, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9895 (pattern : Twelve) (guard : d1 pattern = 1) : d59 pattern ≤ (8 : Int) + d59 pattern := by
  omega
theorem c9896 (pattern : Twelve) (guard : d1 pattern = 1) : d4 pattern ≤ (8 : Int) + d4 pattern := by
  omega
theorem c9897 (pattern : Twelve) (guard : d1 pattern = 1) : d4 pattern ≤ (8 : Int) + d5 pattern := by
  change (4 : Int) ≤ (8 : Int) + 5
  decide
theorem c9898 (pattern : Twelve) (guard : d1 pattern = 1) : d4 pattern ≤ (8 : Int) + d15 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9896 pattern childGuard
    simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9897 pattern childGuard
    simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9899 (pattern : Twelve) (guard : d1 pattern = 1) : d4 pattern ≤ (8 : Int) + d24 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9896 pattern childGuard
    simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9898 pattern childGuard
    simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9900 (pattern : Twelve) (guard : d1 pattern = 1) : d38 pattern ≤ (8 : Int) + d41 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d38, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9860 pattern childGuard
    simpa only [d38, d41, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d38, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9899 pattern childGuard
    simpa only [d38, d41, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9901 (pattern : Twelve) (guard : d1 pattern = 1) : d9 pattern ≤ (8 : Int) + d3 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9836 pattern childGuard
    simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9889 pattern childGuard
    simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9902 (pattern : Twelve) (guard : d1 pattern = 1) : d23 pattern ≤ (8 : Int) + d815 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, d815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9859 pattern childGuard
    simpa only [d23, d815, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, d815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9901 pattern childGuard
    simpa only [d23, d815, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9903 (pattern : Twelve) (guard : d1 pattern = 1) : d40 pattern ≤ (8 : Int) + d820 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d40, d820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9902 pattern childGuard
    simpa only [d40, d820, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d40, d820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9844 pattern childGuard
    simpa only [d40, d820, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9904 (pattern : Twelve) (guard : d1 pattern = 1) : d60 pattern ≤ (8 : Int) + d829 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d60, d829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9900 pattern childGuard
    simpa only [d60, d829, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d60, d829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9903 pattern childGuard
    simpa only [d60, d829, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9905 (pattern : Twelve) (guard : d1 pattern = 1) : d81 pattern ≤ (8 : Int) + d844 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d81, d844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9895 pattern childGuard
    simpa only [d81, d844, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d81, d844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9904 pattern childGuard
    simpa only [d81, d844, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9906 (pattern : Twelve) (guard : d1 pattern = 1) : d39 pattern ≤ (8 : Int) + d40 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d39, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9860 pattern childGuard
    simpa only [d39, d40, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d39, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9844 pattern childGuard
    simpa only [d39, d40, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9907 (pattern : Twelve) (guard : d1 pattern = 1) : d59 pattern ≤ (8 : Int) + d830 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d59, d830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9900 pattern childGuard
    simpa only [d59, d830, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d59, d830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9906 pattern childGuard
    simpa only [d59, d830, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9908 (pattern : Twelve) (guard : d1 pattern = 1) : d4 pattern ≤ (8 : Int) + d13 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9896 pattern childGuard
    simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9853 pattern childGuard
    simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9909 (pattern : Twelve) (guard : d1 pattern = 1) : d15 pattern ≤ (8 : Int) + d14 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d15, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9897 pattern childGuard
    simpa only [d15, d14, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d15, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9851 pattern childGuard
    simpa only [d15, d14, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9910 (pattern : Twelve) (guard : d1 pattern = 1) : d24 pattern ≤ (8 : Int) + d21 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d24, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9908 pattern childGuard
    simpa only [d24, d21, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d24, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9909 pattern childGuard
    simpa only [d24, d21, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9911 (pattern : Twelve) (guard : d1 pattern = 1) : d41 pattern ≤ (8 : Int) + d821 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d41, d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9871 pattern childGuard
    simpa only [d41, d821, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d41, d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9910 pattern childGuard
    simpa only [d41, d821, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9912 (pattern : Twelve) (guard : d1 pattern = 1) : d16 pattern ≤ (8 : Int) + d13 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d16, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9834 pattern childGuard
    simpa only [d16, d13, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d16, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9853 pattern childGuard
    simpa only [d16, d13, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9913 (pattern : Twelve) (guard : d1 pattern = 1) : d12 pattern ≤ (8 : Int) + d14 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d12, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9837 pattern childGuard
    simpa only [d12, d14, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d12, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9851 pattern childGuard
    simpa only [d12, d14, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9914 (pattern : Twelve) (guard : d1 pattern = 1) : d25 pattern ≤ (8 : Int) + d21 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d25, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9912 pattern childGuard
    simpa only [d25, d21, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d25, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9913 pattern childGuard
    simpa only [d25, d21, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9915 (pattern : Twelve) (guard : d1 pattern = 1) : d42 pattern ≤ (8 : Int) + d822 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d42, d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9914 pattern childGuard
    simpa only [d42, d822, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d42, d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9844 pattern childGuard
    simpa only [d42, d822, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9916 (pattern : Twelve) (guard : d1 pattern = 1) : d61 pattern ≤ (8 : Int) + d831 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d61, d831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9911 pattern childGuard
    simpa only [d61, d831, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d61, d831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9915 pattern childGuard
    simpa only [d61, d831, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9917 (pattern : Twelve) (guard : d1 pattern = 1) : d82 pattern ≤ (8 : Int) + d845 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d82, d845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9907 pattern childGuard
    simpa only [d82, d845, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d82, d845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9916 pattern childGuard
    simpa only [d82, d845, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9918 (pattern : Twelve) (guard : d1 pattern = 1) : d96 pattern ≤ (8 : Int) + d856 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d96, d856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9905 pattern childGuard
    simpa only [d96, d856, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d96, d856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9917 pattern childGuard
    simpa only [d96, d856, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9919 (pattern : Twelve) (guard : d1 pattern = 1) : d104 pattern ≤ (8 : Int) + d862 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d104, d862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9894 pattern childGuard
    simpa only [d104, d862, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d104, d862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9918 pattern childGuard
    simpa only [d104, d862, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9920 (pattern : Twelve) (guard : d1 pattern = 1) : d105 pattern ≤ (8 : Int) + d863 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d105, d863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9886 pattern childGuard
    simpa only [d105, d863, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d105, d863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9844 pattern childGuard
    simpa only [d105, d863, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9921 (pattern : Twelve) (guard : d1 pattern = 1) : d111 pattern ≤ (8 : Int) + d867 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d111, d867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9919 pattern childGuard
    simpa only [d111, d867, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d111, d867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9920 pattern childGuard
    simpa only [d111, d867, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9922 (pattern : Twelve) (guard : d1 pattern = 1) : d114 pattern ≤ (8 : Int) + d869 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d114, d869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9888 pattern childGuard
    simpa only [d114, d869, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d114, d869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9921 pattern childGuard
    simpa only [d114, d869, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9923 (pattern : Twelve) (guard : d1 pattern = 1) : d30 pattern ≤ (8 : Int) + d823 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d30, d823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9820 pattern childGuard
    simpa only [d30, d823, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d30, d823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9858 pattern childGuard
    simpa only [d30, d823, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9924 (pattern : Twelve) (guard : d1 pattern = 1) : d80 pattern ≤ (8 : Int) + d846 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d80, d846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9923 pattern childGuard
    simpa only [d80, d846, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d80, d846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9873 pattern childGuard
    simpa only [d80, d846, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9925 (pattern : Twelve) (guard : d1 pattern = 1) : d97 pattern ≤ (8 : Int) + d857 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d97, d857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9827 pattern childGuard
    simpa only [d97, d857, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d97, d857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9924 pattern childGuard
    simpa only [d97, d857, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9926 (pattern : Twelve) (guard : d1 pattern = 1) : d43 pattern ≤ (8 : Int) + d45 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d43, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9821 pattern childGuard
    simpa only [d43, d45, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d43, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9863 pattern childGuard
    simpa only [d43, d45, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9927 (pattern : Twelve) (guard : d1 pattern = 1) : d62 pattern ≤ (8 : Int) + d832 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d62, d832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9861 pattern childGuard
    simpa only [d62, d832, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d62, d832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9926 pattern childGuard
    simpa only [d62, d832, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9928 (pattern : Twelve) (guard : d1 pattern = 1) : d83 pattern ≤ (8 : Int) + d847 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d83, d847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9857 pattern childGuard
    simpa only [d83, d847, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d83, d847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9927 pattern childGuard
    simpa only [d83, d847, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9929 (pattern : Twelve) (guard : d1 pattern = 1) : d44 pattern ≤ (8 : Int) + d39 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d44, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9858 pattern childGuard
    simpa only [d44, d39, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d44, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9867 pattern childGuard
    simpa only [d44, d39, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9930 (pattern : Twelve) (guard : d1 pattern = 1) : d63 pattern ≤ (8 : Int) + d833 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d63, d833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9861 pattern childGuard
    simpa only [d63, d833, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d63, d833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9929 pattern childGuard
    simpa only [d63, d833, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9931 (pattern : Twelve) (guard : d1 pattern = 1) : d40 pattern ≤ (8 : Int) + d42 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d40, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9871 pattern childGuard
    simpa only [d40, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d40, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9844 pattern childGuard
    simpa only [d40, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9932 (pattern : Twelve) (guard : d1 pattern = 1) : d64 pattern ≤ (8 : Int) + d825 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d64, d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9872 pattern childGuard
    simpa only [d64, d825, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d64, d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9931 pattern childGuard
    simpa only [d64, d825, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9933 (pattern : Twelve) (guard : d1 pattern = 1) : d84 pattern ≤ (8 : Int) + d848 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d84, d848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9930 pattern childGuard
    simpa only [d84, d848, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d84, d848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9932 pattern childGuard
    simpa only [d84, d848, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9934 (pattern : Twelve) (guard : d1 pattern = 1) : d98 pattern ≤ (8 : Int) + d858 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d98, d858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9928 pattern childGuard
    simpa only [d98, d858, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d98, d858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9933 pattern childGuard
    simpa only [d98, d858, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9935 (pattern : Twelve) (guard : d1 pattern = 1) : d106 pattern ≤ (8 : Int) + d864 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d106, d864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9925 pattern childGuard
    simpa only [d106, d864, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d106, d864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9934 pattern childGuard
    simpa only [d106, d864, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9936 (pattern : Twelve) (guard : d1 pattern = 1) : d45 pattern ≤ (8 : Int) + d45 pattern := by
  omega
theorem c9937 (pattern : Twelve) (guard : d1 pattern = 1) : d65 pattern ≤ (8 : Int) + d832 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d65, d832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9861 pattern childGuard
    simpa only [d65, d832, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d65, d832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9936 pattern childGuard
    simpa only [d65, d832, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9938 (pattern : Twelve) (guard : d1 pattern = 1) : d85 pattern ≤ (8 : Int) + d847 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d85, d847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9879 pattern childGuard
    simpa only [d85, d847, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d85, d847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9937 pattern childGuard
    simpa only [d85, d847, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9939 (pattern : Twelve) (guard : d1 pattern = 1) : d39 pattern ≤ (8 : Int) + d39 pattern := by
  omega
end NetHack.Sokoban21.Diagram
