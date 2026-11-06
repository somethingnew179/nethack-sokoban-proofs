/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons139
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c19600 (pattern : Twelve) (guard : d1 pattern = 1) : d101 pattern ≤ (16 : Int) + d899 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d101, d899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19599 pattern childGuard
    simpa only [d101, d899, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d101, d899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19594 pattern childGuard
    simpa only [d101, d899, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19601 (pattern : Twelve) (guard : d1 pattern = 1) : d799 pattern ≤ (16 : Int) + d902 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d799, d902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19574 pattern childGuard
    simpa only [d799, d902, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d799, d902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19600 pattern childGuard
    simpa only [d799, d902, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19602 (pattern : Twelve) (guard : d1 pattern = 1) : d802 pattern ≤ (16 : Int) + d902 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19596 pattern childGuard
    simpa only [d802, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19601 pattern childGuard
    simpa only [d802, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19603 (pattern : Twelve) (guard : d1 pattern = 1) : d5 pattern ≤ (16 : Int) + d4 pattern := by
  change (5 : Int) ≤ (16 : Int) + 4
  decide
theorem c19604 (pattern : Twelve) (guard : d1 pattern = 1) : d5 pattern ≤ (16 : Int) + d15 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19603 pattern childGuard
    simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19589 pattern childGuard
    simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19605 (pattern : Twelve) (guard : d1 pattern = 1) : d5 pattern ≤ (16 : Int) + d24 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19603 pattern childGuard
    simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19604 pattern childGuard
    simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19606 (pattern : Twelve) (guard : d1 pattern = 1) : d780 pattern ≤ (16 : Int) + d878 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d780, d878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19582 pattern childGuard
    simpa only [d780, d878, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d780, d878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19605 pattern childGuard
    simpa only [d780, d878, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19607 (pattern : Twelve) (guard : d1 pattern = 1) : d784 pattern ≤ (16 : Int) + d885 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d784, d885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19579 pattern childGuard
    simpa only [d784, d885, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d784, d885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19606 pattern childGuard
    simpa only [d784, d885, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19608 (pattern : Twelve) (guard : d1 pattern = 1) : d791 pattern ≤ (16 : Int) + d894 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d791, d894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19575 pattern childGuard
    simpa only [d791, d894, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d791, d894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19607 pattern childGuard
    simpa only [d791, d894, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19609 (pattern : Twelve) (guard : d1 pattern = 1) : d6 pattern ≤ (16 : Int) + d3 pattern := by
  change (6 : Int) ≤ (16 : Int) + 3
  decide
theorem c19610 (pattern : Twelve) (guard : d1 pattern = 1) : d6 pattern ≤ (16 : Int) + d4 pattern := by
  change (6 : Int) ≤ (16 : Int) + 4
  decide
theorem c19611 (pattern : Twelve) (guard : d1 pattern = 1) : d6 pattern ≤ (16 : Int) + d117 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19609 pattern childGuard
    simpa only [d117, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19610 pattern childGuard
    simpa only [d117, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19612 (pattern : Twelve) (guard : d1 pattern = 1) : d6 pattern ≤ (16 : Int) + d119 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19609 pattern childGuard
    simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19611 pattern childGuard
    simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19613 (pattern : Twelve) (guard : d1 pattern = 1) : d48 pattern ≤ (16 : Int) + d879 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d48, d879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19565 pattern childGuard
    simpa only [d48, d879, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d48, d879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19612 pattern childGuard
    simpa only [d48, d879, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19614 (pattern : Twelve) (guard : d1 pattern = 1) : d70 pattern ≤ (16 : Int) + d886 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d70, d886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19521 pattern childGuard
    simpa only [d70, d886, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d70, d886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19613 pattern childGuard
    simpa only [d70, d886, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19615 (pattern : Twelve) (guard : d1 pattern = 1) : d90 pattern ≤ (16 : Int) + d895 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d90, d895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19614 pattern childGuard
    simpa only [d90, d895, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d90, d895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19593 pattern childGuard
    simpa only [d90, d895, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19616 (pattern : Twelve) (guard : d1 pattern = 1) : d796 pattern ≤ (16 : Int) + d900 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d796, d900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19608 pattern childGuard
    simpa only [d796, d900, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d796, d900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19615 pattern childGuard
    simpa only [d796, d900, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19617 (pattern : Twelve) (guard : d1 pattern = 1) : d48 pattern ≤ (16 : Int) + d38 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d48, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19517 pattern childGuard
    simpa only [d48, d38, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d48, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19610 pattern childGuard
    simpa only [d48, d38, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19618 (pattern : Twelve) (guard : d1 pattern = 1) : d48 pattern ≤ (16 : Int) + d39 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d48, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19517 pattern childGuard
    simpa only [d48, d39, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d48, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19470 pattern childGuard
    simpa only [d48, d39, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19619 (pattern : Twelve) (guard : d1 pattern = 1) : d48 pattern ≤ (16 : Int) + d59 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19617 pattern childGuard
    simpa only [d59, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19618 pattern childGuard
    simpa only [d59, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19620 (pattern : Twelve) (guard : d1 pattern = 1) : d6 pattern ≤ (16 : Int) + d5 pattern := by
  change (6 : Int) ≤ (16 : Int) + 5
  decide
theorem c19621 (pattern : Twelve) (guard : d1 pattern = 1) : d6 pattern ≤ (16 : Int) + d14 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19620 pattern childGuard
    simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19470 pattern childGuard
    simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19622 (pattern : Twelve) (guard : d1 pattern = 1) : d6 pattern ≤ (16 : Int) + d22 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19621 pattern childGuard
    simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19470 pattern childGuard
    simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19623 (pattern : Twelve) (guard : d1 pattern = 1) : d48 pattern ≤ (16 : Int) + d127 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d48, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19520 pattern childGuard
    simpa only [d48, d127, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d48, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19622 pattern childGuard
    simpa only [d48, d127, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19624 (pattern : Twelve) (guard : d1 pattern = 1) : d5 pattern ≤ (16 : Int) + d3 pattern := by
  change (5 : Int) ≤ (16 : Int) + 3
  decide
theorem c19625 (pattern : Twelve) (guard : d1 pattern = 1) : d5 pattern ≤ (16 : Int) + d117 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19624 pattern childGuard
    simpa only [d117, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19603 pattern childGuard
    simpa only [d117, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19626 (pattern : Twelve) (guard : d1 pattern = 1) : d5 pattern ≤ (16 : Int) + d873 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19625 pattern childGuard
    simpa only [d873, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19604 pattern childGuard
    simpa only [d873, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19627 (pattern : Twelve) (guard : d1 pattern = 1) : d781 pattern ≤ (16 : Int) + d880 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d781, d880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19626 pattern childGuard
    simpa only [d781, d880, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d781, d880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19470 pattern childGuard
    simpa only [d781, d880, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19628 (pattern : Twelve) (guard : d1 pattern = 1) : d785 pattern ≤ (16 : Int) + d887 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d785, d887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19623 pattern childGuard
    simpa only [d785, d887, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d785, d887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19627 pattern childGuard
    simpa only [d785, d887, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19629 (pattern : Twelve) (guard : d1 pattern = 1) : d792 pattern ≤ (16 : Int) + d896 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d792, d896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19619 pattern childGuard
    simpa only [d792, d896, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d792, d896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19628 pattern childGuard
    simpa only [d792, d896, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19630 (pattern : Twelve) (guard : d1 pattern = 1) : d6 pattern ≤ (16 : Int) + d118 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19620 pattern childGuard
    simpa only [d118, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19621 pattern childGuard
    simpa only [d118, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19631 (pattern : Twelve) (guard : d1 pattern = 1) : d48 pattern ≤ (16 : Int) + d881 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d48, d881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19520 pattern childGuard
    simpa only [d48, d881, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d48, d881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19630 pattern childGuard
    simpa only [d48, d881, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19632 (pattern : Twelve) (guard : d1 pattern = 1) : d6 pattern ≤ (16 : Int) + d125 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19612 pattern childGuard
    simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19470 pattern childGuard
    simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19633 (pattern : Twelve) (guard : d1 pattern = 1) : d786 pattern ≤ (16 : Int) + d888 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d786, d888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19631 pattern childGuard
    simpa only [d786, d888, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d786, d888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19632 pattern childGuard
    simpa only [d786, d888, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19634 (pattern : Twelve) (guard : d1 pattern = 1) : d787 pattern ≤ (16 : Int) + d889 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d787, d889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19592 pattern childGuard
    simpa only [d787, d889, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d787, d889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19470 pattern childGuard
    simpa only [d787, d889, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19635 (pattern : Twelve) (guard : d1 pattern = 1) : d793 pattern ≤ (16 : Int) + d897 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d793, d897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19633 pattern childGuard
    simpa only [d793, d897, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d793, d897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19634 pattern childGuard
    simpa only [d793, d897, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19636 (pattern : Twelve) (guard : d1 pattern = 1) : d797 pattern ≤ (16 : Int) + d901 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d797, d901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19629 pattern childGuard
    simpa only [d797, d901, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d797, d901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19635 pattern childGuard
    simpa only [d797, d901, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19637 (pattern : Twelve) (guard : d1 pattern = 1) : d800 pattern ≤ (16 : Int) + d903 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d800, d903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19616 pattern childGuard
    simpa only [d800, d903, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d800, d903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19636 pattern childGuard
    simpa only [d800, d903, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19638 (pattern : Twelve) (guard : d1 pattern = 1) : d801 pattern ≤ (16 : Int) + d904 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d801, d904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19600 pattern childGuard
    simpa only [d801, d904, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d801, d904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19470 pattern childGuard
    simpa only [d801, d904, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19639 (pattern : Twelve) (guard : d1 pattern = 1) : d803 pattern ≤ (16 : Int) + d905 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d803, d905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19637 pattern childGuard
    simpa only [d803, d905, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d803, d905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19638 pattern childGuard
    simpa only [d803, d905, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19640 (pattern : Twelve) (guard : d1 pattern = 1) : d804 pattern ≤ (16 : Int) + d906 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d804, d906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19602 pattern childGuard
    simpa only [d804, d906, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d804, d906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19639 pattern childGuard
    simpa only [d804, d906, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19641 (pattern : Twelve) (guard : d1872 pattern = 1) : d805 pattern ≤ (16 : Int) + d906 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1872, d805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19552 pattern childGuard
    simpa only [d1872, d805, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1872, d805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19640 pattern childGuard
    simpa only [d1872, d805, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19642 (pattern : Twelve) (guard : d1872 pattern = 1) : d806 pattern ≤ (16 : Int) + d907 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1872 pattern = 1 := by simpa only [d806, d907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19551 pattern childGuard
    simpa only [d806, d907, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1872 pattern = 1 := by simpa only [d806, d907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19641 pattern childGuard
    simpa only [d806, d907, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19643 (pattern : Twelve) (guard : d0 pattern = 1) : d869 pattern ≤ (16 : Int) + d1321 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c19644 (pattern : Twelve) (guard : d1 pattern = 1) : d1 pattern ≤ (16 : Int) + d2 pattern := by
  change (1 : Int) ≤ (16 : Int) + 2
  decide
theorem c19645 (pattern : Twelve) (guard : d1 pattern = 1) : d7 pattern ≤ (16 : Int) + d8 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19439 pattern childGuard
    simpa only [d7, d8, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19644 pattern childGuard
    simpa only [d7, d8, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19646 (pattern : Twelve) (guard : d1 pattern = 1) : d17 pattern ≤ (16 : Int) + d1275 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, d1275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19440 pattern childGuard
    simpa only [d17, d1275, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, d1275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19645 pattern childGuard
    simpa only [d17, d1275, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19647 (pattern : Twelve) (guard : d1 pattern = 1) : d1 pattern ≤ (16 : Int) + d8 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19442 pattern childGuard
    simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19644 pattern childGuard
    simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19648 (pattern : Twelve) (guard : d1 pattern = 1) : d1 pattern ≤ (16 : Int) + d872 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19442 pattern childGuard
    simpa only [d872, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19647 pattern childGuard
    simpa only [d872, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19649 (pattern : Twelve) (guard : d1 pattern = 1) : d27 pattern ≤ (16 : Int) + d1278 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d27, d1278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19646 pattern childGuard
    simpa only [d27, d1278, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d27, d1278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19648 pattern childGuard
    simpa only [d27, d1278, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19650 (pattern : Twelve) (guard : d1 pattern = 1) : d814 pattern ≤ (16 : Int) + d872 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d814, d872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19444 pattern childGuard
    simpa only [d814, d872, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d814, d872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19647 pattern childGuard
    simpa only [d814, d872, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19651 (pattern : Twelve) (guard : d1 pattern = 1) : d816 pattern ≤ (16 : Int) + d872 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19650 pattern childGuard
    simpa only [d816, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19648 pattern childGuard
    simpa only [d816, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19652 (pattern : Twelve) (guard : d1 pattern = 1) : d824 pattern ≤ (16 : Int) + d1284 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d824, d1284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19649 pattern childGuard
    simpa only [d824, d1284, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d824, d1284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19651 pattern childGuard
    simpa only [d824, d1284, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19653 (pattern : Twelve) (guard : d1 pattern = 1) : d838 pattern ≤ (16 : Int) + d1293 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d838, d1293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19441 pattern childGuard
    simpa only [d838, d1293, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d838, d1293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19652 pattern childGuard
    simpa only [d838, d1293, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19654 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (16 : Int) + d11 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19450 pattern childGuard
    simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19462 pattern childGuard
    simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19655 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (16 : Int) + d19 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19567 pattern childGuard
    simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19654 pattern childGuard
    simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19656 (pattern : Twelve) (guard : d1 pattern = 1) : d823 pattern ≤ (16 : Int) + d19 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19458 pattern childGuard
    simpa only [d823, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19655 pattern childGuard
    simpa only [d823, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19657 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (16 : Int) + d6 pattern := by
  change (0 : Int) ≤ (16 : Int) + 6
  decide
theorem c19658 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (16 : Int) + d6 pattern := by
  change (2 : Int) ≤ (16 : Int) + 6
  decide
theorem c19659 (pattern : Twelve) (guard : d1 pattern = 1) : d10 pattern ≤ (16 : Int) + d6 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19657 pattern childGuard
    simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19658 pattern childGuard
    simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19660 (pattern : Twelve) (guard : d1 pattern = 1) : d1 pattern ≤ (16 : Int) + d6 pattern := by
  change (1 : Int) ≤ (16 : Int) + 6
  decide
theorem c19661 (pattern : Twelve) (guard : d1 pattern = 1) : d11 pattern ≤ (16 : Int) + d6 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19660 pattern childGuard
    simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19476 pattern childGuard
    simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19662 (pattern : Twelve) (guard : d1 pattern = 1) : d19 pattern ≤ (16 : Int) + d6 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19659 pattern childGuard
    simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19661 pattern childGuard
    simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19663 (pattern : Twelve) (guard : d1 pattern = 1) : d16 pattern ≤ (16 : Int) + d6 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19658 pattern childGuard
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19479 pattern childGuard
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19664 (pattern : Twelve) (guard : d1 pattern = 1) : d25 pattern ≤ (16 : Int) + d6 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19663 pattern childGuard
    simpa only [d25, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19478 pattern childGuard
    simpa only [d25, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19665 (pattern : Twelve) (guard : d1 pattern = 1) : d817 pattern ≤ (16 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19662 pattern childGuard
    simpa only [d817, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19664 pattern childGuard
    simpa only [d817, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19666 (pattern : Twelve) (guard : d1 pattern = 1) : d42 pattern ≤ (16 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19664 pattern childGuard
    simpa only [d42, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19470 pattern childGuard
    simpa only [d42, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19667 (pattern : Twelve) (guard : d1 pattern = 1) : d825 pattern ≤ (16 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19665 pattern childGuard
    simpa only [d825, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19666 pattern childGuard
    simpa only [d825, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19668 (pattern : Twelve) (guard : d1 pattern = 1) : d846 pattern ≤ (16 : Int) + d1294 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d846, d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19656 pattern childGuard
    simpa only [d846, d1294, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d846, d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19667 pattern childGuard
    simpa only [d846, d1294, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19669 (pattern : Twelve) (guard : d1 pattern = 1) : d857 pattern ≤ (16 : Int) + d1305 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d857, d1305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19653 pattern childGuard
    simpa only [d857, d1305, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d857, d1305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19668 pattern childGuard
    simpa only [d857, d1305, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19670 (pattern : Twelve) (guard : d1 pattern = 1) : d35 pattern ≤ (16 : Int) + d36 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d35, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19441 pattern childGuard
    simpa only [d35, d36, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d35, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19470 pattern childGuard
    simpa only [d35, d36, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19671 (pattern : Twelve) (guard : d1 pattern = 1) : d56 pattern ≤ (16 : Int) + d827 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d56, d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19486 pattern childGuard
    simpa only [d56, d827, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d56, d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19670 pattern childGuard
    simpa only [d56, d827, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19672 (pattern : Twelve) (guard : d1 pattern = 1) : d3 pattern ≤ (16 : Int) + d4 pattern := by
  change (3 : Int) ≤ (16 : Int) + 4
  decide
theorem c19673 (pattern : Twelve) (guard : d1 pattern = 1) : d9 pattern ≤ (16 : Int) + d117 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19462 pattern childGuard
    simpa only [d9, d117, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19672 pattern childGuard
    simpa only [d9, d117, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19674 (pattern : Twelve) (guard : d1 pattern = 1) : d23 pattern ≤ (16 : Int) + d1276 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, d1276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19484 pattern childGuard
    simpa only [d23, d1276, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, d1276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19673 pattern childGuard
    simpa only [d23, d1276, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19675 (pattern : Twelve) (guard : d1 pattern = 1) : d34 pattern ≤ (16 : Int) + d1279 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d34, d1279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19646 pattern childGuard
    simpa only [d34, d1279, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d34, d1279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19674 pattern childGuard
    simpa only [d34, d1279, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19676 (pattern : Twelve) (guard : d1 pattern = 1) : d45 pattern ≤ (16 : Int) + d1280 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d45, d1280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19648 pattern childGuard
    simpa only [d45, d1280, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d45, d1280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19470 pattern childGuard
    simpa only [d45, d1280, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19677 (pattern : Twelve) (guard : d1 pattern = 1) : d832 pattern ≤ (16 : Int) + d1285 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d832, d1285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19675 pattern childGuard
    simpa only [d832, d1285, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d832, d1285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19676 pattern childGuard
    simpa only [d832, d1285, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19678 (pattern : Twelve) (guard : d1 pattern = 1) : d847 pattern ≤ (16 : Int) + d1295 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d847, d1295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19671 pattern childGuard
    simpa only [d847, d1295, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d847, d1295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19677 pattern childGuard
    simpa only [d847, d1295, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19679 (pattern : Twelve) (guard : d1 pattern = 1) : d39 pattern ≤ (16 : Int) + d29 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d39, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19655 pattern childGuard
    simpa only [d39, d29, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d39, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19470 pattern childGuard
    simpa only [d39, d29, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19680 (pattern : Twelve) (guard : d1 pattern = 1) : d833 pattern ≤ (16 : Int) + d1286 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d833, d1286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19466 pattern childGuard
    simpa only [d833, d1286, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d833, d1286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19679 pattern childGuard
    simpa only [d833, d1286, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19681 (pattern : Twelve) (guard : d1 pattern = 1) : d848 pattern ≤ (16 : Int) + d1296 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d848, d1296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19680 pattern childGuard
    simpa only [d848, d1296, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d848, d1296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19667 pattern childGuard
    simpa only [d848, d1296, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19682 (pattern : Twelve) (guard : d1 pattern = 1) : d858 pattern ≤ (16 : Int) + d1306 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d858, d1306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19678 pattern childGuard
    simpa only [d858, d1306, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d858, d1306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19681 pattern childGuard
    simpa only [d858, d1306, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19683 (pattern : Twelve) (guard : d1 pattern = 1) : d864 pattern ≤ (16 : Int) + d1313 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d864, d1313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19669 pattern childGuard
    simpa only [d864, d1313, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d864, d1313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19682 pattern childGuard
    simpa only [d864, d1313, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19684 (pattern : Twelve) (guard : d1 pattern = 1) : d3 pattern ≤ (16 : Int) + d117 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19513 pattern childGuard
    simpa only [d117, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19672 pattern childGuard
    simpa only [d117, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19685 (pattern : Twelve) (guard : d1 pattern = 1) : d3 pattern ≤ (16 : Int) + d119 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19513 pattern childGuard
    simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19684 pattern childGuard
    simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19686 (pattern : Twelve) (guard : d1 pattern = 1) : d46 pattern ≤ (16 : Int) + d1281 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d46, d1281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19648 pattern childGuard
    simpa only [d46, d1281, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d46, d1281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19685 pattern childGuard
    simpa only [d46, d1281, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19687 (pattern : Twelve) (guard : d1 pattern = 1) : d834 pattern ≤ (16 : Int) + d1287 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d834, d1287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19675 pattern childGuard
    simpa only [d834, d1287, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d834, d1287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19686 pattern childGuard
    simpa only [d834, d1287, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19688 (pattern : Twelve) (guard : d1 pattern = 1) : d849 pattern ≤ (16 : Int) + d1297 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d849, d1297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19486 pattern childGuard
    simpa only [d849, d1297, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d849, d1297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19687 pattern childGuard
    simpa only [d849, d1297, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19689 (pattern : Twelve) (guard : d1 pattern = 1) : d4 pattern ≤ (16 : Int) + d12 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19518 pattern childGuard
    simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19527 pattern childGuard
    simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19690 (pattern : Twelve) (guard : d1 pattern = 1) : d4 pattern ≤ (16 : Int) + d25 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19588 pattern childGuard
    simpa only [d25, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19689 pattern childGuard
    simpa only [d25, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19691 (pattern : Twelve) (guard : d1 pattern = 1) : d38 pattern ≤ (16 : Int) + d817 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d38, d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19655 pattern childGuard
    simpa only [d38, d817, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d38, d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19690 pattern childGuard
    simpa only [d38, d817, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19692 (pattern : Twelve) (guard : d1 pattern = 1) : d835 pattern ≤ (16 : Int) + d817 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19466 pattern childGuard
    simpa only [d835, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19691 pattern childGuard
    simpa only [d835, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19693 (pattern : Twelve) (guard : d1 pattern = 1) : d850 pattern ≤ (16 : Int) + d1298 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d850, d1298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19692 pattern childGuard
    simpa only [d850, d1298, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d850, d1298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19667 pattern childGuard
    simpa only [d850, d1298, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19694 (pattern : Twelve) (guard : d1 pattern = 1) : d859 pattern ≤ (16 : Int) + d1307 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d859, d1307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19688 pattern childGuard
    simpa only [d859, d1307, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d859, d1307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19693 pattern childGuard
    simpa only [d859, d1307, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19695 (pattern : Twelve) (guard : d1 pattern = 1) : d39 pattern ≤ (16 : Int) + d40 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d39, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19485 pattern childGuard
    simpa only [d39, d40, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d39, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19470 pattern childGuard
    simpa only [d39, d40, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19696 (pattern : Twelve) (guard : d1 pattern = 1) : d59 pattern ≤ (16 : Int) + d830 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d59, d830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19530 pattern childGuard
    simpa only [d59, d830, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d59, d830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19695 pattern childGuard
    simpa only [d59, d830, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19697 (pattern : Twelve) (guard : d1 pattern = 1) : d24 pattern ≤ (16 : Int) + d1277 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d24, d1277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19528 pattern childGuard
    simpa only [d24, d1277, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d24, d1277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19540 pattern childGuard
    simpa only [d24, d1277, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19698 (pattern : Twelve) (guard : d1 pattern = 1) : d41 pattern ≤ (16 : Int) + d1282 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d41, d1282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19674 pattern childGuard
    simpa only [d41, d1282, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d41, d1282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19697 pattern childGuard
    simpa only [d41, d1282, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19699 (pattern : Twelve) (guard : d1 pattern = 1) : d47 pattern ≤ (16 : Int) + d125 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d47, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19685 pattern childGuard
    simpa only [d47, d125, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d47, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19470 pattern childGuard
    simpa only [d47, d125, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19700 (pattern : Twelve) (guard : d1 pattern = 1) : d836 pattern ≤ (16 : Int) + d1288 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d836, d1288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19698 pattern childGuard
    simpa only [d836, d1288, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d836, d1288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19699 pattern childGuard
    simpa only [d836, d1288, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19701 (pattern : Twelve) (guard : d1 pattern = 1) : d851 pattern ≤ (16 : Int) + d1299 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d851, d1299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19696 pattern childGuard
    simpa only [d851, d1299, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d851, d1299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19700 pattern childGuard
    simpa only [d851, d1299, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19702 (pattern : Twelve) (guard : d1 pattern = 1) : d48 pattern ≤ (16 : Int) + d42 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d48, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19690 pattern childGuard
    simpa only [d48, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d48, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19470 pattern childGuard
    simpa only [d48, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19703 (pattern : Twelve) (guard : d1 pattern = 1) : d837 pattern ≤ (16 : Int) + d1289 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d837, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19542 pattern childGuard
    simpa only [d837, d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d837, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19702 pattern childGuard
    simpa only [d837, d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19704 (pattern : Twelve) (guard : d1 pattern = 1) : d821 pattern ≤ (16 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19664 pattern childGuard
    simpa only [d821, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19491 pattern childGuard
    simpa only [d821, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19705 (pattern : Twelve) (guard : d1 pattern = 1) : d822 pattern ≤ (16 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19491 pattern childGuard
    simpa only [d822, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19470 pattern childGuard
    simpa only [d822, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19706 (pattern : Twelve) (guard : d1 pattern = 1) : d831 pattern ≤ (16 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19704 pattern childGuard
    simpa only [d831, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19705 pattern childGuard
    simpa only [d831, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19707 (pattern : Twelve) (guard : d1 pattern = 1) : d852 pattern ≤ (16 : Int) + d1300 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d852, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19703 pattern childGuard
    simpa only [d852, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d852, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19706 pattern childGuard
    simpa only [d852, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19708 (pattern : Twelve) (guard : d1 pattern = 1) : d860 pattern ≤ (16 : Int) + d1308 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d860, d1308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19701 pattern childGuard
    simpa only [d860, d1308, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d860, d1308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19707 pattern childGuard
    simpa only [d860, d1308, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19709 (pattern : Twelve) (guard : d1 pattern = 1) : d865 pattern ≤ (16 : Int) + d1314 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d865, d1314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19694 pattern childGuard
    simpa only [d865, d1314, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d865, d1314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19708 pattern childGuard
    simpa only [d865, d1314, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19710 (pattern : Twelve) (guard : d1 pattern = 1) : d866 pattern ≤ (16 : Int) + d1315 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d866, d1315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19682 pattern childGuard
    simpa only [d866, d1315, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d866, d1315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19470 pattern childGuard
    simpa only [d866, d1315, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19711 (pattern : Twelve) (guard : d1 pattern = 1) : d868 pattern ≤ (16 : Int) + d1319 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d868, d1319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19709 pattern childGuard
    simpa only [d868, d1319, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d868, d1319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19710 pattern childGuard
    simpa only [d868, d1319, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19712 (pattern : Twelve) (guard : d1 pattern = 1) : d870 pattern ≤ (16 : Int) + d1321 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d870, d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19683 pattern childGuard
    simpa only [d870, d1321, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d870, d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19711 pattern childGuard
    simpa only [d870, d1321, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19713 (pattern : Twelve) (guard : d1872 pattern = 1) : d871 pattern ≤ (16 : Int) + d1321 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1872, d871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19643 pattern childGuard
    simpa only [d1872, d871, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1872, d871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19712 pattern childGuard
    simpa only [d1872, d871, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19714 (pattern : Twelve) (guard : d0 pattern = 1) : d906 pattern ≤ (16 : Int) + d1353 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c19715 (pattern : Twelve) (guard : d1 pattern = 1) : d9 pattern ≤ (16 : Int) + d8 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19450 pattern childGuard
    simpa only [d9, d8, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19531 pattern childGuard
    simpa only [d9, d8, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19716 (pattern : Twelve) (guard : d1 pattern = 1) : d23 pattern ≤ (16 : Int) + d1275 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, d1275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19451 pattern childGuard
    simpa only [d23, d1275, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, d1275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19715 pattern childGuard
    simpa only [d23, d1275, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19717 (pattern : Twelve) (guard : d1 pattern = 1) : d3 pattern ≤ (16 : Int) + d11 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19553 pattern childGuard
    simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19513 pattern childGuard
    simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19718 (pattern : Twelve) (guard : d1 pattern = 1) : d3 pattern ≤ (16 : Int) + d16 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19531 pattern childGuard
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19672 pattern childGuard
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19719 (pattern : Twelve) (guard : d1 pattern = 1) : d3 pattern ≤ (16 : Int) + d1324 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19717 pattern childGuard
    simpa only [d1324, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19718 pattern childGuard
    simpa only [d1324, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19720 (pattern : Twelve) (guard : d1 pattern = 1) : d779 pattern ≤ (16 : Int) + d1325 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d779, d1325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19716 pattern childGuard
    simpa only [d779, d1325, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d779, d1325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19719 pattern childGuard
    simpa only [d779, d1325, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19721 (pattern : Twelve) (guard : d1 pattern = 1) : d815 pattern ≤ (16 : Int) + d872 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d815, d872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19557 pattern childGuard
    simpa only [d815, d872, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d815, d872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19554 pattern childGuard
    simpa only [d815, d872, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19722 (pattern : Twelve) (guard : d1 pattern = 1) : d1247 pattern ≤ (16 : Int) + d1326 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1247, d1326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19721 pattern childGuard
    simpa only [d1247, d1326, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1247, d1326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19719 pattern childGuard
    simpa only [d1247, d1326, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19723 (pattern : Twelve) (guard : d1 pattern = 1) : d1249 pattern ≤ (16 : Int) + d1333 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1249, d1333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19720 pattern childGuard
    simpa only [d1249, d1333, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1249, d1333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19722 pattern childGuard
    simpa only [d1249, d1333, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19724 (pattern : Twelve) (guard : d1 pattern = 1) : d1253 pattern ≤ (16 : Int) + d1339 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1253, d1339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19452 pattern childGuard
    simpa only [d1253, d1339, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1253, d1339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19723 pattern childGuard
    simpa only [d1253, d1339, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19725 (pattern : Twelve) (guard : d1 pattern = 1) : d4 pattern ≤ (16 : Int) + d10 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19562 pattern childGuard
    simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19517 pattern childGuard
    simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19726 (pattern : Twelve) (guard : d1 pattern = 1) : d4 pattern ≤ (16 : Int) + d11 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19563 pattern childGuard
    simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19518 pattern childGuard
    simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19727 (pattern : Twelve) (guard : d1 pattern = 1) : d4 pattern ≤ (16 : Int) + d19 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19725 pattern childGuard
    simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19726 pattern childGuard
    simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19728 (pattern : Twelve) (guard : d1 pattern = 1) : d1248 pattern ≤ (16 : Int) + d19 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19569 pattern childGuard
    simpa only [d1248, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19727 pattern childGuard
    simpa only [d1248, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19729 (pattern : Twelve) (guard : d1 pattern = 1) : d1254 pattern ≤ (16 : Int) + d1294 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1254, d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19728 pattern childGuard
    simpa only [d1254, d1294, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1254, d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19706 pattern childGuard
    simpa only [d1254, d1294, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19730 (pattern : Twelve) (guard : d1 pattern = 1) : d1258 pattern ≤ (16 : Int) + d1345 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1258, d1345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19724 pattern childGuard
    simpa only [d1258, d1345, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1258, d1345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19729 pattern childGuard
    simpa only [d1258, d1345, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19731 (pattern : Twelve) (guard : d1 pattern = 1) : d59 pattern ≤ (16 : Int) + d827 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d59, d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19521 pattern childGuard
    simpa only [d59, d827, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d59, d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19507 pattern childGuard
    simpa only [d59, d827, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19732 (pattern : Twelve) (guard : d1 pattern = 1) : d15 pattern ≤ (16 : Int) + d117 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d15, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19518 pattern childGuard
    simpa only [d15, d117, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d15, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19603 pattern childGuard
    simpa only [d15, d117, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19733 (pattern : Twelve) (guard : d1 pattern = 1) : d24 pattern ≤ (16 : Int) + d119 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d24, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19518 pattern childGuard
    simpa only [d24, d119, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d24, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19732 pattern childGuard
    simpa only [d24, d119, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19734 (pattern : Twelve) (guard : d1 pattern = 1) : d41 pattern ≤ (16 : Int) + d1327 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d41, d1327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19716 pattern childGuard
    simpa only [d41, d1327, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d41, d1327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19733 pattern childGuard
    simpa only [d41, d1327, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19735 (pattern : Twelve) (guard : d1 pattern = 1) : d47 pattern ≤ (16 : Int) + d1280 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d47, d1280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19555 pattern childGuard
    simpa only [d47, d1280, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d47, d1280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19470 pattern childGuard
    simpa only [d47, d1280, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19736 (pattern : Twelve) (guard : d1 pattern = 1) : d836 pattern ≤ (16 : Int) + d1334 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d836, d1334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19734 pattern childGuard
    simpa only [d836, d1334, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d836, d1334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19735 pattern childGuard
    simpa only [d836, d1334, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19737 (pattern : Twelve) (guard : d1 pattern = 1) : d851 pattern ≤ (16 : Int) + d1340 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d851, d1340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19731 pattern childGuard
    simpa only [d851, d1340, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d851, d1340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19736 pattern childGuard
    simpa only [d851, d1340, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19738 (pattern : Twelve) (guard : d1 pattern = 1) : d41 pattern ≤ (16 : Int) + d817 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d41, d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19569 pattern childGuard
    simpa only [d41, d817, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d41, d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19591 pattern childGuard
    simpa only [d41, d817, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19739 (pattern : Twelve) (guard : d1 pattern = 1) : d48 pattern ≤ (16 : Int) + d29 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d48, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19727 pattern childGuard
    simpa only [d48, d29, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d48, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19470 pattern childGuard
    simpa only [d48, d29, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
