/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons147
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c20720 (pattern : Twelve) (guard : d1 pattern = 1) : d79 pattern ≤ (15 : Int) + d842 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d79, d842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20677 pattern childGuard
    simpa only [d79, d842, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d79, d842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20719 pattern childGuard
    simpa only [d79, d842, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20721 (pattern : Twelve) (guard : d1 pattern = 1) : d80 pattern ≤ (15 : Int) + d843 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d80, d843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20689 pattern childGuard
    simpa only [d80, d843, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d80, d843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20701 pattern childGuard
    simpa only [d80, d843, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20722 (pattern : Twelve) (guard : d1 pattern = 1) : d95 pattern ≤ (15 : Int) + d855 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d95, d855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20720 pattern childGuard
    simpa only [d95, d855, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d95, d855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20721 pattern childGuard
    simpa only [d95, d855, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20723 (pattern : Twelve) (guard : d1 pattern = 1) : d59 pattern ≤ (15 : Int) + d59 pattern := by
  omega
theorem c20724 (pattern : Twelve) (guard : d1 pattern = 1) : d4 pattern ≤ (15 : Int) + d4 pattern := by
  omega
theorem c20725 (pattern : Twelve) (guard : d1 pattern = 1) : d4 pattern ≤ (15 : Int) + d5 pattern := by
  change (4 : Int) ≤ (15 : Int) + 5
  decide
theorem c20726 (pattern : Twelve) (guard : d1 pattern = 1) : d4 pattern ≤ (15 : Int) + d15 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20724 pattern childGuard
    simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20725 pattern childGuard
    simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20727 (pattern : Twelve) (guard : d1 pattern = 1) : d4 pattern ≤ (15 : Int) + d24 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20724 pattern childGuard
    simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20726 pattern childGuard
    simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20728 (pattern : Twelve) (guard : d1 pattern = 1) : d38 pattern ≤ (15 : Int) + d41 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d38, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20688 pattern childGuard
    simpa only [d38, d41, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d38, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20727 pattern childGuard
    simpa only [d38, d41, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20729 (pattern : Twelve) (guard : d1 pattern = 1) : d9 pattern ≤ (15 : Int) + d3 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20664 pattern childGuard
    simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20717 pattern childGuard
    simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20730 (pattern : Twelve) (guard : d1 pattern = 1) : d23 pattern ≤ (15 : Int) + d815 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, d815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20687 pattern childGuard
    simpa only [d23, d815, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, d815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20729 pattern childGuard
    simpa only [d23, d815, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20731 (pattern : Twelve) (guard : d1 pattern = 1) : d40 pattern ≤ (15 : Int) + d820 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d40, d820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20730 pattern childGuard
    simpa only [d40, d820, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d40, d820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20672 pattern childGuard
    simpa only [d40, d820, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20732 (pattern : Twelve) (guard : d1 pattern = 1) : d60 pattern ≤ (15 : Int) + d829 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d60, d829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20728 pattern childGuard
    simpa only [d60, d829, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d60, d829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20731 pattern childGuard
    simpa only [d60, d829, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20733 (pattern : Twelve) (guard : d1 pattern = 1) : d81 pattern ≤ (15 : Int) + d844 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d81, d844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20723 pattern childGuard
    simpa only [d81, d844, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d81, d844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20732 pattern childGuard
    simpa only [d81, d844, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20734 (pattern : Twelve) (guard : d1 pattern = 1) : d39 pattern ≤ (15 : Int) + d40 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d39, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20688 pattern childGuard
    simpa only [d39, d40, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d39, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20672 pattern childGuard
    simpa only [d39, d40, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20735 (pattern : Twelve) (guard : d1 pattern = 1) : d59 pattern ≤ (15 : Int) + d830 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d59, d830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20728 pattern childGuard
    simpa only [d59, d830, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d59, d830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20734 pattern childGuard
    simpa only [d59, d830, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20736 (pattern : Twelve) (guard : d1 pattern = 1) : d4 pattern ≤ (15 : Int) + d13 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20724 pattern childGuard
    simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20681 pattern childGuard
    simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20737 (pattern : Twelve) (guard : d1 pattern = 1) : d15 pattern ≤ (15 : Int) + d14 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d15, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20725 pattern childGuard
    simpa only [d15, d14, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d15, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20679 pattern childGuard
    simpa only [d15, d14, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20738 (pattern : Twelve) (guard : d1 pattern = 1) : d24 pattern ≤ (15 : Int) + d21 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d24, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20736 pattern childGuard
    simpa only [d24, d21, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d24, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20737 pattern childGuard
    simpa only [d24, d21, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20739 (pattern : Twelve) (guard : d1 pattern = 1) : d41 pattern ≤ (15 : Int) + d821 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d41, d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20699 pattern childGuard
    simpa only [d41, d821, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d41, d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20738 pattern childGuard
    simpa only [d41, d821, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20740 (pattern : Twelve) (guard : d1 pattern = 1) : d16 pattern ≤ (15 : Int) + d13 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d16, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20662 pattern childGuard
    simpa only [d16, d13, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d16, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20681 pattern childGuard
    simpa only [d16, d13, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20741 (pattern : Twelve) (guard : d1 pattern = 1) : d12 pattern ≤ (15 : Int) + d14 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d12, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20665 pattern childGuard
    simpa only [d12, d14, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d12, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20679 pattern childGuard
    simpa only [d12, d14, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20742 (pattern : Twelve) (guard : d1 pattern = 1) : d25 pattern ≤ (15 : Int) + d21 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d25, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20740 pattern childGuard
    simpa only [d25, d21, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d25, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20741 pattern childGuard
    simpa only [d25, d21, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20743 (pattern : Twelve) (guard : d1 pattern = 1) : d42 pattern ≤ (15 : Int) + d822 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d42, d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20742 pattern childGuard
    simpa only [d42, d822, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d42, d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20672 pattern childGuard
    simpa only [d42, d822, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20744 (pattern : Twelve) (guard : d1 pattern = 1) : d61 pattern ≤ (15 : Int) + d831 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d61, d831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20739 pattern childGuard
    simpa only [d61, d831, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d61, d831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20743 pattern childGuard
    simpa only [d61, d831, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20745 (pattern : Twelve) (guard : d1 pattern = 1) : d82 pattern ≤ (15 : Int) + d845 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d82, d845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20735 pattern childGuard
    simpa only [d82, d845, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d82, d845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20744 pattern childGuard
    simpa only [d82, d845, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20746 (pattern : Twelve) (guard : d1 pattern = 1) : d96 pattern ≤ (15 : Int) + d856 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d96, d856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20733 pattern childGuard
    simpa only [d96, d856, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d96, d856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20745 pattern childGuard
    simpa only [d96, d856, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20747 (pattern : Twelve) (guard : d1 pattern = 1) : d104 pattern ≤ (15 : Int) + d862 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d104, d862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20722 pattern childGuard
    simpa only [d104, d862, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d104, d862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20746 pattern childGuard
    simpa only [d104, d862, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20748 (pattern : Twelve) (guard : d1 pattern = 1) : d105 pattern ≤ (15 : Int) + d863 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d105, d863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20714 pattern childGuard
    simpa only [d105, d863, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d105, d863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20672 pattern childGuard
    simpa only [d105, d863, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20749 (pattern : Twelve) (guard : d1 pattern = 1) : d111 pattern ≤ (15 : Int) + d867 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d111, d867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20747 pattern childGuard
    simpa only [d111, d867, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d111, d867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20748 pattern childGuard
    simpa only [d111, d867, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20750 (pattern : Twelve) (guard : d1 pattern = 1) : d114 pattern ≤ (15 : Int) + d869 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d114, d869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20716 pattern childGuard
    simpa only [d114, d869, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d114, d869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20749 pattern childGuard
    simpa only [d114, d869, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20751 (pattern : Twelve) (guard : d1 pattern = 1) : d30 pattern ≤ (15 : Int) + d823 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d30, d823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20648 pattern childGuard
    simpa only [d30, d823, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d30, d823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20686 pattern childGuard
    simpa only [d30, d823, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20752 (pattern : Twelve) (guard : d1 pattern = 1) : d80 pattern ≤ (15 : Int) + d846 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d80, d846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20751 pattern childGuard
    simpa only [d80, d846, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d80, d846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20701 pattern childGuard
    simpa only [d80, d846, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20753 (pattern : Twelve) (guard : d1 pattern = 1) : d97 pattern ≤ (15 : Int) + d857 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d97, d857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20655 pattern childGuard
    simpa only [d97, d857, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d97, d857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20752 pattern childGuard
    simpa only [d97, d857, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20754 (pattern : Twelve) (guard : d1 pattern = 1) : d43 pattern ≤ (15 : Int) + d45 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d43, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20649 pattern childGuard
    simpa only [d43, d45, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d43, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20691 pattern childGuard
    simpa only [d43, d45, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20755 (pattern : Twelve) (guard : d1 pattern = 1) : d62 pattern ≤ (15 : Int) + d832 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d62, d832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20689 pattern childGuard
    simpa only [d62, d832, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d62, d832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20754 pattern childGuard
    simpa only [d62, d832, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20756 (pattern : Twelve) (guard : d1 pattern = 1) : d83 pattern ≤ (15 : Int) + d847 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d83, d847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20685 pattern childGuard
    simpa only [d83, d847, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d83, d847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20755 pattern childGuard
    simpa only [d83, d847, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20757 (pattern : Twelve) (guard : d1 pattern = 1) : d44 pattern ≤ (15 : Int) + d39 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d44, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20686 pattern childGuard
    simpa only [d44, d39, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d44, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20695 pattern childGuard
    simpa only [d44, d39, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20758 (pattern : Twelve) (guard : d1 pattern = 1) : d63 pattern ≤ (15 : Int) + d833 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d63, d833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20689 pattern childGuard
    simpa only [d63, d833, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d63, d833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20757 pattern childGuard
    simpa only [d63, d833, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20759 (pattern : Twelve) (guard : d1 pattern = 1) : d40 pattern ≤ (15 : Int) + d42 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d40, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20699 pattern childGuard
    simpa only [d40, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d40, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20672 pattern childGuard
    simpa only [d40, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20760 (pattern : Twelve) (guard : d1 pattern = 1) : d64 pattern ≤ (15 : Int) + d825 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d64, d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20700 pattern childGuard
    simpa only [d64, d825, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d64, d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20759 pattern childGuard
    simpa only [d64, d825, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20761 (pattern : Twelve) (guard : d1 pattern = 1) : d84 pattern ≤ (15 : Int) + d848 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d84, d848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20758 pattern childGuard
    simpa only [d84, d848, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d84, d848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20760 pattern childGuard
    simpa only [d84, d848, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20762 (pattern : Twelve) (guard : d1 pattern = 1) : d98 pattern ≤ (15 : Int) + d858 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d98, d858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20756 pattern childGuard
    simpa only [d98, d858, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d98, d858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20761 pattern childGuard
    simpa only [d98, d858, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20763 (pattern : Twelve) (guard : d1 pattern = 1) : d106 pattern ≤ (15 : Int) + d864 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d106, d864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20753 pattern childGuard
    simpa only [d106, d864, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d106, d864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20762 pattern childGuard
    simpa only [d106, d864, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20764 (pattern : Twelve) (guard : d1 pattern = 1) : d45 pattern ≤ (15 : Int) + d45 pattern := by
  omega
theorem c20765 (pattern : Twelve) (guard : d1 pattern = 1) : d65 pattern ≤ (15 : Int) + d832 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d65, d832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20689 pattern childGuard
    simpa only [d65, d832, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d65, d832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20764 pattern childGuard
    simpa only [d65, d832, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20766 (pattern : Twelve) (guard : d1 pattern = 1) : d85 pattern ≤ (15 : Int) + d847 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d85, d847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20707 pattern childGuard
    simpa only [d85, d847, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d85, d847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20765 pattern childGuard
    simpa only [d85, d847, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20767 (pattern : Twelve) (guard : d1 pattern = 1) : d39 pattern ≤ (15 : Int) + d39 pattern := by
  omega
theorem c20768 (pattern : Twelve) (guard : d1 pattern = 1) : d66 pattern ≤ (15 : Int) + d833 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d66, d833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20689 pattern childGuard
    simpa only [d66, d833, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d66, d833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20767 pattern childGuard
    simpa only [d66, d833, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20769 (pattern : Twelve) (guard : d1 pattern = 1) : d86 pattern ≤ (15 : Int) + d848 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d86, d848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20768 pattern childGuard
    simpa only [d86, d848, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d86, d848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20760 pattern childGuard
    simpa only [d86, d848, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20770 (pattern : Twelve) (guard : d1 pattern = 1) : d99 pattern ≤ (15 : Int) + d858 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d99, d858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20766 pattern childGuard
    simpa only [d99, d858, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d99, d858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20769 pattern childGuard
    simpa only [d99, d858, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20771 (pattern : Twelve) (guard : d1 pattern = 1) : d107 pattern ≤ (15 : Int) + d864 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d107, d864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20753 pattern childGuard
    simpa only [d107, d864, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d107, d864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20770 pattern childGuard
    simpa only [d107, d864, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20772 (pattern : Twelve) (guard : d1 pattern = 1) : d112 pattern ≤ (15 : Int) + d864 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20763 pattern childGuard
    simpa only [d112, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20771 pattern childGuard
    simpa only [d112, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20773 (pattern : Twelve) (guard : d1 pattern = 1) : d46 pattern ≤ (15 : Int) + d46 pattern := by
  omega
theorem c20774 (pattern : Twelve) (guard : d1 pattern = 1) : d67 pattern ≤ (15 : Int) + d834 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d67, d834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20689 pattern childGuard
    simpa only [d67, d834, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d67, d834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20773 pattern childGuard
    simpa only [d67, d834, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20775 (pattern : Twelve) (guard : d1 pattern = 1) : d87 pattern ≤ (15 : Int) + d849 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d87, d849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20677 pattern childGuard
    simpa only [d87, d849, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d87, d849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20774 pattern childGuard
    simpa only [d87, d849, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20776 (pattern : Twelve) (guard : d1 pattern = 1) : d38 pattern ≤ (15 : Int) + d38 pattern := by
  omega
theorem c20777 (pattern : Twelve) (guard : d1 pattern = 1) : d68 pattern ≤ (15 : Int) + d835 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d68, d835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20689 pattern childGuard
    simpa only [d68, d835, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d68, d835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20776 pattern childGuard
    simpa only [d68, d835, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20778 (pattern : Twelve) (guard : d1 pattern = 1) : d88 pattern ≤ (15 : Int) + d850 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d88, d850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20777 pattern childGuard
    simpa only [d88, d850, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d88, d850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20760 pattern childGuard
    simpa only [d88, d850, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20779 (pattern : Twelve) (guard : d1 pattern = 1) : d100 pattern ≤ (15 : Int) + d859 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d100, d859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20775 pattern childGuard
    simpa only [d100, d859, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d100, d859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20778 pattern childGuard
    simpa only [d100, d859, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20780 (pattern : Twelve) (guard : d1 pattern = 1) : d47 pattern ≤ (15 : Int) + d47 pattern := by
  omega
theorem c20781 (pattern : Twelve) (guard : d1 pattern = 1) : d69 pattern ≤ (15 : Int) + d836 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d69, d836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20728 pattern childGuard
    simpa only [d69, d836, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d69, d836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20780 pattern childGuard
    simpa only [d69, d836, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20782 (pattern : Twelve) (guard : d1 pattern = 1) : d89 pattern ≤ (15 : Int) + d851 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d89, d851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20723 pattern childGuard
    simpa only [d89, d851, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d89, d851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20781 pattern childGuard
    simpa only [d89, d851, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20783 (pattern : Twelve) (guard : d1 pattern = 1) : d48 pattern ≤ (15 : Int) + d48 pattern := by
  omega
theorem c20784 (pattern : Twelve) (guard : d1 pattern = 1) : d70 pattern ≤ (15 : Int) + d837 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d70, d837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20728 pattern childGuard
    simpa only [d70, d837, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d70, d837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20783 pattern childGuard
    simpa only [d70, d837, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20785 (pattern : Twelve) (guard : d1 pattern = 1) : d49 pattern ≤ (15 : Int) + d822 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d49, d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20738 pattern childGuard
    simpa only [d49, d822, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d49, d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20672 pattern childGuard
    simpa only [d49, d822, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20786 (pattern : Twelve) (guard : d1 pattern = 1) : d71 pattern ≤ (15 : Int) + d831 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d71, d831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20739 pattern childGuard
    simpa only [d71, d831, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d71, d831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20785 pattern childGuard
    simpa only [d71, d831, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20787 (pattern : Twelve) (guard : d1 pattern = 1) : d90 pattern ≤ (15 : Int) + d852 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d90, d852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20784 pattern childGuard
    simpa only [d90, d852, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d90, d852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20786 pattern childGuard
    simpa only [d90, d852, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20788 (pattern : Twelve) (guard : d1 pattern = 1) : d101 pattern ≤ (15 : Int) + d860 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d101, d860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20782 pattern childGuard
    simpa only [d101, d860, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d101, d860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20787 pattern childGuard
    simpa only [d101, d860, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20789 (pattern : Twelve) (guard : d1 pattern = 1) : d108 pattern ≤ (15 : Int) + d865 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d108, d865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20779 pattern childGuard
    simpa only [d108, d865, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d108, d865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20788 pattern childGuard
    simpa only [d108, d865, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20790 (pattern : Twelve) (guard : d1 pattern = 1) : d109 pattern ≤ (15 : Int) + d866 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d109, d866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20770 pattern childGuard
    simpa only [d109, d866, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d109, d866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20672 pattern childGuard
    simpa only [d109, d866, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20791 (pattern : Twelve) (guard : d1 pattern = 1) : d113 pattern ≤ (15 : Int) + d868 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d113, d868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20789 pattern childGuard
    simpa only [d113, d868, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d113, d868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20790 pattern childGuard
    simpa only [d113, d868, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20792 (pattern : Twelve) (guard : d1 pattern = 1) : d115 pattern ≤ (15 : Int) + d870 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d115, d870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20772 pattern childGuard
    simpa only [d115, d870, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d115, d870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20791 pattern childGuard
    simpa only [d115, d870, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20793 (pattern : Twelve) (guard : d1 pattern = 1) : d116 pattern ≤ (15 : Int) + d871 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d116, d871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20750 pattern childGuard
    simpa only [d116, d871, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d116, d871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20792 pattern childGuard
    simpa only [d116, d871, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20794 (pattern : Twelve) (guard : d1 pattern = 1) : d7 pattern ≤ (15 : Int) + d8 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20646 pattern childGuard
    simpa only [d7, d8, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20661 pattern childGuard
    simpa only [d7, d8, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20795 (pattern : Twelve) (guard : d1 pattern = 1) : d17 pattern ≤ (15 : Int) + d1275 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, d1275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20647 pattern childGuard
    simpa only [d17, d1275, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, d1275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20794 pattern childGuard
    simpa only [d17, d1275, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20796 (pattern : Twelve) (guard : d1 pattern = 1) : d1 pattern ≤ (15 : Int) + d8 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20649 pattern childGuard
    simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20661 pattern childGuard
    simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20797 (pattern : Twelve) (guard : d1 pattern = 1) : d1 pattern ≤ (15 : Int) + d872 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20649 pattern childGuard
    simpa only [d872, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20796 pattern childGuard
    simpa only [d872, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20798 (pattern : Twelve) (guard : d1 pattern = 1) : d27 pattern ≤ (15 : Int) + d1278 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d27, d1278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20795 pattern childGuard
    simpa only [d27, d1278, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d27, d1278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20797 pattern childGuard
    simpa only [d27, d1278, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20799 (pattern : Twelve) (guard : d1 pattern = 1) : d814 pattern ≤ (15 : Int) + d872 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d814, d872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20651 pattern childGuard
    simpa only [d814, d872, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d814, d872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20796 pattern childGuard
    simpa only [d814, d872, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20800 (pattern : Twelve) (guard : d1 pattern = 1) : d816 pattern ≤ (15 : Int) + d872 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20799 pattern childGuard
    simpa only [d816, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20797 pattern childGuard
    simpa only [d816, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20801 (pattern : Twelve) (guard : d1 pattern = 1) : d824 pattern ≤ (15 : Int) + d1284 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d824, d1284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20798 pattern childGuard
    simpa only [d824, d1284, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d824, d1284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20800 pattern childGuard
    simpa only [d824, d1284, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20802 (pattern : Twelve) (guard : d1 pattern = 1) : d838 pattern ≤ (15 : Int) + d1293 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d838, d1293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20648 pattern childGuard
    simpa only [d838, d1293, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d838, d1293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20801 pattern childGuard
    simpa only [d838, d1293, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20803 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (15 : Int) + d6 pattern := by
  change (0 : Int) ≤ (15 : Int) + 6
  decide
theorem c20804 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (15 : Int) + d6 pattern := by
  change (2 : Int) ≤ (15 : Int) + 6
  decide
theorem c20805 (pattern : Twelve) (guard : d1 pattern = 1) : d10 pattern ≤ (15 : Int) + d6 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20803 pattern childGuard
    simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20804 pattern childGuard
    simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20806 (pattern : Twelve) (guard : d1 pattern = 1) : d1 pattern ≤ (15 : Int) + d6 pattern := by
  change (1 : Int) ≤ (15 : Int) + 6
  decide
theorem c20807 (pattern : Twelve) (guard : d1 pattern = 1) : d11 pattern ≤ (15 : Int) + d6 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20806 pattern childGuard
    simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20678 pattern childGuard
    simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20808 (pattern : Twelve) (guard : d1 pattern = 1) : d19 pattern ≤ (15 : Int) + d6 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20805 pattern childGuard
    simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20807 pattern childGuard
    simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20809 (pattern : Twelve) (guard : d1 pattern = 1) : d16 pattern ≤ (15 : Int) + d6 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20804 pattern childGuard
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20681 pattern childGuard
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20810 (pattern : Twelve) (guard : d1 pattern = 1) : d25 pattern ≤ (15 : Int) + d6 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20809 pattern childGuard
    simpa only [d25, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20680 pattern childGuard
    simpa only [d25, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20811 (pattern : Twelve) (guard : d1 pattern = 1) : d817 pattern ≤ (15 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20808 pattern childGuard
    simpa only [d817, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20810 pattern childGuard
    simpa only [d817, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20812 (pattern : Twelve) (guard : d1 pattern = 1) : d42 pattern ≤ (15 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20810 pattern childGuard
    simpa only [d42, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20672 pattern childGuard
    simpa only [d42, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20813 (pattern : Twelve) (guard : d1 pattern = 1) : d825 pattern ≤ (15 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20811 pattern childGuard
    simpa only [d825, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20812 pattern childGuard
    simpa only [d825, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20814 (pattern : Twelve) (guard : d1 pattern = 1) : d839 pattern ≤ (15 : Int) + d1294 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d839, d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20660 pattern childGuard
    simpa only [d839, d1294, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d839, d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20813 pattern childGuard
    simpa only [d839, d1294, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20815 (pattern : Twelve) (guard : d1 pattern = 1) : d853 pattern ≤ (15 : Int) + d1305 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d853, d1305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20802 pattern childGuard
    simpa only [d853, d1305, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d853, d1305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20814 pattern childGuard
    simpa only [d853, d1305, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20816 (pattern : Twelve) (guard : d1 pattern = 1) : d3 pattern ≤ (15 : Int) + d4 pattern := by
  change (3 : Int) ≤ (15 : Int) + 4
  decide
theorem c20817 (pattern : Twelve) (guard : d1 pattern = 1) : d9 pattern ≤ (15 : Int) + d117 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20664 pattern childGuard
    simpa only [d9, d117, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20816 pattern childGuard
    simpa only [d9, d117, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20818 (pattern : Twelve) (guard : d1 pattern = 1) : d23 pattern ≤ (15 : Int) + d1276 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, d1276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20687 pattern childGuard
    simpa only [d23, d1276, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, d1276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20817 pattern childGuard
    simpa only [d23, d1276, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20819 (pattern : Twelve) (guard : d1 pattern = 1) : d34 pattern ≤ (15 : Int) + d1279 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d34, d1279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20795 pattern childGuard
    simpa only [d34, d1279, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d34, d1279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20818 pattern childGuard
    simpa only [d34, d1279, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20820 (pattern : Twelve) (guard : d1 pattern = 1) : d818 pattern ≤ (15 : Int) + d1280 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d818, d1280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20799 pattern childGuard
    simpa only [d818, d1280, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d818, d1280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20672 pattern childGuard
    simpa only [d818, d1280, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20821 (pattern : Twelve) (guard : d1 pattern = 1) : d826 pattern ≤ (15 : Int) + d1285 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d826, d1285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20819 pattern childGuard
    simpa only [d826, d1285, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d826, d1285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20820 pattern childGuard
    simpa only [d826, d1285, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20822 (pattern : Twelve) (guard : d1 pattern = 1) : d840 pattern ≤ (15 : Int) + d1295 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d840, d1295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20712 pattern childGuard
    simpa only [d840, d1295, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d840, d1295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20821 pattern childGuard
    simpa only [d840, d1295, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20823 (pattern : Twelve) (guard : d1 pattern = 1) : d36 pattern ≤ (15 : Int) + d29 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d36, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20660 pattern childGuard
    simpa only [d36, d29, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d36, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20672 pattern childGuard
    simpa only [d36, d29, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20824 (pattern : Twelve) (guard : d1 pattern = 1) : d827 pattern ≤ (15 : Int) + d1286 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d827, d1286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20700 pattern childGuard
    simpa only [d827, d1286, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d827, d1286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20823 pattern childGuard
    simpa only [d827, d1286, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20825 (pattern : Twelve) (guard : d1 pattern = 1) : d841 pattern ≤ (15 : Int) + d1296 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d841, d1296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20824 pattern childGuard
    simpa only [d841, d1296, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d841, d1296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20813 pattern childGuard
    simpa only [d841, d1296, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20826 (pattern : Twelve) (guard : d1 pattern = 1) : d854 pattern ≤ (15 : Int) + d1306 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d854, d1306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20822 pattern childGuard
    simpa only [d854, d1306, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d854, d1306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20825 pattern childGuard
    simpa only [d854, d1306, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20827 (pattern : Twelve) (guard : d1 pattern = 1) : d861 pattern ≤ (15 : Int) + d1313 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d861, d1313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20815 pattern childGuard
    simpa only [d861, d1313, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d861, d1313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20826 pattern childGuard
    simpa only [d861, d1313, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20828 (pattern : Twelve) (guard : d1 pattern = 1) : d3 pattern ≤ (15 : Int) + d117 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20717 pattern childGuard
    simpa only [d117, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20816 pattern childGuard
    simpa only [d117, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20829 (pattern : Twelve) (guard : d1 pattern = 1) : d3 pattern ≤ (15 : Int) + d119 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20717 pattern childGuard
    simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20828 pattern childGuard
    simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20830 (pattern : Twelve) (guard : d1 pattern = 1) : d819 pattern ≤ (15 : Int) + d1281 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d819, d1281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20799 pattern childGuard
    simpa only [d819, d1281, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d819, d1281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20829 pattern childGuard
    simpa only [d819, d1281, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20831 (pattern : Twelve) (guard : d1 pattern = 1) : d828 pattern ≤ (15 : Int) + d1287 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d828, d1287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20819 pattern childGuard
    simpa only [d828, d1287, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d828, d1287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20830 pattern childGuard
    simpa only [d828, d1287, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20832 (pattern : Twelve) (guard : d1 pattern = 1) : d842 pattern ≤ (15 : Int) + d1297 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d842, d1297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20689 pattern childGuard
    simpa only [d842, d1297, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d842, d1297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20831 pattern childGuard
    simpa only [d842, d1297, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20833 (pattern : Twelve) (guard : d1 pattern = 1) : d843 pattern ≤ (15 : Int) + d1298 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d843, d1298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20700 pattern childGuard
    simpa only [d843, d1298, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d843, d1298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20813 pattern childGuard
    simpa only [d843, d1298, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20834 (pattern : Twelve) (guard : d1 pattern = 1) : d855 pattern ≤ (15 : Int) + d1307 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d855, d1307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20832 pattern childGuard
    simpa only [d855, d1307, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d855, d1307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20833 pattern childGuard
    simpa only [d855, d1307, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20835 (pattern : Twelve) (guard : d1 pattern = 1) : d24 pattern ≤ (15 : Int) + d1277 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d24, d1277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20726 pattern childGuard
    simpa only [d24, d1277, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d24, d1277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20737 pattern childGuard
    simpa only [d24, d1277, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20836 (pattern : Twelve) (guard : d1 pattern = 1) : d41 pattern ≤ (15 : Int) + d1282 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d41, d1282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20818 pattern childGuard
    simpa only [d41, d1282, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d41, d1282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20835 pattern childGuard
    simpa only [d41, d1282, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20837 (pattern : Twelve) (guard : d1 pattern = 1) : d815 pattern ≤ (15 : Int) + d119 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d815, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20729 pattern childGuard
    simpa only [d815, d119, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d815, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20828 pattern childGuard
    simpa only [d815, d119, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20838 (pattern : Twelve) (guard : d1 pattern = 1) : d820 pattern ≤ (15 : Int) + d125 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d820, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20837 pattern childGuard
    simpa only [d820, d125, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d820, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20672 pattern childGuard
    simpa only [d820, d125, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20839 (pattern : Twelve) (guard : d1 pattern = 1) : d829 pattern ≤ (15 : Int) + d1288 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d829, d1288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20836 pattern childGuard
    simpa only [d829, d1288, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d829, d1288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20838 pattern childGuard
    simpa only [d829, d1288, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20840 (pattern : Twelve) (guard : d1 pattern = 1) : d844 pattern ≤ (15 : Int) + d1299 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d844, d1299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20735 pattern childGuard
    simpa only [d844, d1299, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d844, d1299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20839 pattern childGuard
    simpa only [d844, d1299, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20841 (pattern : Twelve) (guard : d1 pattern = 1) : d830 pattern ≤ (15 : Int) + d1289 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d830, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20739 pattern childGuard
    simpa only [d830, d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d830, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20759 pattern childGuard
    simpa only [d830, d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20842 (pattern : Twelve) (guard : d1 pattern = 1) : d821 pattern ≤ (15 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20810 pattern childGuard
    simpa only [d821, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20691 pattern childGuard
    simpa only [d821, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20843 (pattern : Twelve) (guard : d1 pattern = 1) : d822 pattern ≤ (15 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20691 pattern childGuard
    simpa only [d822, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20672 pattern childGuard
    simpa only [d822, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20844 (pattern : Twelve) (guard : d1 pattern = 1) : d831 pattern ≤ (15 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20842 pattern childGuard
    simpa only [d831, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20843 pattern childGuard
    simpa only [d831, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20845 (pattern : Twelve) (guard : d1 pattern = 1) : d845 pattern ≤ (15 : Int) + d1300 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d845, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20841 pattern childGuard
    simpa only [d845, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d845, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20844 pattern childGuard
    simpa only [d845, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20846 (pattern : Twelve) (guard : d1 pattern = 1) : d856 pattern ≤ (15 : Int) + d1308 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d856, d1308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20840 pattern childGuard
    simpa only [d856, d1308, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d856, d1308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20845 pattern childGuard
    simpa only [d856, d1308, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20847 (pattern : Twelve) (guard : d1 pattern = 1) : d862 pattern ≤ (15 : Int) + d1314 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d862, d1314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20834 pattern childGuard
    simpa only [d862, d1314, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d862, d1314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20846 pattern childGuard
    simpa only [d862, d1314, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20848 (pattern : Twelve) (guard : d1 pattern = 1) : d863 pattern ≤ (15 : Int) + d1315 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d863, d1315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20826 pattern childGuard
    simpa only [d863, d1315, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d863, d1315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20672 pattern childGuard
    simpa only [d863, d1315, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20849 (pattern : Twelve) (guard : d1 pattern = 1) : d867 pattern ≤ (15 : Int) + d1319 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d867, d1319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20847 pattern childGuard
    simpa only [d867, d1319, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d867, d1319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20848 pattern childGuard
    simpa only [d867, d1319, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20850 (pattern : Twelve) (guard : d1 pattern = 1) : d869 pattern ≤ (15 : Int) + d1321 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d869, d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20827 pattern childGuard
    simpa only [d869, d1321, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d869, d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20849 pattern childGuard
    simpa only [d869, d1321, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20851 (pattern : Twelve) (guard : d1 pattern = 1) : d823 pattern ≤ (15 : Int) + d1283 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d823, d1283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20660 pattern childGuard
    simpa only [d823, d1283, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d823, d1283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20688 pattern childGuard
    simpa only [d823, d1283, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20852 (pattern : Twelve) (guard : d1 pattern = 1) : d846 pattern ≤ (15 : Int) + d1301 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d846, d1301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20851 pattern childGuard
    simpa only [d846, d1301, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d846, d1301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20813 pattern childGuard
    simpa only [d846, d1301, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20853 (pattern : Twelve) (guard : d1 pattern = 1) : d857 pattern ≤ (15 : Int) + d1309 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d857, d1309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20802 pattern childGuard
    simpa only [d857, d1309, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d857, d1309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20852 pattern childGuard
    simpa only [d857, d1309, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20854 (pattern : Twelve) (guard : d1 pattern = 1) : d45 pattern ≤ (15 : Int) + d1280 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d45, d1280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20797 pattern childGuard
    simpa only [d45, d1280, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d45, d1280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20672 pattern childGuard
    simpa only [d45, d1280, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20855 (pattern : Twelve) (guard : d1 pattern = 1) : d832 pattern ≤ (15 : Int) + d1285 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d832, d1285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20819 pattern childGuard
    simpa only [d832, d1285, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d832, d1285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20854 pattern childGuard
    simpa only [d832, d1285, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20856 (pattern : Twelve) (guard : d1 pattern = 1) : d847 pattern ≤ (15 : Int) + d1295 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d847, d1295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20712 pattern childGuard
    simpa only [d847, d1295, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d847, d1295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20855 pattern childGuard
    simpa only [d847, d1295, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20857 (pattern : Twelve) (guard : d1 pattern = 1) : d833 pattern ≤ (15 : Int) + d1290 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d833, d1290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20700 pattern childGuard
    simpa only [d833, d1290, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d833, d1290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20734 pattern childGuard
    simpa only [d833, d1290, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20858 (pattern : Twelve) (guard : d1 pattern = 1) : d848 pattern ≤ (15 : Int) + d1302 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d848, d1302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20857 pattern childGuard
    simpa only [d848, d1302, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d848, d1302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20813 pattern childGuard
    simpa only [d848, d1302, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20859 (pattern : Twelve) (guard : d1 pattern = 1) : d858 pattern ≤ (15 : Int) + d1310 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d858, d1310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20856 pattern childGuard
    simpa only [d858, d1310, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d858, d1310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20858 pattern childGuard
    simpa only [d858, d1310, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
