/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons039
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c5600 (pattern : Twelve) (guard : d1848 pattern = 1) : d1045 pattern ≤ (0 : Int) + d845 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1045, d845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5374 pattern childGuard
    simpa only [d1045, d845, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1045, d845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5599 pattern childGuard
    simpa only [d1045, d845, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5601 (pattern : Twelve) (guard : d1848 pattern = 1) : d1052 pattern ≤ (0 : Int) + d856 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1052, d856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5598 pattern childGuard
    simpa only [d1052, d856, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1052, d856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5600 pattern childGuard
    simpa only [d1052, d856, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5602 (pattern : Twelve) (guard : d1848 pattern = 1) : d1056 pattern ≤ (0 : Int) + d862 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1056, d862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5595 pattern childGuard
    simpa only [d1056, d862, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1056, d862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5601 pattern childGuard
    simpa only [d1056, d862, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5603 (pattern : Twelve) (guard : d1848 pattern = 1) : d1057 pattern ≤ (0 : Int) + d863 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1057, d863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5588 pattern childGuard
    simpa only [d1057, d863, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1057, d863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4269 pattern childGuard
    simpa only [d1057, d863, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5604 (pattern : Twelve) (guard : d1848 pattern = 1) : d1061 pattern ≤ (0 : Int) + d867 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1061, d867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5602 pattern childGuard
    simpa only [d1061, d867, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1061, d867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5603 pattern childGuard
    simpa only [d1061, d867, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5605 (pattern : Twelve) (guard : d1848 pattern = 1) : d1064 pattern ≤ (0 : Int) + d869 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1064, d869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5590 pattern childGuard
    simpa only [d1064, d869, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1064, d869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5604 pattern childGuard
    simpa only [d1064, d869, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5606 (pattern : Twelve) (guard : d1848 pattern = 1) : d1042 pattern ≤ (0 : Int) + d838 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1042, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5045 pattern childGuard
    simpa only [d1042, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1042, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5583 pattern childGuard
    simpa only [d1042, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5607 (pattern : Twelve) (guard : d1848 pattern = 1) : d1050 pattern ≤ (0 : Int) + d853 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1050, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5606 pattern childGuard
    simpa only [d1050, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1050, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5585 pattern childGuard
    simpa only [d1050, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5608 (pattern : Twelve) (guard : d1848 pattern = 1) : d1050 pattern ≤ (0 : Int) + d861 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5607 pattern childGuard
    simpa only [d861, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5588 pattern childGuard
    simpa only [d861, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5609 (pattern : Twelve) (guard : d1848 pattern = 1) : d1042 pattern ≤ (0 : Int) + d842 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1042, d842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5006 pattern childGuard
    simpa only [d1042, d842, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1042, d842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5592 pattern childGuard
    simpa only [d1042, d842, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5610 (pattern : Twelve) (guard : d1848 pattern = 1) : d1050 pattern ≤ (0 : Int) + d855 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1050, d855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5609 pattern childGuard
    simpa only [d1050, d855, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1050, d855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5594 pattern childGuard
    simpa only [d1050, d855, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5611 (pattern : Twelve) (guard : d1848 pattern = 1) : d1058 pattern ≤ (0 : Int) + d862 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1058, d862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5610 pattern childGuard
    simpa only [d1058, d862, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1058, d862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5601 pattern childGuard
    simpa only [d1058, d862, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5612 (pattern : Twelve) (guard : d1848 pattern = 1) : d1062 pattern ≤ (0 : Int) + d867 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1062, d867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5611 pattern childGuard
    simpa only [d1062, d867, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1062, d867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5603 pattern childGuard
    simpa only [d1062, d867, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5613 (pattern : Twelve) (guard : d1848 pattern = 1) : d1065 pattern ≤ (0 : Int) + d869 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1065, d869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5608 pattern childGuard
    simpa only [d1065, d869, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1065, d869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5612 pattern childGuard
    simpa only [d1065, d869, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5614 (pattern : Twelve) (guard : d1848 pattern = 1) : d1067 pattern ≤ (0 : Int) + d869 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1067, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5605 pattern childGuard
    simpa only [d1067, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1067, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5613 pattern childGuard
    simpa only [d1067, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5615 (pattern : Twelve) (guard : d1848 pattern = 1) : d1068 pattern ≤ (0 : Int) + d869 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5614 pattern childGuard
    simpa only [d1068, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5613 pattern childGuard
    simpa only [d1068, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5616 (pattern : Twelve) (guard : d1848 pattern = 1) : d36 pattern ≤ (0 : Int) + d874 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d36, d874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c240 pattern childGuard
    simpa only [d1848, d36, d874, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d36, d874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1043 pattern childGuard
    simpa only [d1848, d36, d874, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5617 (pattern : Twelve) (guard : d1848 pattern = 1) : d818 pattern ≤ (0 : Int) + d875 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d818, d875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4215 pattern childGuard
    simpa only [d1848, d818, d875, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d818, d875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1043 pattern childGuard
    simpa only [d1848, d818, d875, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5618 (pattern : Twelve) (guard : d1848 pattern = 1) : d1033 pattern ≤ (0 : Int) + d882 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1033, d882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5616 pattern childGuard
    simpa only [d1033, d882, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1033, d882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5617 pattern childGuard
    simpa only [d1033, d882, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5619 (pattern : Twelve) (guard : d1848 pattern = 1) : d1042 pattern ≤ (0 : Int) + d890 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1042, d890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5045 pattern childGuard
    simpa only [d1042, d890, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1042, d890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5618 pattern childGuard
    simpa only [d1042, d890, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5620 (pattern : Twelve) (guard : d1848 pattern = 1) : d29 pattern ≤ (0 : Int) + d876 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d29, d876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c328 pattern childGuard
    simpa only [d1848, d29, d876, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d29, d876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5122 pattern childGuard
    simpa only [d1848, d29, d876, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5621 (pattern : Twelve) (guard : d1848 pattern = 1) : d1032 pattern ≤ (0 : Int) + d883 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1032, d883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5620 pattern childGuard
    simpa only [d1032, d883, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1032, d883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2806 pattern childGuard
    simpa only [d1032, d883, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5622 (pattern : Twelve) (guard : d1848 pattern = 1) : d1041 pattern ≤ (0 : Int) + d891 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1041, d891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5109 pattern childGuard
    simpa only [d1041, d891, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1041, d891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5621 pattern childGuard
    simpa only [d1041, d891, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5623 (pattern : Twelve) (guard : d1848 pattern = 1) : d1050 pattern ≤ (0 : Int) + d898 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1050, d898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5619 pattern childGuard
    simpa only [d1050, d898, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1050, d898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5622 pattern childGuard
    simpa only [d1050, d898, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5624 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d815 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5625 (pattern : Twelve) (guard : d1848 pattern = 1) : d36 pattern ≤ (0 : Int) + d877 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d36, d877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c240 pattern childGuard
    simpa only [d1848, d36, d877, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d36, d877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5624 pattern childGuard
    simpa only [d1848, d36, d877, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5626 (pattern : Twelve) (guard : d1848 pattern = 1) : d1033 pattern ≤ (0 : Int) + d884 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1033, d884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5625 pattern childGuard
    simpa only [d1033, d884, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1033, d884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5577 pattern childGuard
    simpa only [d1033, d884, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5627 (pattern : Twelve) (guard : d1848 pattern = 1) : d1042 pattern ≤ (0 : Int) + d892 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1042, d892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5271 pattern childGuard
    simpa only [d1042, d892, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1042, d892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5626 pattern childGuard
    simpa only [d1042, d892, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5628 (pattern : Twelve) (guard : d1848 pattern = 1) : d1041 pattern ≤ (0 : Int) + d893 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1041, d893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5355 pattern childGuard
    simpa only [d1041, d893, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1041, d893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5621 pattern childGuard
    simpa only [d1041, d893, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5629 (pattern : Twelve) (guard : d1848 pattern = 1) : d1050 pattern ≤ (0 : Int) + d899 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1050, d899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5627 pattern childGuard
    simpa only [d1050, d899, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1050, d899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5628 pattern childGuard
    simpa only [d1050, d899, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5630 (pattern : Twelve) (guard : d1848 pattern = 1) : d1050 pattern ≤ (0 : Int) + d902 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5623 pattern childGuard
    simpa only [d902, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5629 pattern childGuard
    simpa only [d902, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5631 (pattern : Twelve) (guard : d1848 pattern = 1) : d818 pattern ≤ (0 : Int) + d878 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d818, d878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4215 pattern childGuard
    simpa only [d1848, d818, d878, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d818, d878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5033 pattern childGuard
    simpa only [d1848, d818, d878, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5632 (pattern : Twelve) (guard : d1848 pattern = 1) : d1033 pattern ≤ (0 : Int) + d885 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1033, d885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5625 pattern childGuard
    simpa only [d1033, d885, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1033, d885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5631 pattern childGuard
    simpa only [d1033, d885, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5633 (pattern : Twelve) (guard : d1848 pattern = 1) : d1042 pattern ≤ (0 : Int) + d894 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1042, d894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5006 pattern childGuard
    simpa only [d1042, d894, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1042, d894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5632 pattern childGuard
    simpa only [d1042, d894, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5634 (pattern : Twelve) (guard : d1848 pattern = 1) : d1041 pattern ≤ (0 : Int) + d895 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1041, d895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5394 pattern childGuard
    simpa only [d1041, d895, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1041, d895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5621 pattern childGuard
    simpa only [d1041, d895, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5635 (pattern : Twelve) (guard : d1848 pattern = 1) : d1050 pattern ≤ (0 : Int) + d900 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1050, d900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5633 pattern childGuard
    simpa only [d1050, d900, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1050, d900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5634 pattern childGuard
    simpa only [d1050, d900, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5636 (pattern : Twelve) (guard : d1848 pattern = 1) : d880 pattern ≤ (0 : Int) + d880 pattern := by
  omega
theorem c5637 (pattern : Twelve) (guard : d1848 pattern = 1) : d1036 pattern ≤ (0 : Int) + d887 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1036, d887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5562 pattern childGuard
    simpa only [d1036, d887, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1036, d887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5636 pattern childGuard
    simpa only [d1036, d887, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5638 (pattern : Twelve) (guard : d1848 pattern = 1) : d1046 pattern ≤ (0 : Int) + d896 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1046, d896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5284 pattern childGuard
    simpa only [d1046, d896, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1046, d896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5637 pattern childGuard
    simpa only [d1046, d896, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5639 (pattern : Twelve) (guard : d1848 pattern = 1) : d889 pattern ≤ (0 : Int) + d889 pattern := by
  omega
theorem c5640 (pattern : Twelve) (guard : d1848 pattern = 1) : d1047 pattern ≤ (0 : Int) + d897 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1047, d897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5402 pattern childGuard
    simpa only [d1047, d897, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1047, d897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5639 pattern childGuard
    simpa only [d1047, d897, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5641 (pattern : Twelve) (guard : d1848 pattern = 1) : d1053 pattern ≤ (0 : Int) + d901 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1053, d901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5638 pattern childGuard
    simpa only [d1053, d901, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1053, d901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5640 pattern childGuard
    simpa only [d1053, d901, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5642 (pattern : Twelve) (guard : d1848 pattern = 1) : d1059 pattern ≤ (0 : Int) + d903 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1059, d903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5635 pattern childGuard
    simpa only [d1059, d903, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1059, d903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5641 pattern childGuard
    simpa only [d1059, d903, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5643 (pattern : Twelve) (guard : d1848 pattern = 1) : d1057 pattern ≤ (0 : Int) + d904 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1057, d904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5629 pattern childGuard
    simpa only [d1057, d904, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1057, d904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4269 pattern childGuard
    simpa only [d1057, d904, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5644 (pattern : Twelve) (guard : d1848 pattern = 1) : d1063 pattern ≤ (0 : Int) + d905 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1063, d905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5642 pattern childGuard
    simpa only [d1063, d905, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1063, d905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5643 pattern childGuard
    simpa only [d1063, d905, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5645 (pattern : Twelve) (guard : d1848 pattern = 1) : d1066 pattern ≤ (0 : Int) + d906 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1066, d906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5630 pattern childGuard
    simpa only [d1066, d906, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1066, d906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5644 pattern childGuard
    simpa only [d1066, d906, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5646 (pattern : Twelve) (guard : d1848 pattern = 1) : d1069 pattern ≤ (0 : Int) + d907 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1069, d907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5615 pattern childGuard
    simpa only [d1069, d907, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1069, d907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5645 pattern childGuard
    simpa only [d1069, d907, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5647 (pattern : Twelve) (guard : d1848 pattern = 1) : d1280 pattern ≤ (0 : Int) + d872 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d1280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4265 pattern childGuard
    simpa only [d1848, d1280, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d1280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1043 pattern childGuard
    simpa only [d1848, d1280, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5648 (pattern : Twelve) (guard : d1848 pattern = 1) : d1445 pattern ≤ (0 : Int) + d1284 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1445, d1284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5159 pattern childGuard
    simpa only [d1445, d1284, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1445, d1284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5647 pattern childGuard
    simpa only [d1445, d1284, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5649 (pattern : Twelve) (guard : d1848 pattern = 1) : d1448 pattern ≤ (0 : Int) + d1293 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1448, d1293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5348 pattern childGuard
    simpa only [d1448, d1293, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1448, d1293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5648 pattern childGuard
    simpa only [d1448, d1293, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5650 (pattern : Twelve) (guard : d1848 pattern = 1) : d1449 pattern ≤ (0 : Int) + d1294 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1449, d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5162 pattern childGuard
    simpa only [d1449, d1294, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1449, d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4269 pattern childGuard
    simpa only [d1449, d1294, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5651 (pattern : Twelve) (guard : d1848 pattern = 1) : d1455 pattern ≤ (0 : Int) + d1305 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1455, d1305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5649 pattern childGuard
    simpa only [d1455, d1305, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1455, d1305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5650 pattern childGuard
    simpa only [d1455, d1305, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5652 (pattern : Twelve) (guard : d1848 pattern = 1) : d1280 pattern ≤ (0 : Int) + d1280 pattern := by
  omega
theorem c5653 (pattern : Twelve) (guard : d1848 pattern = 1) : d1445 pattern ≤ (0 : Int) + d1285 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1445, d1285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5167 pattern childGuard
    simpa only [d1445, d1285, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1445, d1285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5652 pattern childGuard
    simpa only [d1445, d1285, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5654 (pattern : Twelve) (guard : d1848 pattern = 1) : d1450 pattern ≤ (0 : Int) + d1295 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1450, d1295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5355 pattern childGuard
    simpa only [d1450, d1295, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1450, d1295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5653 pattern childGuard
    simpa only [d1450, d1295, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5655 (pattern : Twelve) (guard : d1848 pattern = 1) : d1449 pattern ≤ (0 : Int) + d1296 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1449, d1296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5416 pattern childGuard
    simpa only [d1449, d1296, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1449, d1296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4269 pattern childGuard
    simpa only [d1449, d1296, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5656 (pattern : Twelve) (guard : d1848 pattern = 1) : d1456 pattern ≤ (0 : Int) + d1306 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1456, d1306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5654 pattern childGuard
    simpa only [d1456, d1306, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1456, d1306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5655 pattern childGuard
    simpa only [d1456, d1306, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5657 (pattern : Twelve) (guard : d1848 pattern = 1) : d1459 pattern ≤ (0 : Int) + d1313 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1459, d1313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5651 pattern childGuard
    simpa only [d1459, d1313, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1459, d1313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5656 pattern childGuard
    simpa only [d1459, d1313, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5658 (pattern : Twelve) (guard : d1848 pattern = 1) : d1450 pattern ≤ (0 : Int) + d1293 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1450, d1293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5109 pattern childGuard
    simpa only [d1450, d1293, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1450, d1293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5648 pattern childGuard
    simpa only [d1450, d1293, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5659 (pattern : Twelve) (guard : d1848 pattern = 1) : d1456 pattern ≤ (0 : Int) + d1305 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1456, d1305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5658 pattern childGuard
    simpa only [d1456, d1305, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1456, d1305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5650 pattern childGuard
    simpa only [d1456, d1305, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5660 (pattern : Twelve) (guard : d1848 pattern = 1) : d1456 pattern ≤ (0 : Int) + d1313 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5659 pattern childGuard
    simpa only [d1313, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5656 pattern childGuard
    simpa only [d1313, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5661 (pattern : Twelve) (guard : d1848 pattern = 1) : d1463 pattern ≤ (0 : Int) + d1313 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5657 pattern childGuard
    simpa only [d1463, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5660 pattern childGuard
    simpa only [d1463, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5662 (pattern : Twelve) (guard : d1848 pattern = 1) : d1280 pattern ≤ (0 : Int) + d1281 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d1280, d1281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4265 pattern childGuard
    simpa only [d1848, d1280, d1281, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d1280, d1281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5392 pattern childGuard
    simpa only [d1848, d1280, d1281, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5663 (pattern : Twelve) (guard : d1848 pattern = 1) : d1445 pattern ≤ (0 : Int) + d1287 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1445, d1287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5167 pattern childGuard
    simpa only [d1445, d1287, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1445, d1287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5662 pattern childGuard
    simpa only [d1445, d1287, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5664 (pattern : Twelve) (guard : d1848 pattern = 1) : d1450 pattern ≤ (0 : Int) + d1297 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1450, d1297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4985 pattern childGuard
    simpa only [d1450, d1297, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1450, d1297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5663 pattern childGuard
    simpa only [d1450, d1297, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5665 (pattern : Twelve) (guard : d1848 pattern = 1) : d1449 pattern ≤ (0 : Int) + d1298 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1449, d1298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5096 pattern childGuard
    simpa only [d1449, d1298, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1449, d1298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4269 pattern childGuard
    simpa only [d1449, d1298, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5666 (pattern : Twelve) (guard : d1848 pattern = 1) : d1456 pattern ≤ (0 : Int) + d1307 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1456, d1307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5664 pattern childGuard
    simpa only [d1456, d1307, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1456, d1307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5665 pattern childGuard
    simpa only [d1456, d1307, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5667 (pattern : Twelve) (guard : d1848 pattern = 1) : d1446 pattern ≤ (0 : Int) + d1288 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1446, d1288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5179 pattern childGuard
    simpa only [d1446, d1288, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1446, d1288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5401 pattern childGuard
    simpa only [d1446, d1288, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5668 (pattern : Twelve) (guard : d1848 pattern = 1) : d1451 pattern ≤ (0 : Int) + d1299 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1451, d1299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5374 pattern childGuard
    simpa only [d1451, d1299, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1451, d1299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5667 pattern childGuard
    simpa only [d1451, d1299, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5669 (pattern : Twelve) (guard : d1848 pattern = 1) : d1452 pattern ≤ (0 : Int) + d1300 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1452, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5429 pattern childGuard
    simpa only [d1452, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1452, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4269 pattern childGuard
    simpa only [d1452, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5670 (pattern : Twelve) (guard : d1848 pattern = 1) : d1457 pattern ≤ (0 : Int) + d1308 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1457, d1308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5668 pattern childGuard
    simpa only [d1457, d1308, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1457, d1308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5669 pattern childGuard
    simpa only [d1457, d1308, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5671 (pattern : Twelve) (guard : d1848 pattern = 1) : d1460 pattern ≤ (0 : Int) + d1314 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1460, d1314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5666 pattern childGuard
    simpa only [d1460, d1314, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1460, d1314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5670 pattern childGuard
    simpa only [d1460, d1314, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5672 (pattern : Twelve) (guard : d1848 pattern = 1) : d1461 pattern ≤ (0 : Int) + d1315 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1461, d1315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5656 pattern childGuard
    simpa only [d1461, d1315, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1461, d1315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4269 pattern childGuard
    simpa only [d1461, d1315, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5673 (pattern : Twelve) (guard : d1848 pattern = 1) : d1464 pattern ≤ (0 : Int) + d1319 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1464, d1319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5671 pattern childGuard
    simpa only [d1464, d1319, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1464, d1319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5672 pattern childGuard
    simpa only [d1464, d1319, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5674 (pattern : Twelve) (guard : d1848 pattern = 1) : d1466 pattern ≤ (0 : Int) + d1321 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1466, d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5661 pattern childGuard
    simpa only [d1466, d1321, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1466, d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5673 pattern childGuard
    simpa only [d1466, d1321, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5675 (pattern : Twelve) (guard : d1848 pattern = 1) : d1467 pattern ≤ (0 : Int) + d1321 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1467, d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5660 pattern childGuard
    simpa only [d1467, d1321, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1467, d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5673 pattern childGuard
    simpa only [d1467, d1321, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5676 (pattern : Twelve) (guard : d1848 pattern = 1) : d1469 pattern ≤ (0 : Int) + d1321 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5674 pattern childGuard
    simpa only [d1469, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5675 pattern childGuard
    simpa only [d1469, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5677 (pattern : Twelve) (guard : d1848 pattern = 1) : d1470 pattern ≤ (0 : Int) + d1321 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5676 pattern childGuard
    simpa only [d1470, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5675 pattern childGuard
    simpa only [d1470, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5678 (pattern : Twelve) (guard : d1848 pattern = 1) : d1444 pattern ≤ (0 : Int) + d1325 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d1444, d1325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1469 pattern childGuard
    simpa only [d1848, d1444, d1325, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d1444, d1325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1102 pattern childGuard
    simpa only [d1848, d1444, d1325, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5679 (pattern : Twelve) (guard : d1848 pattern = 1) : d1280 pattern ≤ (0 : Int) + d1326 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d1280, d1326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4265 pattern childGuard
    simpa only [d1848, d1280, d1326, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d1280, d1326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1102 pattern childGuard
    simpa only [d1848, d1280, d1326, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5680 (pattern : Twelve) (guard : d1848 pattern = 1) : d1445 pattern ≤ (0 : Int) + d1333 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1445, d1333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5678 pattern childGuard
    simpa only [d1445, d1333, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1445, d1333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5679 pattern childGuard
    simpa only [d1445, d1333, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5681 (pattern : Twelve) (guard : d1848 pattern = 1) : d1450 pattern ≤ (0 : Int) + d1339 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1450, d1339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5109 pattern childGuard
    simpa only [d1450, d1339, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1450, d1339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5680 pattern childGuard
    simpa only [d1450, d1339, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5682 (pattern : Twelve) (guard : d1848 pattern = 1) : d1456 pattern ≤ (0 : Int) + d1345 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1456, d1345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5681 pattern childGuard
    simpa only [d1456, d1345, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1456, d1345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5650 pattern childGuard
    simpa only [d1456, d1345, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5683 (pattern : Twelve) (guard : d1848 pattern = 1) : d1444 pattern ≤ (0 : Int) + d1327 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d1444, d1327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1469 pattern childGuard
    simpa only [d1848, d1444, d1327, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d1444, d1327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5392 pattern childGuard
    simpa only [d1848, d1444, d1327, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5684 (pattern : Twelve) (guard : d1848 pattern = 1) : d1445 pattern ≤ (0 : Int) + d1334 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1445, d1334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5683 pattern childGuard
    simpa only [d1445, d1334, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1445, d1334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5652 pattern childGuard
    simpa only [d1445, d1334, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5685 (pattern : Twelve) (guard : d1848 pattern = 1) : d1450 pattern ≤ (0 : Int) + d1340 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1450, d1340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5355 pattern childGuard
    simpa only [d1450, d1340, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1450, d1340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5684 pattern childGuard
    simpa only [d1450, d1340, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5686 (pattern : Twelve) (guard : d1848 pattern = 1) : d1456 pattern ≤ (0 : Int) + d1346 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1456, d1346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5685 pattern childGuard
    simpa only [d1456, d1346, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1456, d1346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5655 pattern childGuard
    simpa only [d1456, d1346, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5687 (pattern : Twelve) (guard : d1848 pattern = 1) : d1456 pattern ≤ (0 : Int) + d1349 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5682 pattern childGuard
    simpa only [d1349, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5686 pattern childGuard
    simpa only [d1349, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5688 (pattern : Twelve) (guard : d1848 pattern = 1) : d1280 pattern ≤ (0 : Int) + d1328 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d1280, d1328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4265 pattern childGuard
    simpa only [d1848, d1280, d1328, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d1280, d1328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5178 pattern childGuard
    simpa only [d1848, d1280, d1328, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5689 (pattern : Twelve) (guard : d1848 pattern = 1) : d1445 pattern ≤ (0 : Int) + d1335 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1445, d1335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5683 pattern childGuard
    simpa only [d1445, d1335, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1445, d1335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5688 pattern childGuard
    simpa only [d1445, d1335, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5690 (pattern : Twelve) (guard : d1848 pattern = 1) : d1450 pattern ≤ (0 : Int) + d1341 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1450, d1341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4985 pattern childGuard
    simpa only [d1450, d1341, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1450, d1341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5689 pattern childGuard
    simpa only [d1450, d1341, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5691 (pattern : Twelve) (guard : d1848 pattern = 1) : d1449 pattern ≤ (0 : Int) + d1342 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1449, d1342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5440 pattern childGuard
    simpa only [d1449, d1342, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1449, d1342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4269 pattern childGuard
    simpa only [d1449, d1342, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5692 (pattern : Twelve) (guard : d1848 pattern = 1) : d1456 pattern ≤ (0 : Int) + d1347 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1456, d1347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5690 pattern childGuard
    simpa only [d1456, d1347, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1456, d1347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5691 pattern childGuard
    simpa only [d1456, d1347, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5693 (pattern : Twelve) (guard : d1848 pattern = 1) : d1337 pattern ≤ (0 : Int) + d1337 pattern := by
  omega
theorem c5694 (pattern : Twelve) (guard : d1848 pattern = 1) : d1453 pattern ≤ (0 : Int) + d1343 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1453, d1343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5374 pattern childGuard
    simpa only [d1453, d1343, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1453, d1343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5693 pattern childGuard
    simpa only [d1453, d1343, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5695 (pattern : Twelve) (guard : d1848 pattern = 1) : d1454 pattern ≤ (0 : Int) + d1344 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1454, d1344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5447 pattern childGuard
    simpa only [d1454, d1344, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1454, d1344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4269 pattern childGuard
    simpa only [d1454, d1344, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5696 (pattern : Twelve) (guard : d1848 pattern = 1) : d1458 pattern ≤ (0 : Int) + d1348 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1458, d1348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5694 pattern childGuard
    simpa only [d1458, d1348, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1458, d1348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5695 pattern childGuard
    simpa only [d1458, d1348, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5697 (pattern : Twelve) (guard : d1848 pattern = 1) : d1462 pattern ≤ (0 : Int) + d1350 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1462, d1350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5692 pattern childGuard
    simpa only [d1462, d1350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1462, d1350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5696 pattern childGuard
    simpa only [d1462, d1350, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5698 (pattern : Twelve) (guard : d1848 pattern = 1) : d1461 pattern ≤ (0 : Int) + d1351 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1461, d1351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5686 pattern childGuard
    simpa only [d1461, d1351, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1461, d1351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4269 pattern childGuard
    simpa only [d1461, d1351, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5699 (pattern : Twelve) (guard : d1848 pattern = 1) : d1465 pattern ≤ (0 : Int) + d1352 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1465, d1352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5697 pattern childGuard
    simpa only [d1465, d1352, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1465, d1352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5698 pattern childGuard
    simpa only [d1465, d1352, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5700 (pattern : Twelve) (guard : d1848 pattern = 1) : d1468 pattern ≤ (0 : Int) + d1353 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1468, d1353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5687 pattern childGuard
    simpa only [d1468, d1353, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1468, d1353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5699 pattern childGuard
    simpa only [d1468, d1353, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5701 (pattern : Twelve) (guard : d1848 pattern = 1) : d1471 pattern ≤ (0 : Int) + d1354 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1471, d1354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5677 pattern childGuard
    simpa only [d1471, d1354, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1471, d1354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5700 pattern childGuard
    simpa only [d1471, d1354, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5702 (pattern : Twelve) (guard : d1848 pattern = 1) : d1716 pattern ≤ (0 : Int) + d1649 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1716, d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5162 pattern childGuard
    simpa only [d1716, d1649, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1716, d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5211 pattern childGuard
    simpa only [d1716, d1649, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5703 (pattern : Twelve) (guard : d1848 pattern = 1) : d1452 pattern ≤ (0 : Int) + d1650 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1452, d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5214 pattern childGuard
    simpa only [d1452, d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1452, d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4269 pattern childGuard
    simpa only [d1452, d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5704 (pattern : Twelve) (guard : d1848 pattern = 1) : d1719 pattern ≤ (0 : Int) + d1656 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1719, d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5702 pattern childGuard
    simpa only [d1719, d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1719, d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5703 pattern childGuard
    simpa only [d1719, d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5705 (pattern : Twelve) (guard : d1848 pattern = 1) : d1645 pattern ≤ (0 : Int) + d1645 pattern := by
  omega
theorem c5706 (pattern : Twelve) (guard : d1848 pattern = 1) : d1645 pattern ≤ (0 : Int) + d1647 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5219 pattern childGuard
    simpa only [d1647, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5705 pattern childGuard
    simpa only [d1647, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5707 (pattern : Twelve) (guard : d1848 pattern = 1) : d1716 pattern ≤ (0 : Int) + d1651 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1716, d1651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5416 pattern childGuard
    simpa only [d1716, d1651, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1716, d1651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5706 pattern childGuard
    simpa only [d1716, d1651, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5708 (pattern : Twelve) (guard : d1848 pattern = 1) : d1719 pattern ≤ (0 : Int) + d1657 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1719, d1657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5707 pattern childGuard
    simpa only [d1719, d1657, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1719, d1657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5669 pattern childGuard
    simpa only [d1719, d1657, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5709 (pattern : Twelve) (guard : d1848 pattern = 1) : d1719 pattern ≤ (0 : Int) + d1660 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5704 pattern childGuard
    simpa only [d1660, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5708 pattern childGuard
    simpa only [d1660, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5710 (pattern : Twelve) (guard : d1848 pattern = 1) : d1716 pattern ≤ (0 : Int) + d1652 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1716, d1652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5096 pattern childGuard
    simpa only [d1716, d1652, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1716, d1652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5219 pattern childGuard
    simpa only [d1716, d1652, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5711 (pattern : Twelve) (guard : d1848 pattern = 1) : d1452 pattern ≤ (0 : Int) + d1653 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1452, d1653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5123 pattern childGuard
    simpa only [d1452, d1653, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1452, d1653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4269 pattern childGuard
    simpa only [d1452, d1653, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5712 (pattern : Twelve) (guard : d1848 pattern = 1) : d1719 pattern ≤ (0 : Int) + d1658 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1719, d1658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5710 pattern childGuard
    simpa only [d1719, d1658, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1719, d1658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5711 pattern childGuard
    simpa only [d1719, d1658, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5713 (pattern : Twelve) (guard : d1848 pattern = 1) : d128 pattern ≤ (0 : Int) + d1648 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5225 pattern childGuard
    simpa only [d1648, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5446 pattern childGuard
    simpa only [d1648, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5714 (pattern : Twelve) (guard : d1848 pattern = 1) : d1717 pattern ≤ (0 : Int) + d1654 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1717, d1654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5429 pattern childGuard
    simpa only [d1717, d1654, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1717, d1654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5713 pattern childGuard
    simpa only [d1717, d1654, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5715 (pattern : Twelve) (guard : d1848 pattern = 1) : d1655 pattern ≤ (0 : Int) + d1655 pattern := by
  omega
theorem c5716 (pattern : Twelve) (guard : d1848 pattern = 1) : d1720 pattern ≤ (0 : Int) + d1659 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1720, d1659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5714 pattern childGuard
    simpa only [d1720, d1659, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1720, d1659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5715 pattern childGuard
    simpa only [d1720, d1659, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5717 (pattern : Twelve) (guard : d1848 pattern = 1) : d1722 pattern ≤ (0 : Int) + d1661 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1722, d1661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5712 pattern childGuard
    simpa only [d1722, d1661, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1722, d1661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5716 pattern childGuard
    simpa only [d1722, d1661, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5718 (pattern : Twelve) (guard : d1848 pattern = 1) : d1723 pattern ≤ (0 : Int) + d1662 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1723, d1662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5708 pattern childGuard
    simpa only [d1723, d1662, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1723, d1662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4269 pattern childGuard
    simpa only [d1723, d1662, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5719 (pattern : Twelve) (guard : d1848 pattern = 1) : d1725 pattern ≤ (0 : Int) + d1663 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1725, d1663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5717 pattern childGuard
    simpa only [d1725, d1663, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1725, d1663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5718 pattern childGuard
    simpa only [d1725, d1663, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5720 (pattern : Twelve) (guard : d1848 pattern = 1) : d1727 pattern ≤ (0 : Int) + d1664 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1727, d1664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5709 pattern childGuard
    simpa only [d1727, d1664, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1727, d1664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5719 pattern childGuard
    simpa only [d1727, d1664, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5721 (pattern : Twelve) (guard : d1848 pattern = 1) : d1716 pattern ≤ (0 : Int) + d1668 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1716, d1668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5162 pattern childGuard
    simpa only [d1716, d1668, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1716, d1668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5219 pattern childGuard
    simpa only [d1716, d1668, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5722 (pattern : Twelve) (guard : d1848 pattern = 1) : d1719 pattern ≤ (0 : Int) + d1671 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1719, d1671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5721 pattern childGuard
    simpa only [d1719, d1671, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1719, d1671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5703 pattern childGuard
    simpa only [d1719, d1671, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5723 (pattern : Twelve) (guard : d1848 pattern = 1) : d1719 pattern ≤ (0 : Int) + d1674 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5722 pattern childGuard
    simpa only [d1674, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5708 pattern childGuard
    simpa only [d1674, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5724 (pattern : Twelve) (guard : d1848 pattern = 1) : d1645 pattern ≤ (0 : Int) + d1665 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d1645, d1665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c388 pattern childGuard
    simpa only [d1848, d1645, d1665, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d1645, d1665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5224 pattern childGuard
    simpa only [d1848, d1645, d1665, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5725 (pattern : Twelve) (guard : d1848 pattern = 1) : d1645 pattern ≤ (0 : Int) + d1666 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5219 pattern childGuard
    simpa only [d1666, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5724 pattern childGuard
    simpa only [d1666, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5726 (pattern : Twelve) (guard : d1848 pattern = 1) : d1716 pattern ≤ (0 : Int) + d1669 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1716, d1669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5096 pattern childGuard
    simpa only [d1716, d1669, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1716, d1669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5725 pattern childGuard
    simpa only [d1716, d1669, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5727 (pattern : Twelve) (guard : d1848 pattern = 1) : d1719 pattern ≤ (0 : Int) + d1672 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1719, d1672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5726 pattern childGuard
    simpa only [d1719, d1672, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1719, d1672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5669 pattern childGuard
    simpa only [d1719, d1672, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5728 (pattern : Twelve) (guard : d1848 pattern = 1) : d1667 pattern ≤ (0 : Int) + d1667 pattern := by
  omega
theorem c5729 (pattern : Twelve) (guard : d1848 pattern = 1) : d1718 pattern ≤ (0 : Int) + d1670 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1718, d1670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5429 pattern childGuard
    simpa only [d1718, d1670, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1718, d1670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5728 pattern childGuard
    simpa only [d1718, d1670, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5730 (pattern : Twelve) (guard : d1848 pattern = 1) : d1626 pattern ≤ (0 : Int) + d1626 pattern := by
  omega
theorem c5731 (pattern : Twelve) (guard : d1848 pattern = 1) : d1721 pattern ≤ (0 : Int) + d1673 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1721, d1673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5729 pattern childGuard
    simpa only [d1721, d1673, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1721, d1673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5730 pattern childGuard
    simpa only [d1721, d1673, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5732 (pattern : Twelve) (guard : d1848 pattern = 1) : d1724 pattern ≤ (0 : Int) + d1675 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1724, d1675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5727 pattern childGuard
    simpa only [d1724, d1675, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1724, d1675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5731 pattern childGuard
    simpa only [d1724, d1675, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5733 (pattern : Twelve) (guard : d1848 pattern = 1) : d1726 pattern ≤ (0 : Int) + d1676 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1726, d1676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5732 pattern childGuard
    simpa only [d1726, d1676, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1726, d1676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5718 pattern childGuard
    simpa only [d1726, d1676, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5734 (pattern : Twelve) (guard : d1848 pattern = 1) : d1728 pattern ≤ (0 : Int) + d1677 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1728, d1677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5723 pattern childGuard
    simpa only [d1728, d1677, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1728, d1677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5733 pattern childGuard
    simpa only [d1728, d1677, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5735 (pattern : Twelve) (guard : d1848 pattern = 1) : d1729 pattern ≤ (0 : Int) + d1678 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1729, d1678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5720 pattern childGuard
    simpa only [d1729, d1678, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1729, d1678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5734 pattern childGuard
    simpa only [d1729, d1678, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5736 (pattern : Twelve) (guard : d0 pattern = 1) : d403 pattern ≤ (0 : Int) + d208 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5737 (pattern : Twelve) (guard : d1869 pattern = 1) : d409 pattern ≤ (0 : Int) + d352 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d409, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5483 pattern childGuard
    simpa only [d1869, d409, d352, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d409, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5736 pattern childGuard
    simpa only [d1869, d409, d352, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5738 (pattern : Twelve) (guard : d0 pattern = 1) : d404 pattern ≤ (0 : Int) + d209 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5739 (pattern : Twelve) (guard : d1869 pattern = 1) : d410 pattern ≤ (0 : Int) + d353 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d410, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5494 pattern childGuard
    simpa only [d1869, d410, d353, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d410, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5738 pattern childGuard
    simpa only [d1869, d410, d353, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
