/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons145
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c20440 (pattern : Twelve) (guard : d1 pattern = 1) : d815 pattern ≤ (2 : Int) + d3 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20328 pattern childGuard
    simpa only [d815, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13331 pattern childGuard
    simpa only [d815, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20441 (pattern : Twelve) (guard : d1 pattern = 1) : d820 pattern ≤ (2 : Int) + d47 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d820, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20440 pattern childGuard
    simpa only [d820, d47, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d820, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d820, d47, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20442 (pattern : Twelve) (guard : d1 pattern = 1) : d829 pattern ≤ (2 : Int) + d836 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d829, d836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20335 pattern childGuard
    simpa only [d829, d836, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d829, d836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20441 pattern childGuard
    simpa only [d829, d836, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20443 (pattern : Twelve) (guard : d1 pattern = 1) : d844 pattern ≤ (2 : Int) + d851 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d844, d851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20326 pattern childGuard
    simpa only [d844, d851, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d844, d851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20442 pattern childGuard
    simpa only [d844, d851, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20444 (pattern : Twelve) (guard : d1 pattern = 1) : d40 pattern ≤ (2 : Int) + d48 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d40, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20364 pattern childGuard
    simpa only [d40, d48, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d40, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d40, d48, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20445 (pattern : Twelve) (guard : d1 pattern = 1) : d830 pattern ≤ (2 : Int) + d837 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d830, d837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20335 pattern childGuard
    simpa only [d830, d837, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d830, d837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20444 pattern childGuard
    simpa only [d830, d837, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20446 (pattern : Twelve) (guard : d1 pattern = 1) : d831 pattern ≤ (2 : Int) + d831 pattern := by
  omega
theorem c20447 (pattern : Twelve) (guard : d1 pattern = 1) : d845 pattern ≤ (2 : Int) + d852 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d845, d852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20445 pattern childGuard
    simpa only [d845, d852, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d845, d852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20446 pattern childGuard
    simpa only [d845, d852, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20448 (pattern : Twelve) (guard : d1 pattern = 1) : d856 pattern ≤ (2 : Int) + d860 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d856, d860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20443 pattern childGuard
    simpa only [d856, d860, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d856, d860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20447 pattern childGuard
    simpa only [d856, d860, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20449 (pattern : Twelve) (guard : d1 pattern = 1) : d862 pattern ≤ (2 : Int) + d865 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d862, d865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20439 pattern childGuard
    simpa only [d862, d865, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d862, d865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20448 pattern childGuard
    simpa only [d862, d865, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20450 (pattern : Twelve) (guard : d1 pattern = 1) : d863 pattern ≤ (2 : Int) + d866 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d863, d866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20431 pattern childGuard
    simpa only [d863, d866, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d863, d866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d863, d866, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20451 (pattern : Twelve) (guard : d1 pattern = 1) : d867 pattern ≤ (2 : Int) + d868 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d867, d868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20449 pattern childGuard
    simpa only [d867, d868, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d867, d868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20450 pattern childGuard
    simpa only [d867, d868, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20452 (pattern : Twelve) (guard : d1 pattern = 1) : d869 pattern ≤ (2 : Int) + d870 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d869, d870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20432 pattern childGuard
    simpa only [d869, d870, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d869, d870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20451 pattern childGuard
    simpa only [d869, d870, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20453 (pattern : Twelve) (guard : d0 pattern = 1) : d870 pattern ≤ (2 : Int) + d870 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c20454 (pattern : Twelve) (guard : d1871 pattern = 1) : d871 pattern ≤ (2 : Int) + d870 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1871, d871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20452 pattern childGuard
    simpa only [d1871, d871, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1871, d871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20453 pattern childGuard
    simpa only [d1871, d871, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20455 (pattern : Twelve) (guard : d1 pattern = 1) : d8 pattern ≤ (2 : Int) + d3 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13915 pattern childGuard
    simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13479 pattern childGuard
    simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20456 (pattern : Twelve) (guard : d1 pattern = 1) : d872 pattern ≤ (2 : Int) + d3 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13915 pattern childGuard
    simpa only [d872, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20455 pattern childGuard
    simpa only [d872, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20457 (pattern : Twelve) (guard : d1 pattern = 1) : d874 pattern ≤ (2 : Int) + d779 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d874, d779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13939 pattern childGuard
    simpa only [d874, d779, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d874, d779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20456 pattern childGuard
    simpa only [d874, d779, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20458 (pattern : Twelve) (guard : d1 pattern = 1) : d814 pattern ≤ (2 : Int) + d815 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d814, d815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13916 pattern childGuard
    simpa only [d814, d815, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d814, d815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13915 pattern childGuard
    simpa only [d814, d815, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20459 (pattern : Twelve) (guard : d1 pattern = 1) : d875 pattern ≤ (2 : Int) + d1247 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d875, d1247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20458 pattern childGuard
    simpa only [d875, d1247, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d875, d1247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20456 pattern childGuard
    simpa only [d875, d1247, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20460 (pattern : Twelve) (guard : d1 pattern = 1) : d882 pattern ≤ (2 : Int) + d1249 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d882, d1249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20457 pattern childGuard
    simpa only [d882, d1249, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d882, d1249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20459 pattern childGuard
    simpa only [d882, d1249, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20461 (pattern : Twelve) (guard : d1 pattern = 1) : d890 pattern ≤ (2 : Int) + d1253 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d890, d1253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13913 pattern childGuard
    simpa only [d890, d1253, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d890, d1253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20460 pattern childGuard
    simpa only [d890, d1253, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20462 (pattern : Twelve) (guard : d1 pattern = 1) : d7 pattern ≤ (2 : Int) + d4 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14572 pattern childGuard
    simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20374 pattern childGuard
    simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20463 (pattern : Twelve) (guard : d1 pattern = 1) : d17 pattern ≤ (2 : Int) + d4 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14572 pattern childGuard
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20462 pattern childGuard
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20464 (pattern : Twelve) (guard : d1 pattern = 1) : d17 pattern ≤ (2 : Int) + d1248 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13939 pattern childGuard
    simpa only [d1248, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20463 pattern childGuard
    simpa only [d1248, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20465 (pattern : Twelve) (guard : d1 pattern = 1) : d876 pattern ≤ (2 : Int) + d821 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d876, d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13995 pattern childGuard
    simpa only [d876, d821, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d876, d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14323 pattern childGuard
    simpa only [d876, d821, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20466 (pattern : Twelve) (guard : d1 pattern = 1) : d16 pattern ≤ (2 : Int) + d13 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d16, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13482 pattern childGuard
    simpa only [d16, d13, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d16, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13515 pattern childGuard
    simpa only [d16, d13, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20467 (pattern : Twelve) (guard : d1 pattern = 1) : d25 pattern ≤ (2 : Int) + d21 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d25, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20466 pattern childGuard
    simpa only [d25, d21, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d25, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20359 pattern childGuard
    simpa only [d25, d21, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20468 (pattern : Twelve) (guard : d1 pattern = 1) : d42 pattern ≤ (2 : Int) + d822 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d42, d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20467 pattern childGuard
    simpa only [d42, d822, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d42, d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d42, d822, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20469 (pattern : Twelve) (guard : d1 pattern = 1) : d883 pattern ≤ (2 : Int) + d831 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d883, d831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20465 pattern childGuard
    simpa only [d883, d831, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d883, d831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20468 pattern childGuard
    simpa only [d883, d831, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20470 (pattern : Twelve) (guard : d1 pattern = 1) : d891 pattern ≤ (2 : Int) + d1254 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d891, d1254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20464 pattern childGuard
    simpa only [d891, d1254, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d891, d1254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20469 pattern childGuard
    simpa only [d891, d1254, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20471 (pattern : Twelve) (guard : d1 pattern = 1) : d898 pattern ≤ (2 : Int) + d1258 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d898, d1258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20461 pattern childGuard
    simpa only [d898, d1258, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d898, d1258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20470 pattern childGuard
    simpa only [d898, d1258, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20472 (pattern : Twelve) (guard : d1 pattern = 1) : d3 pattern ≤ (2 : Int) + d15 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13488 pattern childGuard
    simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13491 pattern childGuard
    simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20473 (pattern : Twelve) (guard : d1 pattern = 1) : d815 pattern ≤ (2 : Int) + d24 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d815, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20363 pattern childGuard
    simpa only [d815, d24, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d815, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20472 pattern childGuard
    simpa only [d815, d24, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20474 (pattern : Twelve) (guard : d1 pattern = 1) : d877 pattern ≤ (2 : Int) + d41 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d877, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13939 pattern childGuard
    simpa only [d877, d41, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d877, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20473 pattern childGuard
    simpa only [d877, d41, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20475 (pattern : Twelve) (guard : d1 pattern = 1) : d814 pattern ≤ (2 : Int) + d3 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20366 pattern childGuard
    simpa only [d814, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13915 pattern childGuard
    simpa only [d814, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20476 (pattern : Twelve) (guard : d1 pattern = 1) : d818 pattern ≤ (2 : Int) + d47 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d818, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20475 pattern childGuard
    simpa only [d818, d47, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d818, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d818, d47, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20477 (pattern : Twelve) (guard : d1 pattern = 1) : d884 pattern ≤ (2 : Int) + d836 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d884, d836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20474 pattern childGuard
    simpa only [d884, d836, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d884, d836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20476 pattern childGuard
    simpa only [d884, d836, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20478 (pattern : Twelve) (guard : d1 pattern = 1) : d892 pattern ≤ (2 : Int) + d851 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d892, d851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20382 pattern childGuard
    simpa only [d892, d851, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d892, d851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20477 pattern childGuard
    simpa only [d892, d851, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20479 (pattern : Twelve) (guard : d1 pattern = 1) : d34 pattern ≤ (2 : Int) + d41 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d34, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13939 pattern childGuard
    simpa only [d34, d41, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d34, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20407 pattern childGuard
    simpa only [d34, d41, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20480 (pattern : Twelve) (guard : d1 pattern = 1) : d36 pattern ≤ (2 : Int) + d48 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d36, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20463 pattern childGuard
    simpa only [d36, d48, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d36, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d36, d48, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20481 (pattern : Twelve) (guard : d1 pattern = 1) : d827 pattern ≤ (2 : Int) + d837 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d827, d837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20479 pattern childGuard
    simpa only [d827, d837, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d827, d837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20480 pattern childGuard
    simpa only [d827, d837, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20482 (pattern : Twelve) (guard : d1 pattern = 1) : d893 pattern ≤ (2 : Int) + d852 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d893, d852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20481 pattern childGuard
    simpa only [d893, d852, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d893, d852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20469 pattern childGuard
    simpa only [d893, d852, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20483 (pattern : Twelve) (guard : d1 pattern = 1) : d899 pattern ≤ (2 : Int) + d860 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d899, d860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20478 pattern childGuard
    simpa only [d899, d860, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d899, d860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20482 pattern childGuard
    simpa only [d899, d860, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20484 (pattern : Twelve) (guard : d1 pattern = 1) : d902 pattern ≤ (2 : Int) + d1261 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d902, d1261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20471 pattern childGuard
    simpa only [d902, d1261, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d902, d1261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20483 pattern childGuard
    simpa only [d902, d1261, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20485 (pattern : Twelve) (guard : d1 pattern = 1) : d15 pattern ≤ (2 : Int) + d5 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13514 pattern childGuard
    simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14229 pattern childGuard
    simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20486 (pattern : Twelve) (guard : d1 pattern = 1) : d24 pattern ≤ (2 : Int) + d5 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13514 pattern childGuard
    simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20485 pattern childGuard
    simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20487 (pattern : Twelve) (guard : d1 pattern = 1) : d878 pattern ≤ (2 : Int) + d780 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d878, d780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20475 pattern childGuard
    simpa only [d878, d780, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d878, d780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20486 pattern childGuard
    simpa only [d878, d780, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20488 (pattern : Twelve) (guard : d1 pattern = 1) : d885 pattern ≤ (2 : Int) + d1250 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d885, d1250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20474 pattern childGuard
    simpa only [d885, d1250, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d885, d1250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20487 pattern childGuard
    simpa only [d885, d1250, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20489 (pattern : Twelve) (guard : d1 pattern = 1) : d894 pattern ≤ (2 : Int) + d1255 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d894, d1255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20322 pattern childGuard
    simpa only [d894, d1255, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d894, d1255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20488 pattern childGuard
    simpa only [d894, d1255, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20490 (pattern : Twelve) (guard : d1 pattern = 1) : d879 pattern ≤ (2 : Int) + d48 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d879, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20463 pattern childGuard
    simpa only [d879, d48, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d879, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13569 pattern childGuard
    simpa only [d879, d48, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20491 (pattern : Twelve) (guard : d1 pattern = 1) : d886 pattern ≤ (2 : Int) + d837 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d886, d837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20479 pattern childGuard
    simpa only [d886, d837, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d886, d837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20490 pattern childGuard
    simpa only [d886, d837, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20492 (pattern : Twelve) (guard : d1 pattern = 1) : d895 pattern ≤ (2 : Int) + d852 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d895, d852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20491 pattern childGuard
    simpa only [d895, d852, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d895, d852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20469 pattern childGuard
    simpa only [d895, d852, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20493 (pattern : Twelve) (guard : d1 pattern = 1) : d900 pattern ≤ (2 : Int) + d1259 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d900, d1259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20489 pattern childGuard
    simpa only [d900, d1259, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d900, d1259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20492 pattern childGuard
    simpa only [d900, d1259, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20494 (pattern : Twelve) (guard : d1 pattern = 1) : d873 pattern ≤ (2 : Int) + d5 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20398 pattern childGuard
    simpa only [d873, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20485 pattern childGuard
    simpa only [d873, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20495 (pattern : Twelve) (guard : d1 pattern = 1) : d880 pattern ≤ (2 : Int) + d781 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d880, d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20494 pattern childGuard
    simpa only [d880, d781, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d880, d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d880, d781, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20496 (pattern : Twelve) (guard : d1 pattern = 1) : d887 pattern ≤ (2 : Int) + d1251 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d887, d1251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20409 pattern childGuard
    simpa only [d887, d1251, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d887, d1251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20495 pattern childGuard
    simpa only [d887, d1251, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20497 (pattern : Twelve) (guard : d1 pattern = 1) : d896 pattern ≤ (2 : Int) + d1256 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d896, d1256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20395 pattern childGuard
    simpa only [d896, d1256, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d896, d1256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20496 pattern childGuard
    simpa only [d896, d1256, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20498 (pattern : Twelve) (guard : d1 pattern = 1) : d881 pattern ≤ (2 : Int) + d49 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d881, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20407 pattern childGuard
    simpa only [d881, d49, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d881, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20396 pattern childGuard
    simpa only [d881, d49, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20499 (pattern : Twelve) (guard : d1 pattern = 1) : d125 pattern ≤ (2 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13569 pattern childGuard
    simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20500 (pattern : Twelve) (guard : d1 pattern = 1) : d888 pattern ≤ (2 : Int) + d787 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d888, d787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20498 pattern childGuard
    simpa only [d888, d787, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d888, d787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20499 pattern childGuard
    simpa only [d888, d787, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20501 (pattern : Twelve) (guard : d1 pattern = 1) : d889 pattern ≤ (2 : Int) + d1252 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d889, d1252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20468 pattern childGuard
    simpa only [d889, d1252, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d889, d1252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d889, d1252, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20502 (pattern : Twelve) (guard : d1 pattern = 1) : d897 pattern ≤ (2 : Int) + d1257 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d897, d1257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20500 pattern childGuard
    simpa only [d897, d1257, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d897, d1257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20501 pattern childGuard
    simpa only [d897, d1257, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20503 (pattern : Twelve) (guard : d1 pattern = 1) : d901 pattern ≤ (2 : Int) + d1260 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d901, d1260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20497 pattern childGuard
    simpa only [d901, d1260, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d901, d1260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20502 pattern childGuard
    simpa only [d901, d1260, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20504 (pattern : Twelve) (guard : d1 pattern = 1) : d903 pattern ≤ (2 : Int) + d1262 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d903, d1262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20493 pattern childGuard
    simpa only [d903, d1262, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d903, d1262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20503 pattern childGuard
    simpa only [d903, d1262, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20505 (pattern : Twelve) (guard : d1 pattern = 1) : d904 pattern ≤ (2 : Int) + d1263 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d904, d1263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20483 pattern childGuard
    simpa only [d904, d1263, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d904, d1263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d904, d1263, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20506 (pattern : Twelve) (guard : d1 pattern = 1) : d905 pattern ≤ (2 : Int) + d1264 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d905, d1264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20504 pattern childGuard
    simpa only [d905, d1264, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d905, d1264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20505 pattern childGuard
    simpa only [d905, d1264, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20507 (pattern : Twelve) (guard : d1 pattern = 1) : d906 pattern ≤ (2 : Int) + d1265 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d906, d1265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20484 pattern childGuard
    simpa only [d906, d1265, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d906, d1265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20506 pattern childGuard
    simpa only [d906, d1265, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20508 (pattern : Twelve) (guard : d0 pattern = 1) : d1265 pattern ≤ (2 : Int) + d1265 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c20509 (pattern : Twelve) (guard : d1871 pattern = 1) : d1266 pattern ≤ (2 : Int) + d1265 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1871, d1266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20507 pattern childGuard
    simpa only [d1871, d1266, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1871, d1266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20508 pattern childGuard
    simpa only [d1871, d1266, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20510 (pattern : Twelve) (guard : d1871 pattern = 1) : d1267 pattern ≤ (2 : Int) + d3238 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1871 pattern = 1 := by simpa only [d1267, d3238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20454 pattern childGuard
    simpa only [d1267, d3238, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1871 pattern = 1 := by simpa only [d1267, d3238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20509 pattern childGuard
    simpa only [d1267, d3238, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20511 (pattern : Twelve) (guard : d1 pattern = 1) : d1293 pattern ≤ (2 : Int) + d1293 pattern := by
  omega
theorem c20512 (pattern : Twelve) (guard : d1 pattern = 1) : d19 pattern ≤ (2 : Int) + d1283 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13418 pattern childGuard
    simpa only [d1283, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14048 pattern childGuard
    simpa only [d1283, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20513 (pattern : Twelve) (guard : d1 pattern = 1) : d1294 pattern ≤ (2 : Int) + d1301 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1294, d1301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20512 pattern childGuard
    simpa only [d1294, d1301, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1294, d1301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d1294, d1301, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20514 (pattern : Twelve) (guard : d1 pattern = 1) : d1305 pattern ≤ (2 : Int) + d1309 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1305, d1309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20511 pattern childGuard
    simpa only [d1305, d1309, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1305, d1309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20513 pattern childGuard
    simpa only [d1305, d1309, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20515 (pattern : Twelve) (guard : d1 pattern = 1) : d1295 pattern ≤ (2 : Int) + d1295 pattern := by
  omega
theorem c20516 (pattern : Twelve) (guard : d1 pattern = 1) : d1286 pattern ≤ (2 : Int) + d1290 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1286, d1290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13573 pattern childGuard
    simpa only [d1286, d1290, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1286, d1290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20302 pattern childGuard
    simpa only [d1286, d1290, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20517 (pattern : Twelve) (guard : d1 pattern = 1) : d1296 pattern ≤ (2 : Int) + d1302 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1296, d1302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20516 pattern childGuard
    simpa only [d1296, d1302, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1296, d1302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d1296, d1302, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20518 (pattern : Twelve) (guard : d1 pattern = 1) : d1306 pattern ≤ (2 : Int) + d1310 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1306, d1310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20515 pattern childGuard
    simpa only [d1306, d1310, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1306, d1310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20517 pattern childGuard
    simpa only [d1306, d1310, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20519 (pattern : Twelve) (guard : d1 pattern = 1) : d1313 pattern ≤ (2 : Int) + d1316 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1313, d1316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20514 pattern childGuard
    simpa only [d1313, d1316, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1313, d1316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20518 pattern childGuard
    simpa only [d1313, d1316, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20520 (pattern : Twelve) (guard : d1 pattern = 1) : d1297 pattern ≤ (2 : Int) + d1297 pattern := by
  omega
theorem c20521 (pattern : Twelve) (guard : d1 pattern = 1) : d817 pattern ≤ (2 : Int) + d41 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d817, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14048 pattern childGuard
    simpa only [d817, d41, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d817, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20338 pattern childGuard
    simpa only [d817, d41, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20522 (pattern : Twelve) (guard : d1 pattern = 1) : d817 pattern ≤ (2 : Int) + d1291 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13573 pattern childGuard
    simpa only [d1291, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20521 pattern childGuard
    simpa only [d1291, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20523 (pattern : Twelve) (guard : d1 pattern = 1) : d1298 pattern ≤ (2 : Int) + d1303 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1298, d1303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20522 pattern childGuard
    simpa only [d1298, d1303, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1298, d1303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d1298, d1303, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20524 (pattern : Twelve) (guard : d1 pattern = 1) : d1307 pattern ≤ (2 : Int) + d1311 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1307, d1311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20520 pattern childGuard
    simpa only [d1307, d1311, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1307, d1311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20523 pattern childGuard
    simpa only [d1307, d1311, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20525 (pattern : Twelve) (guard : d1 pattern = 1) : d1299 pattern ≤ (2 : Int) + d1299 pattern := by
  omega
theorem c20526 (pattern : Twelve) (guard : d1 pattern = 1) : d1289 pattern ≤ (2 : Int) + d1292 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1289, d1292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13612 pattern childGuard
    simpa only [d1289, d1292, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1289, d1292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20339 pattern childGuard
    simpa only [d1289, d1292, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20527 (pattern : Twelve) (guard : d1 pattern = 1) : d1300 pattern ≤ (2 : Int) + d1304 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1300, d1304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20526 pattern childGuard
    simpa only [d1300, d1304, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1300, d1304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d1300, d1304, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20528 (pattern : Twelve) (guard : d1 pattern = 1) : d1308 pattern ≤ (2 : Int) + d1312 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1308, d1312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20525 pattern childGuard
    simpa only [d1308, d1312, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1308, d1312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20527 pattern childGuard
    simpa only [d1308, d1312, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20529 (pattern : Twelve) (guard : d1 pattern = 1) : d1314 pattern ≤ (2 : Int) + d1317 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1314, d1317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20524 pattern childGuard
    simpa only [d1314, d1317, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1314, d1317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20528 pattern childGuard
    simpa only [d1314, d1317, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20530 (pattern : Twelve) (guard : d1 pattern = 1) : d1315 pattern ≤ (2 : Int) + d1318 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1315, d1318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20518 pattern childGuard
    simpa only [d1315, d1318, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1315, d1318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d1315, d1318, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20531 (pattern : Twelve) (guard : d1 pattern = 1) : d1319 pattern ≤ (2 : Int) + d1320 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1319, d1320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20529 pattern childGuard
    simpa only [d1319, d1320, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1319, d1320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20530 pattern childGuard
    simpa only [d1319, d1320, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20532 (pattern : Twelve) (guard : d1 pattern = 1) : d1321 pattern ≤ (2 : Int) + d1322 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1321, d1322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20519 pattern childGuard
    simpa only [d1321, d1322, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1321, d1322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20531 pattern childGuard
    simpa only [d1321, d1322, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20533 (pattern : Twelve) (guard : d0 pattern = 1) : d1322 pattern ≤ (2 : Int) + d1322 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c20534 (pattern : Twelve) (guard : d1871 pattern = 1) : d1323 pattern ≤ (2 : Int) + d1322 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1871, d1323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20532 pattern childGuard
    simpa only [d1871, d1323, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1871, d1323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20533 pattern childGuard
    simpa only [d1871, d1323, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20535 (pattern : Twelve) (guard : d1 pattern = 1) : d8 pattern ≤ (2 : Int) + d117 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d8, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13915 pattern childGuard
    simpa only [d8, d117, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d8, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13482 pattern childGuard
    simpa only [d8, d117, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20536 (pattern : Twelve) (guard : d1 pattern = 1) : d1275 pattern ≤ (2 : Int) + d1276 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1275, d1276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13916 pattern childGuard
    simpa only [d1275, d1276, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1275, d1276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20535 pattern childGuard
    simpa only [d1275, d1276, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20537 (pattern : Twelve) (guard : d1 pattern = 1) : d11 pattern ≤ (2 : Int) + d3 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13915 pattern childGuard
    simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13331 pattern childGuard
    simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20538 (pattern : Twelve) (guard : d1 pattern = 1) : d16 pattern ≤ (2 : Int) + d117 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d16, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13479 pattern childGuard
    simpa only [d16, d117, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d16, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14227 pattern childGuard
    simpa only [d16, d117, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20539 (pattern : Twelve) (guard : d1 pattern = 1) : d1324 pattern ≤ (2 : Int) + d119 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1324, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20537 pattern childGuard
    simpa only [d1324, d119, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1324, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20538 pattern childGuard
    simpa only [d1324, d119, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20540 (pattern : Twelve) (guard : d1 pattern = 1) : d1325 pattern ≤ (2 : Int) + d1616 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1325, d1616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20536 pattern childGuard
    simpa only [d1325, d1616, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1325, d1616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20539 pattern childGuard
    simpa only [d1325, d1616, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20541 (pattern : Twelve) (guard : d1 pattern = 1) : d872 pattern ≤ (2 : Int) + d119 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d872, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13915 pattern childGuard
    simpa only [d872, d119, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d872, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20535 pattern childGuard
    simpa only [d872, d119, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20542 (pattern : Twelve) (guard : d1 pattern = 1) : d1326 pattern ≤ (2 : Int) + d119 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20541 pattern childGuard
    simpa only [d1326, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20539 pattern childGuard
    simpa only [d1326, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20543 (pattern : Twelve) (guard : d1 pattern = 1) : d1333 pattern ≤ (2 : Int) + d1619 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1333, d1619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20540 pattern childGuard
    simpa only [d1333, d1619, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1333, d1619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20542 pattern childGuard
    simpa only [d1333, d1619, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20544 (pattern : Twelve) (guard : d1 pattern = 1) : d1339 pattern ≤ (2 : Int) + d1622 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1339, d1622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13939 pattern childGuard
    simpa only [d1339, d1622, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1339, d1622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20543 pattern childGuard
    simpa only [d1339, d1622, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20545 (pattern : Twelve) (guard : d1 pattern = 1) : d19 pattern ≤ (2 : Int) + d1617 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13995 pattern childGuard
    simpa only [d1617, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20376 pattern childGuard
    simpa only [d1617, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20546 (pattern : Twelve) (guard : d1 pattern = 1) : d1294 pattern ≤ (2 : Int) + d1623 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1294, d1623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20545 pattern childGuard
    simpa only [d1294, d1623, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1294, d1623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d1294, d1623, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20547 (pattern : Twelve) (guard : d1 pattern = 1) : d1345 pattern ≤ (2 : Int) + d1627 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1345, d1627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20544 pattern childGuard
    simpa only [d1345, d1627, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1345, d1627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20546 pattern childGuard
    simpa only [d1345, d1627, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20548 (pattern : Twelve) (guard : d1 pattern = 1) : d36 pattern ≤ (2 : Int) + d40 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d36, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13939 pattern childGuard
    simpa only [d36, d40, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d36, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d36, d40, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20549 (pattern : Twelve) (guard : d1 pattern = 1) : d827 pattern ≤ (2 : Int) + d830 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d827, d830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20479 pattern childGuard
    simpa only [d827, d830, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d827, d830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20548 pattern childGuard
    simpa only [d827, d830, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20550 (pattern : Twelve) (guard : d1 pattern = 1) : d117 pattern ≤ (2 : Int) + d14 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d117, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13491 pattern childGuard
    simpa only [d117, d14, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d117, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13515 pattern childGuard
    simpa only [d117, d14, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20551 (pattern : Twelve) (guard : d1 pattern = 1) : d119 pattern ≤ (2 : Int) + d1277 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d119, d1277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20472 pattern childGuard
    simpa only [d119, d1277, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d119, d1277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20550 pattern childGuard
    simpa only [d119, d1277, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20552 (pattern : Twelve) (guard : d1 pattern = 1) : d1327 pattern ≤ (2 : Int) + d1282 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1327, d1282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20536 pattern childGuard
    simpa only [d1327, d1282, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1327, d1282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20551 pattern childGuard
    simpa only [d1327, d1282, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20553 (pattern : Twelve) (guard : d1 pattern = 1) : d1280 pattern ≤ (2 : Int) + d125 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1280, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20541 pattern childGuard
    simpa only [d1280, d125, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1280, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d1280, d125, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20554 (pattern : Twelve) (guard : d1 pattern = 1) : d1334 pattern ≤ (2 : Int) + d1288 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1334, d1288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20552 pattern childGuard
    simpa only [d1334, d1288, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1334, d1288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20553 pattern childGuard
    simpa only [d1334, d1288, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20555 (pattern : Twelve) (guard : d1 pattern = 1) : d1340 pattern ≤ (2 : Int) + d1299 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1340, d1299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20549 pattern childGuard
    simpa only [d1340, d1299, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1340, d1299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20554 pattern childGuard
    simpa only [d1340, d1299, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20556 (pattern : Twelve) (guard : d1 pattern = 1) : d817 pattern ≤ (2 : Int) + d821 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d817, d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13995 pattern childGuard
    simpa only [d817, d821, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d817, d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20467 pattern childGuard
    simpa only [d817, d821, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20557 (pattern : Twelve) (guard : d1 pattern = 1) : d1286 pattern ≤ (2 : Int) + d1292 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1286, d1292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20556 pattern childGuard
    simpa only [d1286, d1292, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1286, d1292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20377 pattern childGuard
    simpa only [d1286, d1292, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20558 (pattern : Twelve) (guard : d1 pattern = 1) : d1296 pattern ≤ (2 : Int) + d1304 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1296, d1304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20557 pattern childGuard
    simpa only [d1296, d1304, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1296, d1304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d1296, d1304, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20559 (pattern : Twelve) (guard : d1 pattern = 1) : d1346 pattern ≤ (2 : Int) + d1312 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1346, d1312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20555 pattern childGuard
    simpa only [d1346, d1312, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1346, d1312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20558 pattern childGuard
    simpa only [d1346, d1312, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20560 (pattern : Twelve) (guard : d1 pattern = 1) : d1349 pattern ≤ (2 : Int) + d1630 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1349, d1630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20547 pattern childGuard
    simpa only [d1349, d1630, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1349, d1630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20559 pattern childGuard
    simpa only [d1349, d1630, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20561 (pattern : Twelve) (guard : d1 pattern = 1) : d14 pattern ≤ (2 : Int) + d14 pattern := by
  omega
theorem c20562 (pattern : Twelve) (guard : d1 pattern = 1) : d1277 pattern ≤ (2 : Int) + d118 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1277, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20485 pattern childGuard
    simpa only [d1277, d118, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1277, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20561 pattern childGuard
    simpa only [d1277, d118, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20563 (pattern : Twelve) (guard : d1 pattern = 1) : d1328 pattern ≤ (2 : Int) + d1618 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1328, d1618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20541 pattern childGuard
    simpa only [d1328, d1618, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1328, d1618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20562 pattern childGuard
    simpa only [d1328, d1618, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20564 (pattern : Twelve) (guard : d1 pattern = 1) : d1335 pattern ≤ (2 : Int) + d1620 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1335, d1620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20552 pattern childGuard
    simpa only [d1335, d1620, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1335, d1620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20563 pattern childGuard
    simpa only [d1335, d1620, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20565 (pattern : Twelve) (guard : d1 pattern = 1) : d1341 pattern ≤ (2 : Int) + d1624 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1341, d1624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20479 pattern childGuard
    simpa only [d1341, d1624, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1341, d1624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20564 pattern childGuard
    simpa only [d1341, d1624, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20566 (pattern : Twelve) (guard : d1 pattern = 1) : d1329 pattern ≤ (2 : Int) + d49 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1329, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20376 pattern childGuard
    simpa only [d1329, d49, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1329, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13608 pattern childGuard
    simpa only [d1329, d49, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20567 (pattern : Twelve) (guard : d1 pattern = 1) : d1336 pattern ≤ (2 : Int) + d1292 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1336, d1292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20556 pattern childGuard
    simpa only [d1336, d1292, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1336, d1292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20566 pattern childGuard
    simpa only [d1336, d1292, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20568 (pattern : Twelve) (guard : d1 pattern = 1) : d1342 pattern ≤ (2 : Int) + d1304 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1342, d1304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20567 pattern childGuard
    simpa only [d1342, d1304, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1342, d1304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d1342, d1304, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20569 (pattern : Twelve) (guard : d1 pattern = 1) : d1347 pattern ≤ (2 : Int) + d1628 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1347, d1628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20565 pattern childGuard
    simpa only [d1347, d1628, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1347, d1628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20568 pattern childGuard
    simpa only [d1347, d1628, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20570 (pattern : Twelve) (guard : d1 pattern = 1) : d41 pattern ≤ (2 : Int) + d49 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d41, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20407 pattern childGuard
    simpa only [d41, d49, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d41, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13592 pattern childGuard
    simpa only [d41, d49, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20571 (pattern : Twelve) (guard : d1 pattern = 1) : d40 pattern ≤ (2 : Int) + d49 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d40, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20407 pattern childGuard
    simpa only [d40, d49, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d40, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d40, d49, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20572 (pattern : Twelve) (guard : d1 pattern = 1) : d830 pattern ≤ (2 : Int) + d49 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20570 pattern childGuard
    simpa only [d830, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20571 pattern childGuard
    simpa only [d830, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20573 (pattern : Twelve) (guard : d1 pattern = 1) : d1276 pattern ≤ (2 : Int) + d1277 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1276, d1277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20406 pattern childGuard
    simpa only [d1276, d1277, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1276, d1277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20550 pattern childGuard
    simpa only [d1276, d1277, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20574 (pattern : Twelve) (guard : d1 pattern = 1) : d1330 pattern ≤ (2 : Int) + d1331 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1330, d1331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20573 pattern childGuard
    simpa only [d1330, d1331, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1330, d1331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d1330, d1331, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20575 (pattern : Twelve) (guard : d1 pattern = 1) : d1331 pattern ≤ (2 : Int) + d182 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1331, d182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20562 pattern childGuard
    simpa only [d1331, d182, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1331, d182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d1331, d182, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20576 (pattern : Twelve) (guard : d1 pattern = 1) : d1337 pattern ≤ (2 : Int) + d1621 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1337, d1621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20574 pattern childGuard
    simpa only [d1337, d1621, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1337, d1621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20575 pattern childGuard
    simpa only [d1337, d1621, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20577 (pattern : Twelve) (guard : d1 pattern = 1) : d1343 pattern ≤ (2 : Int) + d1625 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1343, d1625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20572 pattern childGuard
    simpa only [d1343, d1625, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1343, d1625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20576 pattern childGuard
    simpa only [d1343, d1625, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20578 (pattern : Twelve) (guard : d1 pattern = 1) : d1332 pattern ≤ (2 : Int) + d822 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1332, d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20467 pattern childGuard
    simpa only [d1332, d822, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1332, d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20408 pattern childGuard
    simpa only [d1332, d822, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20579 (pattern : Twelve) (guard : d1 pattern = 1) : d1338 pattern ≤ (2 : Int) + d1252 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1338, d1252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20578 pattern childGuard
    simpa only [d1338, d1252, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1338, d1252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20410 pattern childGuard
    simpa only [d1338, d1252, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
