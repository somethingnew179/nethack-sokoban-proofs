/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons082
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c11620 (pattern : Twelve) (guard : d1848 pattern = 1) : d47 pattern ≤ (0 : Int) + d24 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11619 pattern childGuard
    simpa only [d1848, d47, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5033 pattern childGuard
    simpa only [d1848, d47, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11621 (pattern : Twelve) (guard : d1901 pattern = 1) : d836 pattern ≤ (0 : Int) + d24 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1901, d836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11499 pattern childGuard
    simpa only [d1901, d836, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1901, d836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11620 pattern childGuard
    simpa only [d1901, d836, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11622 (pattern : Twelve) (guard : d1901 pattern = 1) : d851 pattern ≤ (0 : Int) + d1950 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d851, d1950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11492 pattern childGuard
    simpa only [d851, d1950, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d851, d1950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11621 pattern childGuard
    simpa only [d851, d1950, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11623 (pattern : Twelve) (guard : d1 pattern = 1) : d4 pattern ≤ (0 : Int) + d5 pattern := by
  change (4 : Int) ≤ (0 : Int) + 5
  decide
theorem c11624 (pattern : Twelve) (guard : d1 pattern = 1) : d4 pattern ≤ (0 : Int) + d15 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2933 pattern childGuard
    simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11623 pattern childGuard
    simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11625 (pattern : Twelve) (guard : d1 pattern = 1) : d4 pattern ≤ (0 : Int) + d24 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2933 pattern childGuard
    simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11624 pattern childGuard
    simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11626 (pattern : Twelve) (guard : d1848 pattern = 1) : d48 pattern ≤ (0 : Int) + d24 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11625 pattern childGuard
    simpa only [d1848, d48, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5033 pattern childGuard
    simpa only [d1848, d48, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11627 (pattern : Twelve) (guard : d1901 pattern = 1) : d837 pattern ≤ (0 : Int) + d24 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1901, d837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11499 pattern childGuard
    simpa only [d1901, d837, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1901, d837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11626 pattern childGuard
    simpa only [d1901, d837, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11628 (pattern : Twelve) (guard : d1901 pattern = 1) : d852 pattern ≤ (0 : Int) + d1965 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d852, d1965, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11627 pattern childGuard
    simpa only [d852, d1965, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d852, d1965, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11591 pattern childGuard
    simpa only [d852, d1965, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11629 (pattern : Twelve) (guard : d1901 pattern = 1) : d860 pattern ≤ (0 : Int) + d1966 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d860, d1966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11622 pattern childGuard
    simpa only [d860, d1966, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d860, d1966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11628 pattern childGuard
    simpa only [d860, d1966, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11630 (pattern : Twelve) (guard : d1901 pattern = 1) : d865 pattern ≤ (0 : Int) + d1967 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d865, d1967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11618 pattern childGuard
    simpa only [d865, d1967, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d865, d1967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11629 pattern childGuard
    simpa only [d865, d1967, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11631 (pattern : Twelve) (guard : d1901 pattern = 1) : d866 pattern ≤ (0 : Int) + d1968 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d866, d1968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11609 pattern childGuard
    simpa only [d866, d1968, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d866, d1968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11508 pattern childGuard
    simpa only [d866, d1968, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11632 (pattern : Twelve) (guard : d1901 pattern = 1) : d868 pattern ≤ (0 : Int) + d1969 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d868, d1969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11630 pattern childGuard
    simpa only [d868, d1969, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d868, d1969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11631 pattern childGuard
    simpa only [d868, d1969, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11633 (pattern : Twelve) (guard : d1901 pattern = 1) : d870 pattern ≤ (0 : Int) + d1974 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d870, d1974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11610 pattern childGuard
    simpa only [d870, d1974, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d870, d1974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11632 pattern childGuard
    simpa only [d870, d1974, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11634 (pattern : Twelve) (guard : d1901 pattern = 1) : d871 pattern ≤ (0 : Int) + d1975 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d871, d1975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11597 pattern childGuard
    simpa only [d871, d1975, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d871, d1975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11633 pattern childGuard
    simpa only [d871, d1975, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11635 (pattern : Twelve) (guard : d0 pattern = 1) : d1278 pattern ≤ (0 : Int) + d872 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11636 (pattern : Twelve) (guard : d1848 pattern = 1) : d872 pattern ≤ (0 : Int) + d872 pattern := by
  omega
theorem c11637 (pattern : Twelve) (guard : d1901 pattern = 1) : d1284 pattern ≤ (0 : Int) + d872 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1901, d1284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11635 pattern childGuard
    simpa only [d1901, d1284, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1901, d1284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11636 pattern childGuard
    simpa only [d1901, d1284, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11638 (pattern : Twelve) (guard : d1901 pattern = 1) : d1293 pattern ≤ (0 : Int) + d1976 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1293, d1976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11558 pattern childGuard
    simpa only [d1293, d1976, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1293, d1976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11637 pattern childGuard
    simpa only [d1293, d1976, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11639 (pattern : Twelve) (guard : d1901 pattern = 1) : d1294 pattern ≤ (0 : Int) + d1294 pattern := by
  omega
theorem c11640 (pattern : Twelve) (guard : d1901 pattern = 1) : d1305 pattern ≤ (0 : Int) + d1977 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1305, d1977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11638 pattern childGuard
    simpa only [d1305, d1977, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1305, d1977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11639 pattern childGuard
    simpa only [d1305, d1977, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11641 (pattern : Twelve) (guard : d0 pattern = 1) : d1279 pattern ≤ (0 : Int) + d1276 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11642 (pattern : Twelve) (guard : d1848 pattern = 1) : d1280 pattern ≤ (0 : Int) + d1276 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d1280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10985 pattern childGuard
    simpa only [d1848, d1280, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d1280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5166 pattern childGuard
    simpa only [d1848, d1280, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11643 (pattern : Twelve) (guard : d1901 pattern = 1) : d1285 pattern ≤ (0 : Int) + d1276 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1901, d1285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11641 pattern childGuard
    simpa only [d1901, d1285, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1901, d1285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11642 pattern childGuard
    simpa only [d1901, d1285, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11644 (pattern : Twelve) (guard : d1901 pattern = 1) : d1295 pattern ≤ (0 : Int) + d1978 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1295, d1978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11568 pattern childGuard
    simpa only [d1295, d1978, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1295, d1978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11643 pattern childGuard
    simpa only [d1295, d1978, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11645 (pattern : Twelve) (guard : d1848 pattern = 1) : d29 pattern ≤ (0 : Int) + d25 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10890 pattern childGuard
    simpa only [d1848, d29, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1105 pattern childGuard
    simpa only [d1848, d29, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11646 (pattern : Twelve) (guard : d1901 pattern = 1) : d1286 pattern ≤ (0 : Int) + d25 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1901, d1286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11559 pattern childGuard
    simpa only [d1901, d1286, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1901, d1286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11645 pattern childGuard
    simpa only [d1901, d1286, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11647 (pattern : Twelve) (guard : d1901 pattern = 1) : d1296 pattern ≤ (0 : Int) + d1650 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1296, d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11646 pattern childGuard
    simpa only [d1296, d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1296, d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11508 pattern childGuard
    simpa only [d1296, d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11648 (pattern : Twelve) (guard : d1901 pattern = 1) : d1306 pattern ≤ (0 : Int) + d1979 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1306, d1979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11644 pattern childGuard
    simpa only [d1306, d1979, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1306, d1979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11647 pattern childGuard
    simpa only [d1306, d1979, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11649 (pattern : Twelve) (guard : d1901 pattern = 1) : d1313 pattern ≤ (0 : Int) + d1980 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1313, d1980, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11640 pattern childGuard
    simpa only [d1313, d1980, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1313, d1980, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11648 pattern childGuard
    simpa only [d1313, d1980, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11650 (pattern : Twelve) (guard : d0 pattern = 1) : d119 pattern ≤ (0 : Int) + d1276 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11651 (pattern : Twelve) (guard : d1848 pattern = 1) : d1281 pattern ≤ (0 : Int) + d1276 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d1281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10985 pattern childGuard
    simpa only [d1848, d1281, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d1281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11650 pattern childGuard
    simpa only [d1848, d1281, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11652 (pattern : Twelve) (guard : d1901 pattern = 1) : d1287 pattern ≤ (0 : Int) + d1276 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1901, d1287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11641 pattern childGuard
    simpa only [d1901, d1287, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1901, d1287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11651 pattern childGuard
    simpa only [d1901, d1287, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11653 (pattern : Twelve) (guard : d1901 pattern = 1) : d1297 pattern ≤ (0 : Int) + d1978 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1297, d1978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11578 pattern childGuard
    simpa only [d1297, d1978, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1297, d1978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11652 pattern childGuard
    simpa only [d1297, d1978, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11654 (pattern : Twelve) (guard : d0 pattern = 1) : d25 pattern ≤ (0 : Int) + d25 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11655 (pattern : Twelve) (guard : d1848 pattern = 1) : d817 pattern ≤ (0 : Int) + d25 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10890 pattern childGuard
    simpa only [d1848, d817, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11654 pattern childGuard
    simpa only [d1848, d817, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11656 (pattern : Twelve) (guard : d1901 pattern = 1) : d817 pattern ≤ (0 : Int) + d25 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11559 pattern childGuard
    simpa only [d1901, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11655 pattern childGuard
    simpa only [d1901, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11657 (pattern : Twelve) (guard : d1901 pattern = 1) : d1298 pattern ≤ (0 : Int) + d1650 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1298, d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11656 pattern childGuard
    simpa only [d1298, d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1298, d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11508 pattern childGuard
    simpa only [d1298, d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11658 (pattern : Twelve) (guard : d1901 pattern = 1) : d1307 pattern ≤ (0 : Int) + d1979 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1307, d1979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11653 pattern childGuard
    simpa only [d1307, d1979, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1307, d1979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11657 pattern childGuard
    simpa only [d1307, d1979, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11659 (pattern : Twelve) (guard : d0 pattern = 1) : d1282 pattern ≤ (0 : Int) + d1277 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11660 (pattern : Twelve) (guard : d1 pattern = 1) : d119 pattern ≤ (0 : Int) + d1277 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d119, d1277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11581 pattern childGuard
    simpa only [d119, d1277, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d119, d1277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10995 pattern childGuard
    simpa only [d119, d1277, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11661 (pattern : Twelve) (guard : d1848 pattern = 1) : d125 pattern ≤ (0 : Int) + d1277 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11660 pattern childGuard
    simpa only [d1848, d125, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5178 pattern childGuard
    simpa only [d1848, d125, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11662 (pattern : Twelve) (guard : d1901 pattern = 1) : d1288 pattern ≤ (0 : Int) + d1277 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1901, d1288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11659 pattern childGuard
    simpa only [d1901, d1288, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1901, d1288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11661 pattern childGuard
    simpa only [d1901, d1288, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11663 (pattern : Twelve) (guard : d1901 pattern = 1) : d1299 pattern ≤ (0 : Int) + d1981 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1299, d1981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11587 pattern childGuard
    simpa only [d1299, d1981, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1299, d1981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11662 pattern childGuard
    simpa only [d1299, d1981, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11664 (pattern : Twelve) (guard : d1848 pattern = 1) : d42 pattern ≤ (0 : Int) + d21 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10948 pattern childGuard
    simpa only [d1848, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5122 pattern childGuard
    simpa only [d1848, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11665 (pattern : Twelve) (guard : d1901 pattern = 1) : d1289 pattern ≤ (0 : Int) + d21 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1901, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11588 pattern childGuard
    simpa only [d1901, d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1901, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11664 pattern childGuard
    simpa only [d1901, d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11666 (pattern : Twelve) (guard : d1901 pattern = 1) : d1300 pattern ≤ (0 : Int) + d1815 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1300, d1815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11665 pattern childGuard
    simpa only [d1300, d1815, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1300, d1815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11508 pattern childGuard
    simpa only [d1300, d1815, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11667 (pattern : Twelve) (guard : d1901 pattern = 1) : d1308 pattern ≤ (0 : Int) + d1982 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1308, d1982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11663 pattern childGuard
    simpa only [d1308, d1982, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1308, d1982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11666 pattern childGuard
    simpa only [d1308, d1982, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11668 (pattern : Twelve) (guard : d1901 pattern = 1) : d1314 pattern ≤ (0 : Int) + d1983 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1314, d1983, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11658 pattern childGuard
    simpa only [d1314, d1983, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1314, d1983, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11667 pattern childGuard
    simpa only [d1314, d1983, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11669 (pattern : Twelve) (guard : d1901 pattern = 1) : d1315 pattern ≤ (0 : Int) + d1984 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1315, d1984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11648 pattern childGuard
    simpa only [d1315, d1984, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1315, d1984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11508 pattern childGuard
    simpa only [d1315, d1984, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11670 (pattern : Twelve) (guard : d1901 pattern = 1) : d1319 pattern ≤ (0 : Int) + d1985 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1319, d1985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11668 pattern childGuard
    simpa only [d1319, d1985, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1319, d1985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11669 pattern childGuard
    simpa only [d1319, d1985, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11671 (pattern : Twelve) (guard : d1901 pattern = 1) : d1321 pattern ≤ (0 : Int) + d1986 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1321, d1986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11649 pattern childGuard
    simpa only [d1321, d1986, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1321, d1986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11670 pattern childGuard
    simpa only [d1321, d1986, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11672 (pattern : Twelve) (guard : d0 pattern = 1) : d1283 pattern ≤ (0 : Int) + d23 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11673 (pattern : Twelve) (guard : d1848 pattern = 1) : d1283 pattern ≤ (0 : Int) + d23 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d1283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10909 pattern childGuard
    simpa only [d1848, d1283, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d1283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11576 pattern childGuard
    simpa only [d1848, d1283, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11674 (pattern : Twelve) (guard : d1901 pattern = 1) : d1283 pattern ≤ (0 : Int) + d23 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11672 pattern childGuard
    simpa only [d1901, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11673 pattern childGuard
    simpa only [d1901, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11675 (pattern : Twelve) (guard : d1901 pattern = 1) : d1301 pattern ≤ (0 : Int) + d1987 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1301, d1987, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11674 pattern childGuard
    simpa only [d1301, d1987, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1301, d1987, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11508 pattern childGuard
    simpa only [d1301, d1987, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11676 (pattern : Twelve) (guard : d1901 pattern = 1) : d1309 pattern ≤ (0 : Int) + d1988 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1309, d1988, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11638 pattern childGuard
    simpa only [d1309, d1988, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1309, d1988, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11675 pattern childGuard
    simpa only [d1309, d1988, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11677 (pattern : Twelve) (guard : d1848 pattern = 1) : d40 pattern ≤ (0 : Int) + d25 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11011 pattern childGuard
    simpa only [d1848, d40, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1105 pattern childGuard
    simpa only [d1848, d40, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11678 (pattern : Twelve) (guard : d1901 pattern = 1) : d1290 pattern ≤ (0 : Int) + d25 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1901, d1290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11559 pattern childGuard
    simpa only [d1901, d1290, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1901, d1290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11677 pattern childGuard
    simpa only [d1901, d1290, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11679 (pattern : Twelve) (guard : d1901 pattern = 1) : d1302 pattern ≤ (0 : Int) + d1650 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1302, d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11678 pattern childGuard
    simpa only [d1302, d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1302, d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11508 pattern childGuard
    simpa only [d1302, d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11680 (pattern : Twelve) (guard : d1901 pattern = 1) : d1310 pattern ≤ (0 : Int) + d1979 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1310, d1979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11644 pattern childGuard
    simpa only [d1310, d1979, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1310, d1979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11679 pattern childGuard
    simpa only [d1310, d1979, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11681 (pattern : Twelve) (guard : d1901 pattern = 1) : d1316 pattern ≤ (0 : Int) + d1989 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1316, d1989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11676 pattern childGuard
    simpa only [d1316, d1989, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1316, d1989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11680 pattern childGuard
    simpa only [d1316, d1989, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11682 (pattern : Twelve) (guard : d0 pattern = 1) : d24 pattern ≤ (0 : Int) + d25 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11683 (pattern : Twelve) (guard : d1848 pattern = 1) : d41 pattern ≤ (0 : Int) + d25 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11011 pattern childGuard
    simpa only [d1848, d41, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11682 pattern childGuard
    simpa only [d1848, d41, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11684 (pattern : Twelve) (guard : d1901 pattern = 1) : d1291 pattern ≤ (0 : Int) + d25 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1901, d1291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11559 pattern childGuard
    simpa only [d1901, d1291, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1901, d1291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11683 pattern childGuard
    simpa only [d1901, d1291, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11685 (pattern : Twelve) (guard : d1901 pattern = 1) : d1303 pattern ≤ (0 : Int) + d1650 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1303, d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11684 pattern childGuard
    simpa only [d1303, d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1303, d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11508 pattern childGuard
    simpa only [d1303, d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11686 (pattern : Twelve) (guard : d1901 pattern = 1) : d1311 pattern ≤ (0 : Int) + d1979 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1311, d1979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11653 pattern childGuard
    simpa only [d1311, d1979, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1311, d1979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11685 pattern childGuard
    simpa only [d1311, d1979, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11687 (pattern : Twelve) (guard : d1 pattern = 1) : d4 pattern ≤ (0 : Int) + d13 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2933 pattern childGuard
    simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10944 pattern childGuard
    simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11688 (pattern : Twelve) (guard : d1 pattern = 1) : d15 pattern ≤ (0 : Int) + d14 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d15, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11623 pattern childGuard
    simpa only [d15, d14, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d15, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10946 pattern childGuard
    simpa only [d15, d14, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11689 (pattern : Twelve) (guard : d1 pattern = 1) : d24 pattern ≤ (0 : Int) + d21 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d24, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11687 pattern childGuard
    simpa only [d24, d21, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d24, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11688 pattern childGuard
    simpa only [d24, d21, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11690 (pattern : Twelve) (guard : d1848 pattern = 1) : d49 pattern ≤ (0 : Int) + d21 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11689 pattern childGuard
    simpa only [d1848, d49, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5122 pattern childGuard
    simpa only [d1848, d49, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11691 (pattern : Twelve) (guard : d1901 pattern = 1) : d1292 pattern ≤ (0 : Int) + d21 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1901, d1292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11588 pattern childGuard
    simpa only [d1901, d1292, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1901, d1292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11690 pattern childGuard
    simpa only [d1901, d1292, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11692 (pattern : Twelve) (guard : d1901 pattern = 1) : d1304 pattern ≤ (0 : Int) + d1815 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1304, d1815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11691 pattern childGuard
    simpa only [d1304, d1815, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1304, d1815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11508 pattern childGuard
    simpa only [d1304, d1815, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11693 (pattern : Twelve) (guard : d1901 pattern = 1) : d1312 pattern ≤ (0 : Int) + d1982 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1312, d1982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11663 pattern childGuard
    simpa only [d1312, d1982, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1312, d1982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11692 pattern childGuard
    simpa only [d1312, d1982, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11694 (pattern : Twelve) (guard : d1901 pattern = 1) : d1317 pattern ≤ (0 : Int) + d1983 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1317, d1983, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11686 pattern childGuard
    simpa only [d1317, d1983, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1317, d1983, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11693 pattern childGuard
    simpa only [d1317, d1983, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11695 (pattern : Twelve) (guard : d1901 pattern = 1) : d1318 pattern ≤ (0 : Int) + d1984 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1318, d1984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11680 pattern childGuard
    simpa only [d1318, d1984, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1318, d1984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11508 pattern childGuard
    simpa only [d1318, d1984, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11696 (pattern : Twelve) (guard : d1901 pattern = 1) : d1320 pattern ≤ (0 : Int) + d1985 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1320, d1985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11694 pattern childGuard
    simpa only [d1320, d1985, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1320, d1985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11695 pattern childGuard
    simpa only [d1320, d1985, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11697 (pattern : Twelve) (guard : d1901 pattern = 1) : d1322 pattern ≤ (0 : Int) + d1990 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1322, d1990, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11681 pattern childGuard
    simpa only [d1322, d1990, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1322, d1990, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11696 pattern childGuard
    simpa only [d1322, d1990, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11698 (pattern : Twelve) (guard : d1901 pattern = 1) : d1323 pattern ≤ (0 : Int) + d1991 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1323, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11671 pattern childGuard
    simpa only [d1323, d1991, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1323, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11697 pattern childGuard
    simpa only [d1323, d1991, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11699 (pattern : Twelve) (guard : d1901 pattern = 1) : d1656 pattern ≤ (0 : Int) + d1656 pattern := by
  omega
theorem c11700 (pattern : Twelve) (guard : d0 pattern = 1) : d1644 pattern ≤ (0 : Int) + d20 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11701 (pattern : Twelve) (guard : d1848 pattern = 1) : d1645 pattern ≤ (0 : Int) + d20 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d1645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11026 pattern childGuard
    simpa only [d1848, d1645, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d1645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5218 pattern childGuard
    simpa only [d1848, d1645, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11702 (pattern : Twelve) (guard : d1901 pattern = 1) : d1647 pattern ≤ (0 : Int) + d20 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1901, d1647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11700 pattern childGuard
    simpa only [d1901, d1647, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1901, d1647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11701 pattern childGuard
    simpa only [d1901, d1647, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11703 (pattern : Twelve) (guard : d1901 pattern = 1) : d1651 pattern ≤ (0 : Int) + d1814 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1651, d1814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11646 pattern childGuard
    simpa only [d1651, d1814, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1651, d1814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11702 pattern childGuard
    simpa only [d1651, d1814, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11704 (pattern : Twelve) (guard : d1901 pattern = 1) : d1657 pattern ≤ (0 : Int) + d1818 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1657, d1818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11703 pattern childGuard
    simpa only [d1657, d1818, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1657, d1818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11666 pattern childGuard
    simpa only [d1657, d1818, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11705 (pattern : Twelve) (guard : d1901 pattern = 1) : d1660 pattern ≤ (0 : Int) + d1992 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1660, d1992, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11699 pattern childGuard
    simpa only [d1660, d1992, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1660, d1992, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11704 pattern childGuard
    simpa only [d1660, d1992, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11706 (pattern : Twelve) (guard : d0 pattern = 1) : d20 pattern ≤ (0 : Int) + d20 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11707 (pattern : Twelve) (guard : d1848 pattern = 1) : d1644 pattern ≤ (0 : Int) + d20 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11026 pattern childGuard
    simpa only [d1848, d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11706 pattern childGuard
    simpa only [d1848, d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11708 (pattern : Twelve) (guard : d1901 pattern = 1) : d1644 pattern ≤ (0 : Int) + d20 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11700 pattern childGuard
    simpa only [d1901, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11707 pattern childGuard
    simpa only [d1901, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11709 (pattern : Twelve) (guard : d1901 pattern = 1) : d1652 pattern ≤ (0 : Int) + d1814 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1652, d1814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11656 pattern childGuard
    simpa only [d1652, d1814, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1652, d1814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11708 pattern childGuard
    simpa only [d1652, d1814, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11710 (pattern : Twelve) (guard : d0 pattern = 1) : d21 pattern ≤ (0 : Int) + d21 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11711 (pattern : Twelve) (guard : d1848 pattern = 1) : d821 pattern ≤ (0 : Int) + d21 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10948 pattern childGuard
    simpa only [d1848, d821, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11710 pattern childGuard
    simpa only [d1848, d821, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11712 (pattern : Twelve) (guard : d1901 pattern = 1) : d821 pattern ≤ (0 : Int) + d21 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11588 pattern childGuard
    simpa only [d1901, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11711 pattern childGuard
    simpa only [d1901, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11713 (pattern : Twelve) (guard : d1901 pattern = 1) : d1653 pattern ≤ (0 : Int) + d1815 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1653, d1815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11712 pattern childGuard
    simpa only [d1653, d1815, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1653, d1815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11508 pattern childGuard
    simpa only [d1653, d1815, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11714 (pattern : Twelve) (guard : d1901 pattern = 1) : d1658 pattern ≤ (0 : Int) + d1818 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1658, d1818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11709 pattern childGuard
    simpa only [d1658, d1818, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1658, d1818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11713 pattern childGuard
    simpa only [d1658, d1818, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11715 (pattern : Twelve) (guard : d0 pattern = 1) : d1646 pattern ≤ (0 : Int) + d22 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11716 (pattern : Twelve) (guard : d1848 pattern = 1) : d128 pattern ≤ (0 : Int) + d22 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11033 pattern childGuard
    simpa only [d1848, d128, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5224 pattern childGuard
    simpa only [d1848, d128, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11717 (pattern : Twelve) (guard : d1901 pattern = 1) : d1648 pattern ≤ (0 : Int) + d22 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1901, d1648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11715 pattern childGuard
    simpa only [d1901, d1648, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1901, d1648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11716 pattern childGuard
    simpa only [d1901, d1648, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11718 (pattern : Twelve) (guard : d1901 pattern = 1) : d1654 pattern ≤ (0 : Int) + d1993 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1654, d1993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11665 pattern childGuard
    simpa only [d1654, d1993, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1654, d1993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11717 pattern childGuard
    simpa only [d1654, d1993, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11719 (pattern : Twelve) (guard : d1848 pattern = 1) : d822 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11039 pattern childGuard
    simpa only [d1848, d822, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d1848, d822, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11720 (pattern : Twelve) (guard : d1901 pattern = 1) : d822 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c279 pattern childGuard
    simpa only [d1901, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11719 pattern childGuard
    simpa only [d1901, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11721 (pattern : Twelve) (guard : d1901 pattern = 1) : d1655 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11720 pattern childGuard
    simpa only [d1655, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11508 pattern childGuard
    simpa only [d1655, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11722 (pattern : Twelve) (guard : d1901 pattern = 1) : d1659 pattern ≤ (0 : Int) + d1994 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1659, d1994, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11718 pattern childGuard
    simpa only [d1659, d1994, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1659, d1994, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11721 pattern childGuard
    simpa only [d1659, d1994, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11723 (pattern : Twelve) (guard : d1901 pattern = 1) : d1661 pattern ≤ (0 : Int) + d1995 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1661, d1995, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11714 pattern childGuard
    simpa only [d1661, d1995, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1661, d1995, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11722 pattern childGuard
    simpa only [d1661, d1995, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11724 (pattern : Twelve) (guard : d1901 pattern = 1) : d1662 pattern ≤ (0 : Int) + d1996 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1662, d1996, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11704 pattern childGuard
    simpa only [d1662, d1996, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1662, d1996, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11508 pattern childGuard
    simpa only [d1662, d1996, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11725 (pattern : Twelve) (guard : d1901 pattern = 1) : d1663 pattern ≤ (0 : Int) + d1997 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1663, d1997, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11723 pattern childGuard
    simpa only [d1663, d1997, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1663, d1997, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11724 pattern childGuard
    simpa only [d1663, d1997, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11726 (pattern : Twelve) (guard : d1901 pattern = 1) : d1664 pattern ≤ (0 : Int) + d1998 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1664, d1998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11705 pattern childGuard
    simpa only [d1664, d1998, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1664, d1998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11725 pattern childGuard
    simpa only [d1664, d1998, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11727 (pattern : Twelve) (guard : d0 pattern = 1) : d425 pattern ≤ (1 : Int) + d838 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11728 (pattern : Twelve) (guard : d0 pattern = 1) : d186 pattern ≤ (1 : Int) + d824 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11729 (pattern : Twelve) (guard : d1852 pattern = 1) : d426 pattern ≤ (1 : Int) + d838 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d426, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11049 pattern childGuard
    simpa only [d1852, d426, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d426, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11728 pattern childGuard
    simpa only [d1852, d426, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11730 (pattern : Twelve) (guard : d1999 pattern = 1) : d444 pattern ≤ (1 : Int) + d838 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1999, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11727 pattern childGuard
    simpa only [d1999, d444, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1999, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11729 pattern childGuard
    simpa only [d1999, d444, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11731 (pattern : Twelve) (guard : d0 pattern = 1) : d427 pattern ≤ (1 : Int) + d840 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11732 (pattern : Twelve) (guard : d1 pattern = 1) : d30 pattern ≤ (1 : Int) + d30 pattern := by
  omega
theorem c11733 (pattern : Twelve) (guard : d1 pattern = 1) : d33 pattern ≤ (1 : Int) + d35 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d33, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11049 pattern childGuard
    simpa only [d33, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d33, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11431 pattern childGuard
    simpa only [d33, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11734 (pattern : Twelve) (guard : d1 pattern = 1) : d54 pattern ≤ (1 : Int) + d56 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d54, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11732 pattern childGuard
    simpa only [d54, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d54, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11733 pattern childGuard
    simpa only [d54, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11735 (pattern : Twelve) (guard : d0 pattern = 1) : d189 pattern ≤ (1 : Int) + d826 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11736 (pattern : Twelve) (guard : d1852 pattern = 1) : d428 pattern ≤ (1 : Int) + d840 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d428, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11734 pattern childGuard
    simpa only [d1852, d428, d840, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d428, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11735 pattern childGuard
    simpa only [d1852, d428, d840, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11737 (pattern : Twelve) (guard : d1999 pattern = 1) : d445 pattern ≤ (1 : Int) + d840 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1999, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11731 pattern childGuard
    simpa only [d1999, d445, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1999, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11736 pattern childGuard
    simpa only [d1999, d445, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11738 (pattern : Twelve) (guard : d1999 pattern = 1) : d455 pattern ≤ (1 : Int) + d2000 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1999 pattern = 1 := by simpa only [d455, d2000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11730 pattern childGuard
    simpa only [d455, d2000, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1999 pattern = 1 := by simpa only [d455, d2000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11737 pattern childGuard
    simpa only [d455, d2000, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11739 (pattern : Twelve) (guard : d0 pattern = 1) : d429 pattern ≤ (1 : Int) + d838 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11740 (pattern : Twelve) (guard : d0 pattern = 1) : d189 pattern ≤ (1 : Int) + d824 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11741 (pattern : Twelve) (guard : d1852 pattern = 1) : d430 pattern ≤ (1 : Int) + d838 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d430, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11049 pattern childGuard
    simpa only [d1852, d430, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d430, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11740 pattern childGuard
    simpa only [d1852, d430, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11742 (pattern : Twelve) (guard : d1999 pattern = 1) : d446 pattern ≤ (1 : Int) + d838 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1999, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11739 pattern childGuard
    simpa only [d1999, d446, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1999, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11741 pattern childGuard
    simpa only [d1999, d446, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11743 (pattern : Twelve) (guard : d0 pattern = 1) : d431 pattern ≤ (1 : Int) + d840 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11744 (pattern : Twelve) (guard : d1 pattern = 1) : d56 pattern ≤ (1 : Int) + d56 pattern := by
  omega
theorem c11745 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (1 : Int) + d826 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11746 (pattern : Twelve) (guard : d1852 pattern = 1) : d432 pattern ≤ (1 : Int) + d840 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d432, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11744 pattern childGuard
    simpa only [d1852, d432, d840, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d432, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11745 pattern childGuard
    simpa only [d1852, d432, d840, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11747 (pattern : Twelve) (guard : d1999 pattern = 1) : d447 pattern ≤ (1 : Int) + d840 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1999, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11743 pattern childGuard
    simpa only [d1999, d447, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1999, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11746 pattern childGuard
    simpa only [d1999, d447, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11748 (pattern : Twelve) (guard : d1999 pattern = 1) : d456 pattern ≤ (1 : Int) + d2000 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1999 pattern = 1 := by simpa only [d456, d2000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11742 pattern childGuard
    simpa only [d456, d2000, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1999 pattern = 1 := by simpa only [d456, d2000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11747 pattern childGuard
    simpa only [d456, d2000, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11749 (pattern : Twelve) (guard : d1999 pattern = 1) : d465 pattern ≤ (1 : Int) + d2000 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1999 pattern = 1 := by simpa only [d465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11738 pattern childGuard
    simpa only [d465, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1999 pattern = 1 := by simpa only [d465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11748 pattern childGuard
    simpa only [d465, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11750 (pattern : Twelve) (guard : d0 pattern = 1) : d433 pattern ≤ (1 : Int) + d842 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11751 (pattern : Twelve) (guard : d0 pattern = 1) : d194 pattern ≤ (1 : Int) + d828 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11752 (pattern : Twelve) (guard : d1852 pattern = 1) : d434 pattern ≤ (1 : Int) + d842 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d434, d842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11732 pattern childGuard
    simpa only [d1852, d434, d842, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d434, d842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11751 pattern childGuard
    simpa only [d1852, d434, d842, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11753 (pattern : Twelve) (guard : d1999 pattern = 1) : d448 pattern ≤ (1 : Int) + d842 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1999, d448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11750 pattern childGuard
    simpa only [d1999, d448, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1999, d448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11752 pattern childGuard
    simpa only [d1999, d448, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11754 (pattern : Twelve) (guard : d0 pattern = 1) : d435 pattern ≤ (1 : Int) + d844 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11755 (pattern : Twelve) (guard : d1 pattern = 1) : d59 pattern ≤ (1 : Int) + d59 pattern := by
  omega
theorem c11756 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (1 : Int) + d829 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11757 (pattern : Twelve) (guard : d1852 pattern = 1) : d436 pattern ≤ (1 : Int) + d844 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d436, d844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11755 pattern childGuard
    simpa only [d1852, d436, d844, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d436, d844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11756 pattern childGuard
    simpa only [d1852, d436, d844, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11758 (pattern : Twelve) (guard : d1999 pattern = 1) : d449 pattern ≤ (1 : Int) + d844 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1999, d449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11754 pattern childGuard
    simpa only [d1999, d449, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1999, d449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11757 pattern childGuard
    simpa only [d1999, d449, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11759 (pattern : Twelve) (guard : d1999 pattern = 1) : d457 pattern ≤ (1 : Int) + d2001 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1999 pattern = 1 := by simpa only [d457, d2001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11753 pattern childGuard
    simpa only [d457, d2001, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1999 pattern = 1 := by simpa only [d457, d2001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11758 pattern childGuard
    simpa only [d457, d2001, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
