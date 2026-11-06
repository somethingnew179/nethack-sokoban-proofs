/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Comparisons048
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare6860 (p : Pattern) (guard : d1506 p = 1) : d648 p ≤ (0 : Int) + d1546 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d648, d1546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6833 p hg
    simpa only [d648, d1546, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d648, d1546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6773 p hg
    simpa only [d648, d1546, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6861 (p : Pattern) (guard : d1506 p = 1) : d649 p ≤ (0 : Int) + d1547 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d649, d1547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6859 p hg
    simpa only [d649, d1547, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d649, d1547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6860 p hg
    simpa only [d649, d1547, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6862 (p : Pattern) (guard : d1506 p = 1) : d650 p ≤ (0 : Int) + d1548 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d650, d1548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6858 p hg
    simpa only [d650, d1548, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d650, d1548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6861 p hg
    simpa only [d650, d1548, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6863 (p : Pattern) (guard : d1506 p = 1) : d651 p ≤ (0 : Int) + d1549 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d651, d1549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6849 p hg
    simpa only [d651, d1549, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d651, d1549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6862 p hg
    simpa only [d651, d1549, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6864 (p : Pattern) (guard : d1506 p = 1) : d652 p ≤ (0 : Int) + d1550 p := by
  cases selected : p 80 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d652, d1550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6837 p hg
    simpa only [d652, d1550, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d652, d1550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6863 p hg
    simpa only [d652, d1550, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6865 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d32 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6866 (p : Pattern) (guard : d873 p = 1) : d551 p ≤ (0 : Int) + d33 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d873, d551, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2369 p hg
    simpa only [d873, d551, d33, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d873, d551, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6865 p hg
    simpa only [d873, d551, d33, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6867 (p : Pattern) (guard : d873 p = 1) : d552 p ≤ (0 : Int) + d34 p := by
  cases selected : p 139 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d552, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6866 p hg
    simpa only [d552, d34, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d552, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6388 p hg
    simpa only [d552, d34, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6868 (p : Pattern) (guard : d873 p = 1) : d553 p ≤ (0 : Int) + d35 p := by
  cases selected : p 138 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d553, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6866 p hg
    simpa only [d553, d35, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d553, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6867 p hg
    simpa only [d553, d35, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6869 (p : Pattern) (guard : d873 p = 1) : d554 p ≤ (0 : Int) + d36 p := by
  cases selected : p 134 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d554, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6382 p hg
    simpa only [d554, d36, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d554, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6868 p hg
    simpa only [d554, d36, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6870 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d37 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6871 (p : Pattern) (guard : d873 p = 1) : d539 p ≤ (0 : Int) + d38 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d873, d539, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2347 p hg
    simpa only [d873, d539, d38, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d873, d539, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6870 p hg
    simpa only [d873, d539, d38, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6872 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d39 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6873 (p : Pattern) (guard : d873 p = 1) : d540 p ≤ (0 : Int) + d40 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d873, d540, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2352 p hg
    simpa only [d873, d540, d40, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d873, d540, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6872 p hg
    simpa only [d873, d540, d40, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6874 (p : Pattern) (guard : d873 p = 1) : d541 p ≤ (0 : Int) + d41 p := by
  cases selected : p 139 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d541, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6871 p hg
    simpa only [d541, d41, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d541, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6873 p hg
    simpa only [d541, d41, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6875 (p : Pattern) (guard : d873 p = 1) : d543 p ≤ (0 : Int) + d42 p := by
  cases selected : p 138 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d543, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6871 p hg
    simpa only [d543, d42, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d543, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6874 p hg
    simpa only [d543, d42, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6876 (p : Pattern) (guard : d873 p = 1) : d549 p ≤ (0 : Int) + d43 p := by
  cases selected : p 134 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d549, d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6875 p hg
    simpa only [d549, d43, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d549, d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6390 p hg
    simpa only [d549, d43, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6877 (p : Pattern) (guard : d873 p = 1) : d555 p ≤ (0 : Int) + d44 p := by
  cases selected : p 133 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d555, d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6869 p hg
    simpa only [d555, d44, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d555, d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6876 p hg
    simpa only [d555, d44, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6878 (p : Pattern) (guard : d873 p = 1) : d556 p ≤ (0 : Int) + d45 p := by
  cases selected : p 132 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d556, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6392 p hg
    simpa only [d556, d45, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d556, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6877 p hg
    simpa only [d556, d45, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6879 (p : Pattern) (guard : d873 p = 1) : d559 p ≤ (0 : Int) + d48 p := by
  cases selected : p 134 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d559, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6381 p hg
    simpa only [d559, d48, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d559, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6867 p hg
    simpa only [d559, d48, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6880 (p : Pattern) (guard : d873 p = 1) : d557 p ≤ (0 : Int) + d49 p := by
  cases selected : p 134 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d557, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6874 p hg
    simpa only [d557, d49, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d557, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6389 p hg
    simpa only [d557, d49, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6881 (p : Pattern) (guard : d873 p = 1) : d560 p ≤ (0 : Int) + d50 p := by
  cases selected : p 133 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d560, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6879 p hg
    simpa only [d560, d50, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d560, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6880 p hg
    simpa only [d560, d50, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6882 (p : Pattern) (guard : d873 p = 1) : d561 p ≤ (0 : Int) + d51 p := by
  cases selected : p 132 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d561, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6396 p hg
    simpa only [d561, d51, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d561, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6881 p hg
    simpa only [d561, d51, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6883 (p : Pattern) (guard : d873 p = 1) : d568 p ≤ (0 : Int) + d58 p := by
  cases selected : p 139 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d568, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6866 p hg
    simpa only [d568, d58, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d568, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare715 p hg
    simpa only [d568, d58, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6884 (p : Pattern) (guard : d873 p = 1) : d569 p ≤ (0 : Int) + d59 p := by
  cases selected : p 138 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d569, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6867 p hg
    simpa only [d569, d59, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d569, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6883 p hg
    simpa only [d569, d59, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6885 (p : Pattern) (guard : d873 p = 1) : d570 p ≤ (0 : Int) + d60 p := by
  cases selected : p 134 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d570, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6400 p hg
    simpa only [d570, d60, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d570, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6884 p hg
    simpa only [d570, d60, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6886 (p : Pattern) (guard : d873 p = 1) : d562 p ≤ (0 : Int) + d61 p := by
  cases selected : p 139 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d562, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6871 p hg
    simpa only [d562, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d562, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare715 p hg
    simpa only [d562, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6887 (p : Pattern) (guard : d873 p = 1) : d563 p ≤ (0 : Int) + d62 p := by
  cases selected : p 138 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d563, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6874 p hg
    simpa only [d563, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d563, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6886 p hg
    simpa only [d563, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6888 (p : Pattern) (guard : d873 p = 1) : d566 p ≤ (0 : Int) + d63 p := by
  cases selected : p 134 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d566, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6887 p hg
    simpa only [d566, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d566, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6402 p hg
    simpa only [d566, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6889 (p : Pattern) (guard : d873 p = 1) : d571 p ≤ (0 : Int) + d64 p := by
  cases selected : p 133 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d571, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6885 p hg
    simpa only [d571, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d571, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6888 p hg
    simpa only [d571, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6890 (p : Pattern) (guard : d873 p = 1) : d572 p ≤ (0 : Int) + d65 p := by
  cases selected : p 132 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d572, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6404 p hg
    simpa only [d572, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d572, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6889 p hg
    simpa only [d572, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6891 (p : Pattern) (guard : d873 p = 1) : d573 p ≤ (0 : Int) + d66 p := by
  cases selected : p 113 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d573, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6882 p hg
    simpa only [d573, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d573, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6890 p hg
    simpa only [d573, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6892 (p : Pattern) (guard : d873 p = 1) : d574 p ≤ (0 : Int) + d67 p := by
  cases selected : p 112 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d574, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6878 p hg
    simpa only [d574, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d574, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6891 p hg
    simpa only [d574, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6893 (p : Pattern) (guard : d873 p = 1) : d575 p ≤ (0 : Int) + d27 p := by
  cases selected : p 134 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d575, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6382 p hg
    simpa only [d575, d27, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d575, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6390 p hg
    simpa only [d575, d27, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6894 (p : Pattern) (guard : d873 p = 1) : d576 p ≤ (0 : Int) + d68 p := by
  cases selected : p 139 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d576, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6873 p hg
    simpa only [d576, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d576, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare715 p hg
    simpa only [d576, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6895 (p : Pattern) (guard : d873 p = 1) : d577 p ≤ (0 : Int) + d69 p := by
  cases selected : p 138 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d577, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6873 p hg
    simpa only [d577, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d577, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6894 p hg
    simpa only [d577, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6896 (p : Pattern) (guard : d873 p = 1) : d580 p ≤ (0 : Int) + d72 p := by
  cases selected : p 134 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d580, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6895 p hg
    simpa only [d580, d72, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d580, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6433 p hg
    simpa only [d580, d72, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6897 (p : Pattern) (guard : d873 p = 1) : d581 p ≤ (0 : Int) + d73 p := by
  cases selected : p 133 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d581, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6893 p hg
    simpa only [d581, d73, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d581, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6896 p hg
    simpa only [d581, d73, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6898 (p : Pattern) (guard : d873 p = 1) : d582 p ≤ (0 : Int) + d74 p := by
  cases selected : p 132 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d582, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6392 p hg
    simpa only [d582, d74, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d582, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6897 p hg
    simpa only [d582, d74, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6899 (p : Pattern) (guard : d873 p = 1) : d585 p ≤ (0 : Int) + d27 p := by
  cases selected : p 134 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d585, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6466 p hg
    simpa only [d585, d27, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d585, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6390 p hg
    simpa only [d585, d27, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6900 (p : Pattern) (guard : d873 p = 1) : d586 p ≤ (0 : Int) + d75 p := by
  cases selected : p 134 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d586, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6894 p hg
    simpa only [d586, d75, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d586, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6432 p hg
    simpa only [d586, d75, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6901 (p : Pattern) (guard : d873 p = 1) : d587 p ≤ (0 : Int) + d76 p := by
  cases selected : p 133 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d587, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6899 p hg
    simpa only [d587, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d587, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6900 p hg
    simpa only [d587, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6902 (p : Pattern) (guard : d873 p = 1) : d588 p ≤ (0 : Int) + d77 p := by
  cases selected : p 132 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d588, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6392 p hg
    simpa only [d588, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d588, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6901 p hg
    simpa only [d588, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6903 (p : Pattern) (guard : d873 p = 1) : d589 p ≤ (0 : Int) + d78 p := by
  cases selected : p 113 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d589, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6898 p hg
    simpa only [d589, d78, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d589, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6902 p hg
    simpa only [d589, d78, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6904 (p : Pattern) (guard : d873 p = 1) : d590 p ≤ (0 : Int) + d79 p := by
  cases selected : p 133 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d590, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6395 p hg
    simpa only [d590, d79, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d590, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6900 p hg
    simpa only [d590, d79, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6905 (p : Pattern) (guard : d873 p = 1) : d591 p ≤ (0 : Int) + d80 p := by
  cases selected : p 132 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d591, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6396 p hg
    simpa only [d591, d80, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d591, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6904 p hg
    simpa only [d591, d80, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6906 (p : Pattern) (guard : d873 p = 1) : d592 p ≤ (0 : Int) + d81 p := by
  cases selected : p 133 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d592, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6403 p hg
    simpa only [d592, d81, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d592, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6900 p hg
    simpa only [d592, d81, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6907 (p : Pattern) (guard : d873 p = 1) : d593 p ≤ (0 : Int) + d82 p := by
  cases selected : p 132 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d593, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6404 p hg
    simpa only [d593, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d593, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6906 p hg
    simpa only [d593, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6908 (p : Pattern) (guard : d873 p = 1) : d594 p ≤ (0 : Int) + d83 p := by
  cases selected : p 113 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d594, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6905 p hg
    simpa only [d594, d83, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d594, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6907 p hg
    simpa only [d594, d83, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6909 (p : Pattern) (guard : d873 p = 1) : d595 p ≤ (0 : Int) + d84 p := by
  cases selected : p 112 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d595, d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6903 p hg
    simpa only [d595, d84, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d595, d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6908 p hg
    simpa only [d595, d84, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6910 (p : Pattern) (guard : d873 p = 1) : d596 p ≤ (0 : Int) + d85 p := by
  cases selected : p 106 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d596, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6892 p hg
    simpa only [d596, d85, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d596, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6909 p hg
    simpa only [d596, d85, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6911 (p : Pattern) (guard : d873 p = 1) : d604 p ≤ (0 : Int) + d90 p := by
  cases selected : p 138 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d604, d90, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6866 p hg
    simpa only [d604, d90, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d604, d90, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6883 p hg
    simpa only [d604, d90, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6912 (p : Pattern) (guard : d873 p = 1) : d605 p ≤ (0 : Int) + d91 p := by
  cases selected : p 134 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d605, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6443 p hg
    simpa only [d605, d91, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d605, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6911 p hg
    simpa only [d605, d91, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6913 (p : Pattern) (guard : d873 p = 1) : d598 p ≤ (0 : Int) + d92 p := by
  cases selected : p 138 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d598, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6871 p hg
    simpa only [d598, d92, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d598, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6886 p hg
    simpa only [d598, d92, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6914 (p : Pattern) (guard : d873 p = 1) : d601 p ≤ (0 : Int) + d93 p := by
  cases selected : p 134 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d601, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6913 p hg
    simpa only [d601, d93, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d601, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6424 p hg
    simpa only [d601, d93, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6915 (p : Pattern) (guard : d873 p = 1) : d606 p ≤ (0 : Int) + d94 p := by
  cases selected : p 133 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d606, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6912 p hg
    simpa only [d606, d94, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d606, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6914 p hg
    simpa only [d606, d94, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6916 (p : Pattern) (guard : d873 p = 1) : d607 p ≤ (0 : Int) + d95 p := by
  cases selected : p 132 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d607, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6426 p hg
    simpa only [d607, d95, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d607, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6915 p hg
    simpa only [d607, d95, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6917 (p : Pattern) (guard : d873 p = 1) : d608 p ≤ (0 : Int) + d96 p := by
  cases selected : p 113 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d608, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6878 p hg
    simpa only [d608, d96, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d608, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6916 p hg
    simpa only [d608, d96, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6918 (p : Pattern) (guard : d873 p = 1) : d580 p ≤ (0 : Int) + d101 p := by
  cases selected : p 133 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6434 p hg
    simpa only [d101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6896 p hg
    simpa only [d101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6919 (p : Pattern) (guard : d873 p = 1) : d610 p ≤ (0 : Int) + d102 p := by
  cases selected : p 132 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d610, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6435 p hg
    simpa only [d610, d102, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d610, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6918 p hg
    simpa only [d610, d102, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6920 (p : Pattern) (guard : d873 p = 1) : d611 p ≤ (0 : Int) + d103 p := by
  cases selected : p 112 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d611, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6917 p hg
    simpa only [d611, d103, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d611, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6919 p hg
    simpa only [d611, d103, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6921 (p : Pattern) (guard : d873 p = 1) : d614 p ≤ (0 : Int) + d104 p := by
  cases selected : p 133 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d614, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6425 p hg
    simpa only [d614, d104, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d614, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6900 p hg
    simpa only [d614, d104, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6922 (p : Pattern) (guard : d873 p = 1) : d615 p ≤ (0 : Int) + d105 p := by
  cases selected : p 132 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d615, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6445 p hg
    simpa only [d615, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d615, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6921 p hg
    simpa only [d615, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6923 (p : Pattern) (guard : d873 p = 1) : d616 p ≤ (0 : Int) + d106 p := by
  cases selected : p 113 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d616, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6902 p hg
    simpa only [d616, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d616, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6922 p hg
    simpa only [d616, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6924 (p : Pattern) (guard : d873 p = 1) : d617 p ≤ (0 : Int) + d107 p := by
  cases selected : p 133 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d617, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6434 p hg
    simpa only [d617, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d617, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare715 p hg
    simpa only [d617, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6925 (p : Pattern) (guard : d873 p = 1) : d618 p ≤ (0 : Int) + d108 p := by
  cases selected : p 132 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d618, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6435 p hg
    simpa only [d618, d108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d618, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6924 p hg
    simpa only [d618, d108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6926 (p : Pattern) (guard : d873 p = 1) : d620 p ≤ (0 : Int) + d111 p := by
  cases selected : p 133 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d620, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6451 p hg
    simpa only [d620, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d620, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare715 p hg
    simpa only [d620, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6927 (p : Pattern) (guard : d873 p = 1) : d621 p ≤ (0 : Int) + d112 p := by
  cases selected : p 132 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d621, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6452 p hg
    simpa only [d621, d112, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d621, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6926 p hg
    simpa only [d621, d112, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6928 (p : Pattern) (guard : d873 p = 1) : d622 p ≤ (0 : Int) + d113 p := by
  cases selected : p 113 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d622, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6925 p hg
    simpa only [d622, d113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d622, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6927 p hg
    simpa only [d622, d113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6929 (p : Pattern) (guard : d873 p = 1) : d623 p ≤ (0 : Int) + d114 p := by
  cases selected : p 112 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d623, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6923 p hg
    simpa only [d623, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d623, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6928 p hg
    simpa only [d623, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6930 (p : Pattern) (guard : d873 p = 1) : d624 p ≤ (0 : Int) + d115 p := by
  cases selected : p 106 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d624, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6920 p hg
    simpa only [d624, d115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d624, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6929 p hg
    simpa only [d624, d115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6931 (p : Pattern) (guard : d873 p = 1) : d625 p ≤ (0 : Int) + d116 p := by
  cases selected : p 86 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d625, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6910 p hg
    simpa only [d625, d116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d625, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6930 p hg
    simpa only [d625, d116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6932 (p : Pattern) (guard : d873 p = 1) : d626 p ≤ (0 : Int) + d36 p := by
  cases selected : p 134 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d626, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6466 p hg
    simpa only [d626, d36, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d626, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6868 p hg
    simpa only [d626, d36, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6933 (p : Pattern) (guard : d873 p = 1) : d627 p ≤ (0 : Int) + d44 p := by
  cases selected : p 133 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d627, d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6932 p hg
    simpa only [d627, d44, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d627, d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6876 p hg
    simpa only [d627, d44, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6934 (p : Pattern) (guard : d873 p = 1) : d628 p ≤ (0 : Int) + d45 p := by
  cases selected : p 132 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d628, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6392 p hg
    simpa only [d628, d45, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d628, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6933 p hg
    simpa only [d628, d45, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6935 (p : Pattern) (guard : d873 p = 1) : d629 p ≤ (0 : Int) + d45 p := by
  cases selected : p 113 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6878 p hg
    simpa only [d629, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6934 p hg
    simpa only [d629, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6936 (p : Pattern) (guard : d873 p = 1) : d630 p ≤ (0 : Int) + d67 p := by
  cases selected : p 112 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d630, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6935 p hg
    simpa only [d630, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d630, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6891 p hg
    simpa only [d630, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6937 (p : Pattern) (guard : d873 p = 1) : d633 p ≤ (0 : Int) + d76 p := by
  cases selected : p 133 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d633, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6391 p hg
    simpa only [d633, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d633, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6900 p hg
    simpa only [d633, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6938 (p : Pattern) (guard : d873 p = 1) : d634 p ≤ (0 : Int) + d77 p := by
  cases selected : p 132 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d634, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6468 p hg
    simpa only [d634, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d634, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6937 p hg
    simpa only [d634, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6939 (p : Pattern) (guard : d873 p = 1) : d635 p ≤ (0 : Int) + d77 p := by
  cases selected : p 113 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6902 p hg
    simpa only [d635, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6938 p hg
    simpa only [d635, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6940 (p : Pattern) (guard : d873 p = 1) : d636 p ≤ (0 : Int) + d117 p := by
  cases selected : p 112 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d636, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6939 p hg
    simpa only [d636, d117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d636, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6908 p hg
    simpa only [d636, d117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6941 (p : Pattern) (guard : d873 p = 1) : d637 p ≤ (0 : Int) + d118 p := by
  cases selected : p 106 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d637, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6936 p hg
    simpa only [d637, d118, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d637, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6940 p hg
    simpa only [d637, d118, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6942 (p : Pattern) (guard : d873 p = 1) : d638 p ≤ (0 : Int) + d119 p := by
  cases selected : p 139 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d638, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6866 p hg
    simpa only [d638, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d638, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6386 p hg
    simpa only [d638, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6943 (p : Pattern) (guard : d873 p = 1) : d639 p ≤ (0 : Int) + d120 p := by
  cases selected : p 138 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d639, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6942 p hg
    simpa only [d639, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d639, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6883 p hg
    simpa only [d639, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6944 (p : Pattern) (guard : d873 p = 1) : d640 p ≤ (0 : Int) + d121 p := by
  cases selected : p 134 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d640, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6422 p hg
    simpa only [d640, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d640, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6943 p hg
    simpa only [d640, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6945 (p : Pattern) (guard : d873 p = 1) : d641 p ≤ (0 : Int) + d122 p := by
  cases selected : p 133 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d641, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6944 p hg
    simpa only [d641, d122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d641, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6914 p hg
    simpa only [d641, d122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6946 (p : Pattern) (guard : d873 p = 1) : d642 p ≤ (0 : Int) + d123 p := by
  cases selected : p 132 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d642, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6445 p hg
    simpa only [d642, d123, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d642, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6945 p hg
    simpa only [d642, d123, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6947 (p : Pattern) (guard : d873 p = 1) : d643 p ≤ (0 : Int) + d124 p := by
  cases selected : p 113 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d643, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6934 p hg
    simpa only [d643, d124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d643, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6946 p hg
    simpa only [d643, d124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6948 (p : Pattern) (guard : d873 p = 1) : d586 p ≤ (0 : Int) + d125 p := by
  cases selected : p 133 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6451 p hg
    simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6900 p hg
    simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6949 (p : Pattern) (guard : d873 p = 1) : d644 p ≤ (0 : Int) + d126 p := by
  cases selected : p 132 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d644, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6452 p hg
    simpa only [d644, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d644, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6948 p hg
    simpa only [d644, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6950 (p : Pattern) (guard : d873 p = 1) : d645 p ≤ (0 : Int) + d127 p := by
  cases selected : p 113 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d645, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6919 p hg
    simpa only [d645, d127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d645, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6949 p hg
    simpa only [d645, d127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6951 (p : Pattern) (guard : d873 p = 1) : d646 p ≤ (0 : Int) + d128 p := by
  cases selected : p 112 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d646, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6947 p hg
    simpa only [d646, d128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d646, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6950 p hg
    simpa only [d646, d128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6952 (p : Pattern) (guard : d873 p = 1) : d647 p ≤ (0 : Int) + d129 p := by
  cases selected : p 113 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d647, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6938 p hg
    simpa only [d647, d129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d647, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6907 p hg
    simpa only [d647, d129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6953 (p : Pattern) (guard : d873 p = 1) : d648 p ≤ (0 : Int) + d130 p := by
  cases selected : p 113 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d648, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6927 p hg
    simpa only [d648, d130, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d648, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare715 p hg
    simpa only [d648, d130, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6954 (p : Pattern) (guard : d873 p = 1) : d649 p ≤ (0 : Int) + d131 p := by
  cases selected : p 112 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d649, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6952 p hg
    simpa only [d649, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d649, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6953 p hg
    simpa only [d649, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6955 (p : Pattern) (guard : d873 p = 1) : d650 p ≤ (0 : Int) + d132 p := by
  cases selected : p 106 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d650, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6951 p hg
    simpa only [d650, d132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d650, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6954 p hg
    simpa only [d650, d132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6956 (p : Pattern) (guard : d873 p = 1) : d651 p ≤ (0 : Int) + d133 p := by
  cases selected : p 86 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d651, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6941 p hg
    simpa only [d651, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d651, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6955 p hg
    simpa only [d651, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6957 (p : Pattern) (guard : d873 p = 1) : d652 p ≤ (0 : Int) + d134 p := by
  cases selected : p 80 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d652, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6931 p hg
    simpa only [d652, d134, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d652, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6956 p hg
    simpa only [d652, d134, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6958 (p : Pattern) (guard : d0 p = 1) : d549 p ≤ (0 : Int) + d140 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6959 (p : Pattern) (guard : d1243 p = 1) : d550 p ≤ (0 : Int) + d293 p := by
  cases selected : p 133 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d1243, d550, d293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6384 p hg
    simpa only [d1243, d550, d293, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1243, d550, d293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6958 p hg
    simpa only [d1243, d550, d293, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6960 (p : Pattern) (guard : d1171 p = 1) : d538 p ≤ (0 : Int) + d8 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1167 p = 1 := by simpa only [d1171, d538, d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3514 p hg
    simpa only [d1171, d538, d8, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1171, d538, d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6375 p hg
    simpa only [d1171, d538, d8, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6961 (p : Pattern) (guard : d1171 p = 1) : d539 p ≤ (0 : Int) + d8 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1167 p = 1 := by simpa only [d1171, d539, d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3514 p hg
    simpa only [d1171, d539, d8, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1171, d539, d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6377 p hg
    simpa only [d1171, d539, d8, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6962 (p : Pattern) (guard : d1171 p = 1) : d540 p ≤ (0 : Int) + d14 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1167 p = 1 := by simpa only [d1171, d540, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3517 p hg
    simpa only [d1171, d540, d14, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1171, d540, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6379 p hg
    simpa only [d1171, d540, d14, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6963 (p : Pattern) (guard : d1171 p = 1) : d541 p ≤ (0 : Int) + d15 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d541, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6961 p hg
    simpa only [d541, d15, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d541, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6962 p hg
    simpa only [d541, d15, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6964 (p : Pattern) (guard : d1171 p = 1) : d542 p ≤ (0 : Int) + d16 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d542, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6960 p hg
    simpa only [d542, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d542, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6963 p hg
    simpa only [d542, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6965 (p : Pattern) (guard : d0 p = 1) : d30 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6966 (p : Pattern) (guard : d1167 p = 1) : d31 p ≤ (0 : Int) + d6 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1167, d31, d6, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare659 p hg
    simpa only [d1167, d31, d6, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1167, d31, d6, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6965 p hg
    simpa only [d1167, d31, d6, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6967 (p : Pattern) (guard : d1171 p = 1) : d551 p ≤ (0 : Int) + d8 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1167 p = 1 := by simpa only [d1171, d551, d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6966 p hg
    simpa only [d1171, d551, d8, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1171, d551, d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6377 p hg
    simpa only [d1171, d551, d8, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6968 (p : Pattern) (guard : d0 p = 1) : d21 p ≤ (0 : Int) + d11 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6969 (p : Pattern) (guard : d1167 p = 1) : d22 p ≤ (0 : Int) + d12 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1167, d22, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare665 p hg
    simpa only [d1167, d22, d12, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1167, d22, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6968 p hg
    simpa only [d1167, d22, d12, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6970 (p : Pattern) (guard : d1171 p = 1) : d546 p ≤ (0 : Int) + d14 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1167 p = 1 := by simpa only [d1171, d546, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6969 p hg
    simpa only [d1171, d546, d14, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1171, d546, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6379 p hg
    simpa only [d1171, d546, d14, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6971 (p : Pattern) (guard : d1171 p = 1) : d552 p ≤ (0 : Int) + d15 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d552, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6967 p hg
    simpa only [d552, d15, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d552, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6970 p hg
    simpa only [d552, d15, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6972 (p : Pattern) (guard : d1171 p = 1) : d553 p ≤ (0 : Int) + d16 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d553, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6967 p hg
    simpa only [d553, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d553, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6971 p hg
    simpa only [d553, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6973 (p : Pattern) (guard : d1171 p = 1) : d554 p ≤ (0 : Int) + d16 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6964 p hg
    simpa only [d554, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6972 p hg
    simpa only [d554, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6974 (p : Pattern) (guard : d1246 p = 1) : d555 p ≤ (0 : Int) + d293 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d1246, d555, d293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6973 p hg
    simpa only [d1246, d555, d293, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1246, d555, d293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6958 p hg
    simpa only [d1246, d555, d293, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6975 (p : Pattern) (guard : d1247 p = 1) : d556 p ≤ (0 : Int) + d293 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1243 p = 1 := by simpa only [d1247, d556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6959 p hg
    simpa only [d1247, d556, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1246 p = 1 := by simpa only [d1247, d556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6974 p hg
    simpa only [d1247, d556, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6976 (p : Pattern) (guard : d0 p = 1) : d557 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6977 (p : Pattern) (guard : d1243 p = 1) : d558 p ≤ (0 : Int) + d294 p := by
  cases selected : p 133 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d1243, d558, d294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6381 p hg
    simpa only [d1243, d558, d294, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1243, d558, d294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6976 p hg
    simpa only [d1243, d558, d294, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6978 (p : Pattern) (guard : d1171 p = 1) : d559 p ≤ (0 : Int) + d15 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6963 p hg
    simpa only [d559, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6971 p hg
    simpa only [d559, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6979 (p : Pattern) (guard : d1246 p = 1) : d560 p ≤ (0 : Int) + d294 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d1246, d560, d294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6978 p hg
    simpa only [d1246, d560, d294, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1246, d560, d294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6976 p hg
    simpa only [d1246, d560, d294, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6980 (p : Pattern) (guard : d1247 p = 1) : d561 p ≤ (0 : Int) + d294 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1243 p = 1 := by simpa only [d1247, d561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6977 p hg
    simpa only [d1247, d561, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1246 p = 1 := by simpa only [d1247, d561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6979 p hg
    simpa only [d1247, d561, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6981 (p : Pattern) (guard : d0 p = 1) : d566 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6982 (p : Pattern) (guard : d1243 p = 1) : d567 p ≤ (0 : Int) + d295 p := by
  cases selected : p 133 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d1243, d567, d295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6400 p hg
    simpa only [d1243, d567, d295, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1243, d567, d295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6981 p hg
    simpa only [d1243, d567, d295, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6983 (p : Pattern) (guard : d1171 p = 1) : d562 p ≤ (0 : Int) + d52 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d562, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6961 p hg
    simpa only [d562, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d562, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2819 p hg
    simpa only [d562, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6984 (p : Pattern) (guard : d1171 p = 1) : d563 p ≤ (0 : Int) + d53 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d563, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6963 p hg
    simpa only [d563, d53, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d563, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6983 p hg
    simpa only [d563, d53, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6985 (p : Pattern) (guard : d1171 p = 1) : d568 p ≤ (0 : Int) + d52 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d568, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6967 p hg
    simpa only [d568, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d568, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2819 p hg
    simpa only [d568, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6986 (p : Pattern) (guard : d1171 p = 1) : d569 p ≤ (0 : Int) + d53 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d569, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6971 p hg
    simpa only [d569, d53, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d569, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6985 p hg
    simpa only [d569, d53, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6987 (p : Pattern) (guard : d1171 p = 1) : d570 p ≤ (0 : Int) + d53 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6984 p hg
    simpa only [d570, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6986 p hg
    simpa only [d570, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6988 (p : Pattern) (guard : d1246 p = 1) : d571 p ≤ (0 : Int) + d295 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d1246, d571, d295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6987 p hg
    simpa only [d1246, d571, d295, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1246, d571, d295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6981 p hg
    simpa only [d1246, d571, d295, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6989 (p : Pattern) (guard : d1247 p = 1) : d572 p ≤ (0 : Int) + d295 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1243 p = 1 := by simpa only [d1247, d572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6982 p hg
    simpa only [d1247, d572, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1246 p = 1 := by simpa only [d1247, d572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6988 p hg
    simpa only [d1247, d572, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6990 (p : Pattern) (guard : d1247 p = 1) : d573 p ≤ (0 : Int) + d296 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1247 p = 1 := by simpa only [d573, d296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6980 p hg
    simpa only [d573, d296, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1247 p = 1 := by simpa only [d573, d296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6989 p hg
    simpa only [d573, d296, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6991 (p : Pattern) (guard : d1247 p = 1) : d574 p ≤ (0 : Int) + d297 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1247 p = 1 := by simpa only [d574, d297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6975 p hg
    simpa only [d574, d297, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1247 p = 1 := by simpa only [d574, d297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6990 p hg
    simpa only [d574, d297, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6992 (p : Pattern) (guard : d0 p = 1) : d17 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6993 (p : Pattern) (guard : d1167 p = 1) : d18 p ≤ (0 : Int) + d6 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1167, d18, d6, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare659 p hg
    simpa only [d1167, d18, d6, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1167, d18, d6, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6992 p hg
    simpa only [d1167, d18, d6, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6994 (p : Pattern) (guard : d1171 p = 1) : d545 p ≤ (0 : Int) + d8 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1167 p = 1 := by simpa only [d1171, d545, d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6993 p hg
    simpa only [d1171, d545, d8, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1171, d545, d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6377 p hg
    simpa only [d1171, d545, d8, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6995 (p : Pattern) (guard : d1171 p = 1) : d547 p ≤ (0 : Int) + d15 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d547, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6994 p hg
    simpa only [d547, d15, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d547, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6970 p hg
    simpa only [d547, d15, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6996 (p : Pattern) (guard : d1171 p = 1) : d548 p ≤ (0 : Int) + d16 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d548, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6994 p hg
    simpa only [d548, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d548, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6995 p hg
    simpa only [d548, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6997 (p : Pattern) (guard : d1171 p = 1) : d575 p ≤ (0 : Int) + d16 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6964 p hg
    simpa only [d575, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6996 p hg
    simpa only [d575, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6998 (p : Pattern) (guard : d0 p = 1) : d580 p ≤ (0 : Int) + d140 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6999 (p : Pattern) (guard : d1246 p = 1) : d581 p ≤ (0 : Int) + d293 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d1246, d581, d293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6997 p hg
    simpa only [d1246, d581, d293, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1246, d581, d293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6998 p hg
    simpa only [d1246, d581, d293, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban32Refined
