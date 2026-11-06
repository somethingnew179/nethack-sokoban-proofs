/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Substitutions49
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c0 (pattern : Twelve) (guard : d1 pattern = 1) : d116 pattern ≤ (0 : Int) + d116 pattern := by
  omega
theorem c1 (pattern : Twelve) (guard : d1 pattern = 1) : d871 pattern ≤ (0 : Int) + d871 pattern := by
  omega
theorem c2 (pattern : Twelve) (guard : d1 pattern = 1) : d1323 pattern ≤ (0 : Int) + d1323 pattern := by
  omega
theorem c3 (pattern : Twelve) (guard : d1 pattern = 1) : d1664 pattern ≤ (0 : Int) + d1664 pattern := by
  omega
theorem c4 (pattern : Twelve) (guard : d1 pattern = 1) : d102 pattern ≤ (0 : Int) + d102 pattern := by
  omega
theorem c5 (pattern : Twelve) (guard : d0 pattern = 1) : d103 pattern ≤ (0 : Int) + d213 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6 (pattern : Twelve) (guard : d1835 pattern = 1) : d110 pattern ≤ (0 : Int) + d222 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1835, d110, d222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4 pattern childGuard
    simpa only [d1835, d110, d222, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1835, d110, d222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5 pattern childGuard
    simpa only [d1835, d110, d222, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7 (pattern : Twelve) (guard : d1 pattern = 1) : d104 pattern ≤ (0 : Int) + d104 pattern := by
  omega
theorem c8 (pattern : Twelve) (guard : d0 pattern = 1) : d105 pattern ≤ (0 : Int) + d215 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9 (pattern : Twelve) (guard : d1835 pattern = 1) : d111 pattern ≤ (0 : Int) + d223 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1835, d111, d223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7 pattern childGuard
    simpa only [d1835, d111, d223, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1835, d111, d223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8 pattern childGuard
    simpa only [d1835, d111, d223, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10 (pattern : Twelve) (guard : d1835 pattern = 1) : d114 pattern ≤ (0 : Int) + d228 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1835 pattern = 1 := by simpa only [d114, d228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6 pattern childGuard
    simpa only [d114, d228, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1835 pattern = 1 := by simpa only [d114, d228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9 pattern childGuard
    simpa only [d114, d228, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11 (pattern : Twelve) (guard : d1 pattern = 1) : d106 pattern ≤ (0 : Int) + d106 pattern := by
  omega
theorem c12 (pattern : Twelve) (guard : d0 pattern = 1) : d107 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c13 (pattern : Twelve) (guard : d1835 pattern = 1) : d112 pattern ≤ (0 : Int) + d224 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1835, d112, d224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11 pattern childGuard
    simpa only [d1835, d112, d224, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1835, d112, d224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12 pattern childGuard
    simpa only [d1835, d112, d224, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14 (pattern : Twelve) (guard : d1 pattern = 1) : d108 pattern ≤ (0 : Int) + d108 pattern := by
  omega
theorem c15 (pattern : Twelve) (guard : d0 pattern = 1) : d109 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c16 (pattern : Twelve) (guard : d1835 pattern = 1) : d113 pattern ≤ (0 : Int) + d225 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1835, d113, d225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14 pattern childGuard
    simpa only [d1835, d113, d225, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1835, d113, d225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15 pattern childGuard
    simpa only [d1835, d113, d225, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17 (pattern : Twelve) (guard : d1835 pattern = 1) : d115 pattern ≤ (0 : Int) + d229 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1835 pattern = 1 := by simpa only [d115, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13 pattern childGuard
    simpa only [d115, d229, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1835 pattern = 1 := by simpa only [d115, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16 pattern childGuard
    simpa only [d115, d229, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18 (pattern : Twelve) (guard : d1835 pattern = 1) : d116 pattern ≤ (0 : Int) + d231 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1835 pattern = 1 := by simpa only [d116, d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10 pattern childGuard
    simpa only [d116, d231, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1835 pattern = 1 := by simpa only [d116, d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17 pattern childGuard
    simpa only [d116, d231, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19 (pattern : Twelve) (guard : d0 pattern = 1) : d103 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c20 (pattern : Twelve) (guard : d1835 pattern = 1) : d110 pattern ≤ (0 : Int) + d226 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1835, d110, d226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4 pattern childGuard
    simpa only [d1835, d110, d226, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1835, d110, d226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19 pattern childGuard
    simpa only [d1835, d110, d226, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21 (pattern : Twelve) (guard : d0 pattern = 1) : d105 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c22 (pattern : Twelve) (guard : d1835 pattern = 1) : d111 pattern ≤ (0 : Int) + d227 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1835, d111, d227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7 pattern childGuard
    simpa only [d1835, d111, d227, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1835, d111, d227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21 pattern childGuard
    simpa only [d1835, d111, d227, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23 (pattern : Twelve) (guard : d1835 pattern = 1) : d114 pattern ≤ (0 : Int) + d230 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1835 pattern = 1 := by simpa only [d114, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20 pattern childGuard
    simpa only [d114, d230, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1835 pattern = 1 := by simpa only [d114, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22 pattern childGuard
    simpa only [d114, d230, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c24 (pattern : Twelve) (guard : d1835 pattern = 1) : d116 pattern ≤ (0 : Int) + d232 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1835 pattern = 1 := by simpa only [d116, d232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23 pattern childGuard
    simpa only [d116, d232, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1835 pattern = 1 := by simpa only [d116, d232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17 pattern childGuard
    simpa only [d116, d232, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c25 (pattern : Twelve) (guard : d1835 pattern = 1) : d116 pattern ≤ (0 : Int) + d233 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1835 pattern = 1 := by simpa only [d233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18 pattern childGuard
    simpa only [d233, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1835 pattern = 1 := by simpa only [d233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c24 pattern childGuard
    simpa only [d233, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c26 (pattern : Twelve) (guard : d1835 pattern = 1) : d116 pattern ≤ (0 : Int) + d234 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1835 pattern = 1 := by simpa only [d234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c25 pattern childGuard
    simpa only [d234, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1835 pattern = 1 := by simpa only [d234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c24 pattern childGuard
    simpa only [d234, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c27 (pattern : Twelve) (guard : d1 pattern = 1) : d861 pattern ≤ (0 : Int) + d861 pattern := by
  omega
theorem c28 (pattern : Twelve) (guard : d0 pattern = 1) : d861 pattern ≤ (0 : Int) + d918 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c29 (pattern : Twelve) (guard : d1835 pattern = 1) : d861 pattern ≤ (0 : Int) + d927 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1835, d927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c27 pattern childGuard
    simpa only [d1835, d927, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1835, d927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c28 pattern childGuard
    simpa only [d1835, d927, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c30 (pattern : Twelve) (guard : d1 pattern = 1) : d862 pattern ≤ (0 : Int) + d862 pattern := by
  omega
theorem c31 (pattern : Twelve) (guard : d0 pattern = 1) : d863 pattern ≤ (0 : Int) + d920 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c32 (pattern : Twelve) (guard : d1835 pattern = 1) : d867 pattern ≤ (0 : Int) + d928 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1835, d867, d928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c30 pattern childGuard
    simpa only [d1835, d867, d928, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1835, d867, d928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c31 pattern childGuard
    simpa only [d1835, d867, d928, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c33 (pattern : Twelve) (guard : d1835 pattern = 1) : d869 pattern ≤ (0 : Int) + d933 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1835 pattern = 1 := by simpa only [d869, d933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c29 pattern childGuard
    simpa only [d869, d933, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1835 pattern = 1 := by simpa only [d869, d933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c32 pattern childGuard
    simpa only [d869, d933, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c34 (pattern : Twelve) (guard : d1 pattern = 1) : d864 pattern ≤ (0 : Int) + d864 pattern := by
  omega
theorem c35 (pattern : Twelve) (guard : d0 pattern = 1) : d864 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c36 (pattern : Twelve) (guard : d1835 pattern = 1) : d864 pattern ≤ (0 : Int) + d929 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1835, d929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c34 pattern childGuard
    simpa only [d1835, d929, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1835, d929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c35 pattern childGuard
    simpa only [d1835, d929, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c37 (pattern : Twelve) (guard : d1 pattern = 1) : d865 pattern ≤ (0 : Int) + d865 pattern := by
  omega
theorem c38 (pattern : Twelve) (guard : d0 pattern = 1) : d866 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c39 (pattern : Twelve) (guard : d1835 pattern = 1) : d868 pattern ≤ (0 : Int) + d930 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1835, d868, d930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c37 pattern childGuard
    simpa only [d1835, d868, d930, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1835, d868, d930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c38 pattern childGuard
    simpa only [d1835, d868, d930, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c40 (pattern : Twelve) (guard : d1835 pattern = 1) : d870 pattern ≤ (0 : Int) + d934 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1835 pattern = 1 := by simpa only [d870, d934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c36 pattern childGuard
    simpa only [d870, d934, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1835 pattern = 1 := by simpa only [d870, d934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c39 pattern childGuard
    simpa only [d870, d934, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c41 (pattern : Twelve) (guard : d1835 pattern = 1) : d871 pattern ≤ (0 : Int) + d936 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1835 pattern = 1 := by simpa only [d871, d936, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c33 pattern childGuard
    simpa only [d871, d936, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1835 pattern = 1 := by simpa only [d871, d936, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c40 pattern childGuard
    simpa only [d871, d936, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c42 (pattern : Twelve) (guard : d0 pattern = 1) : d861 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c43 (pattern : Twelve) (guard : d1835 pattern = 1) : d861 pattern ≤ (0 : Int) + d931 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1835, d931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c27 pattern childGuard
    simpa only [d1835, d931, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1835, d931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c42 pattern childGuard
    simpa only [d1835, d931, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c44 (pattern : Twelve) (guard : d0 pattern = 1) : d863 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c45 (pattern : Twelve) (guard : d1835 pattern = 1) : d867 pattern ≤ (0 : Int) + d932 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1835, d867, d932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c30 pattern childGuard
    simpa only [d1835, d867, d932, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1835, d867, d932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c44 pattern childGuard
    simpa only [d1835, d867, d932, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c46 (pattern : Twelve) (guard : d1835 pattern = 1) : d869 pattern ≤ (0 : Int) + d935 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1835 pattern = 1 := by simpa only [d869, d935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c43 pattern childGuard
    simpa only [d869, d935, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1835 pattern = 1 := by simpa only [d869, d935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c45 pattern childGuard
    simpa only [d869, d935, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c47 (pattern : Twelve) (guard : d1835 pattern = 1) : d871 pattern ≤ (0 : Int) + d937 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1835 pattern = 1 := by simpa only [d871, d937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c46 pattern childGuard
    simpa only [d871, d937, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1835 pattern = 1 := by simpa only [d871, d937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c40 pattern childGuard
    simpa only [d871, d937, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c48 (pattern : Twelve) (guard : d1835 pattern = 1) : d871 pattern ≤ (0 : Int) + d938 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1835 pattern = 1 := by simpa only [d938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c41 pattern childGuard
    simpa only [d938, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1835 pattern = 1 := by simpa only [d938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c47 pattern childGuard
    simpa only [d938, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c49 (pattern : Twelve) (guard : d1835 pattern = 1) : d871 pattern ≤ (0 : Int) + d939 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1835 pattern = 1 := by simpa only [d939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c48 pattern childGuard
    simpa only [d939, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1835 pattern = 1 := by simpa only [d939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c47 pattern childGuard
    simpa only [d939, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c50 (pattern : Twelve) (guard : d1 pattern = 1) : d1313 pattern ≤ (0 : Int) + d1313 pattern := by
  omega
theorem c51 (pattern : Twelve) (guard : d0 pattern = 1) : d1313 pattern ≤ (0 : Int) + d1360 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c52 (pattern : Twelve) (guard : d1835 pattern = 1) : d1313 pattern ≤ (0 : Int) + d1368 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1835, d1368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c50 pattern childGuard
    simpa only [d1835, d1368, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1835, d1368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c51 pattern childGuard
    simpa only [d1835, d1368, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c53 (pattern : Twelve) (guard : d1 pattern = 1) : d1314 pattern ≤ (0 : Int) + d1314 pattern := by
  omega
theorem c54 (pattern : Twelve) (guard : d0 pattern = 1) : d1315 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c55 (pattern : Twelve) (guard : d1835 pattern = 1) : d1319 pattern ≤ (0 : Int) + d1369 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1835, d1319, d1369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c53 pattern childGuard
    simpa only [d1835, d1319, d1369, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1835, d1319, d1369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c54 pattern childGuard
    simpa only [d1835, d1319, d1369, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c56 (pattern : Twelve) (guard : d1835 pattern = 1) : d1321 pattern ≤ (0 : Int) + d1373 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1835 pattern = 1 := by simpa only [d1321, d1373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c52 pattern childGuard
    simpa only [d1321, d1373, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1835 pattern = 1 := by simpa only [d1321, d1373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c55 pattern childGuard
    simpa only [d1321, d1373, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c57 (pattern : Twelve) (guard : d1 pattern = 1) : d1316 pattern ≤ (0 : Int) + d1316 pattern := by
  omega
theorem c58 (pattern : Twelve) (guard : d0 pattern = 1) : d1316 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c59 (pattern : Twelve) (guard : d1835 pattern = 1) : d1316 pattern ≤ (0 : Int) + d1370 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1835, d1370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c57 pattern childGuard
    simpa only [d1835, d1370, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1835, d1370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c58 pattern childGuard
    simpa only [d1835, d1370, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c60 (pattern : Twelve) (guard : d1 pattern = 1) : d1317 pattern ≤ (0 : Int) + d1317 pattern := by
  omega
theorem c61 (pattern : Twelve) (guard : d0 pattern = 1) : d1318 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c62 (pattern : Twelve) (guard : d1835 pattern = 1) : d1320 pattern ≤ (0 : Int) + d1371 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1835, d1320, d1371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c60 pattern childGuard
    simpa only [d1835, d1320, d1371, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1835, d1320, d1371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c61 pattern childGuard
    simpa only [d1835, d1320, d1371, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c63 (pattern : Twelve) (guard : d1835 pattern = 1) : d1322 pattern ≤ (0 : Int) + d1374 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1835 pattern = 1 := by simpa only [d1322, d1374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c59 pattern childGuard
    simpa only [d1322, d1374, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1835 pattern = 1 := by simpa only [d1322, d1374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c62 pattern childGuard
    simpa only [d1322, d1374, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c64 (pattern : Twelve) (guard : d1835 pattern = 1) : d1323 pattern ≤ (0 : Int) + d1376 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1835 pattern = 1 := by simpa only [d1323, d1376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c56 pattern childGuard
    simpa only [d1323, d1376, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1835 pattern = 1 := by simpa only [d1323, d1376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c63 pattern childGuard
    simpa only [d1323, d1376, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c65 (pattern : Twelve) (guard : d0 pattern = 1) : d1313 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c66 (pattern : Twelve) (guard : d1835 pattern = 1) : d1313 pattern ≤ (0 : Int) + d1372 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1835, d1372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c50 pattern childGuard
    simpa only [d1835, d1372, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1835, d1372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c65 pattern childGuard
    simpa only [d1835, d1372, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c67 (pattern : Twelve) (guard : d1835 pattern = 1) : d1321 pattern ≤ (0 : Int) + d1375 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1835 pattern = 1 := by simpa only [d1321, d1375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c66 pattern childGuard
    simpa only [d1321, d1375, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1835 pattern = 1 := by simpa only [d1321, d1375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c55 pattern childGuard
    simpa only [d1321, d1375, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c68 (pattern : Twelve) (guard : d1835 pattern = 1) : d1323 pattern ≤ (0 : Int) + d1377 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1835 pattern = 1 := by simpa only [d1323, d1377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c67 pattern childGuard
    simpa only [d1323, d1377, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1835 pattern = 1 := by simpa only [d1323, d1377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c63 pattern childGuard
    simpa only [d1323, d1377, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c69 (pattern : Twelve) (guard : d1835 pattern = 1) : d1323 pattern ≤ (0 : Int) + d1378 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1835 pattern = 1 := by simpa only [d1378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c64 pattern childGuard
    simpa only [d1378, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1835 pattern = 1 := by simpa only [d1378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c68 pattern childGuard
    simpa only [d1378, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c70 (pattern : Twelve) (guard : d1835 pattern = 1) : d1323 pattern ≤ (0 : Int) + d1379 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1835 pattern = 1 := by simpa only [d1379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c69 pattern childGuard
    simpa only [d1379, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1835 pattern = 1 := by simpa only [d1379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c68 pattern childGuard
    simpa only [d1379, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c71 (pattern : Twelve) (guard : d1 pattern = 1) : d1660 pattern ≤ (0 : Int) + d1660 pattern := by
  omega
theorem c72 (pattern : Twelve) (guard : d0 pattern = 1) : d1660 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c73 (pattern : Twelve) (guard : d1835 pattern = 1) : d1660 pattern ≤ (0 : Int) + d1686 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1835, d1686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c71 pattern childGuard
    simpa only [d1835, d1686, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1835, d1686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c72 pattern childGuard
    simpa only [d1835, d1686, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c74 (pattern : Twelve) (guard : d1 pattern = 1) : d1661 pattern ≤ (0 : Int) + d1661 pattern := by
  omega
theorem c75 (pattern : Twelve) (guard : d0 pattern = 1) : d1662 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c76 (pattern : Twelve) (guard : d1835 pattern = 1) : d1663 pattern ≤ (0 : Int) + d1687 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1835, d1663, d1687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c74 pattern childGuard
    simpa only [d1835, d1663, d1687, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1835, d1663, d1687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c75 pattern childGuard
    simpa only [d1835, d1663, d1687, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c77 (pattern : Twelve) (guard : d1835 pattern = 1) : d1664 pattern ≤ (0 : Int) + d1688 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1835 pattern = 1 := by simpa only [d1664, d1688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c73 pattern childGuard
    simpa only [d1664, d1688, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1835 pattern = 1 := by simpa only [d1664, d1688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c76 pattern childGuard
    simpa only [d1664, d1688, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c78 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (0 : Int) + d0 pattern := by
  omega
theorem c79 (pattern : Twelve) (guard : d0 pattern = 1) : d0 pattern ≤ (0 : Int) + d171 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c80 (pattern : Twelve) (guard : d1837 pattern = 1) : d0 pattern ≤ (0 : Int) + d235 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1837, d235, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c79 pattern childGuard
    simpa only [d1837, d235, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c81 (pattern : Twelve) (guard : d1 pattern = 1) : d26 pattern ≤ (0 : Int) + d26 pattern := by
  omega
theorem c82 (pattern : Twelve) (guard : d0 pattern = 1) : d27 pattern ≤ (0 : Int) + d172 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c83 (pattern : Twelve) (guard : d1837 pattern = 1) : d50 pattern ≤ (0 : Int) + d236 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d50, d236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c81 pattern childGuard
    simpa only [d1837, d50, d236, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d50, d236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c82 pattern childGuard
    simpa only [d1837, d50, d236, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c84 (pattern : Twelve) (guard : d1837 pattern = 1) : d72 pattern ≤ (0 : Int) + d256 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d72, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c80 pattern childGuard
    simpa only [d72, d256, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d72, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c83 pattern childGuard
    simpa only [d72, d256, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c85 (pattern : Twelve) (guard : d0 pattern = 1) : d0 pattern ≤ (0 : Int) + d172 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c86 (pattern : Twelve) (guard : d1837 pattern = 1) : d0 pattern ≤ (0 : Int) + d237 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1837, d237, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c85 pattern childGuard
    simpa only [d1837, d237, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c87 (pattern : Twelve) (guard : d1 pattern = 1) : d28 pattern ≤ (0 : Int) + d28 pattern := by
  omega
theorem c88 (pattern : Twelve) (guard : d0 pattern = 1) : d29 pattern ≤ (0 : Int) + d173 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c89 (pattern : Twelve) (guard : d1837 pattern = 1) : d51 pattern ≤ (0 : Int) + d238 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d51, d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c87 pattern childGuard
    simpa only [d1837, d51, d238, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d51, d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c88 pattern childGuard
    simpa only [d1837, d51, d238, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c90 (pattern : Twelve) (guard : d1837 pattern = 1) : d73 pattern ≤ (0 : Int) + d257 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d73, d257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c86 pattern childGuard
    simpa only [d73, d257, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d73, d257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c89 pattern childGuard
    simpa only [d73, d257, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c91 (pattern : Twelve) (guard : d1837 pattern = 1) : d91 pattern ≤ (0 : Int) + d272 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d91, d272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c84 pattern childGuard
    simpa only [d91, d272, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d91, d272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c90 pattern childGuard
    simpa only [d91, d272, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c92 (pattern : Twelve) (guard : d1 pattern = 1) : d30 pattern ≤ (0 : Int) + d30 pattern := by
  omega
theorem c93 (pattern : Twelve) (guard : d0 pattern = 1) : d31 pattern ≤ (0 : Int) + d175 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c94 (pattern : Twelve) (guard : d1837 pattern = 1) : d52 pattern ≤ (0 : Int) + d239 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d52, d239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c92 pattern childGuard
    simpa only [d1837, d52, d239, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d52, d239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c93 pattern childGuard
    simpa only [d1837, d52, d239, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c95 (pattern : Twelve) (guard : d0 pattern = 1) : d32 pattern ≤ (0 : Int) + d176 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c96 (pattern : Twelve) (guard : d1837 pattern = 1) : d53 pattern ≤ (0 : Int) + d240 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d53, d240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c92 pattern childGuard
    simpa only [d1837, d53, d240, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d53, d240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c95 pattern childGuard
    simpa only [d1837, d53, d240, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c97 (pattern : Twelve) (guard : d1837 pattern = 1) : d74 pattern ≤ (0 : Int) + d258 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d74, d258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c94 pattern childGuard
    simpa only [d74, d258, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d74, d258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c96 pattern childGuard
    simpa only [d74, d258, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c98 (pattern : Twelve) (guard : d0 pattern = 1) : d33 pattern ≤ (0 : Int) + d176 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c99 (pattern : Twelve) (guard : d1837 pattern = 1) : d54 pattern ≤ (0 : Int) + d240 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d54, d240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c92 pattern childGuard
    simpa only [d1837, d54, d240, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d54, d240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c98 pattern childGuard
    simpa only [d1837, d54, d240, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c100 (pattern : Twelve) (guard : d1 pattern = 1) : d34 pattern ≤ (0 : Int) + d34 pattern := by
  omega
theorem c101 (pattern : Twelve) (guard : d0 pattern = 1) : d29 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c102 (pattern : Twelve) (guard : d1837 pattern = 1) : d55 pattern ≤ (0 : Int) + d241 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d55, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c100 pattern childGuard
    simpa only [d1837, d55, d241, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d55, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c101 pattern childGuard
    simpa only [d1837, d55, d241, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c103 (pattern : Twelve) (guard : d1837 pattern = 1) : d75 pattern ≤ (0 : Int) + d259 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d75, d259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c99 pattern childGuard
    simpa only [d75, d259, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d75, d259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c102 pattern childGuard
    simpa only [d75, d259, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c104 (pattern : Twelve) (guard : d1837 pattern = 1) : d92 pattern ≤ (0 : Int) + d273 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d92, d273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c97 pattern childGuard
    simpa only [d92, d273, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d92, d273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c103 pattern childGuard
    simpa only [d92, d273, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c105 (pattern : Twelve) (guard : d1837 pattern = 1) : d102 pattern ≤ (0 : Int) + d284 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d102, d284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c91 pattern childGuard
    simpa only [d102, d284, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d102, d284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c104 pattern childGuard
    simpa only [d102, d284, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c106 (pattern : Twelve) (guard : d0 pattern = 1) : d0 pattern ≤ (0 : Int) + d175 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c107 (pattern : Twelve) (guard : d1837 pattern = 1) : d0 pattern ≤ (0 : Int) + d242 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1837, d242, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c106 pattern childGuard
    simpa only [d1837, d242, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c108 (pattern : Twelve) (guard : d0 pattern = 1) : d27 pattern ≤ (0 : Int) + d176 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c109 (pattern : Twelve) (guard : d1837 pattern = 1) : d50 pattern ≤ (0 : Int) + d243 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d50, d243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c81 pattern childGuard
    simpa only [d1837, d50, d243, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d50, d243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c108 pattern childGuard
    simpa only [d1837, d50, d243, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c110 (pattern : Twelve) (guard : d1837 pattern = 1) : d72 pattern ≤ (0 : Int) + d260 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d72, d260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c107 pattern childGuard
    simpa only [d72, d260, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d72, d260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c109 pattern childGuard
    simpa only [d72, d260, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c111 (pattern : Twelve) (guard : d0 pattern = 1) : d0 pattern ≤ (0 : Int) + d176 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c112 (pattern : Twelve) (guard : d1837 pattern = 1) : d0 pattern ≤ (0 : Int) + d244 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1837, d244, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c111 pattern childGuard
    simpa only [d1837, d244, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c113 (pattern : Twelve) (guard : d1837 pattern = 1) : d76 pattern ≤ (0 : Int) + d261 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d76, d261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c112 pattern childGuard
    simpa only [d76, d261, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d76, d261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c102 pattern childGuard
    simpa only [d76, d261, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c114 (pattern : Twelve) (guard : d1837 pattern = 1) : d93 pattern ≤ (0 : Int) + d274 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d93, d274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c110 pattern childGuard
    simpa only [d93, d274, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d93, d274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c113 pattern childGuard
    simpa only [d93, d274, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c115 (pattern : Twelve) (guard : d0 pattern = 1) : d35 pattern ≤ (0 : Int) + d178 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c116 (pattern : Twelve) (guard : d1837 pattern = 1) : d56 pattern ≤ (0 : Int) + d245 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d56, d245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c92 pattern childGuard
    simpa only [d1837, d56, d245, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d56, d245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c115 pattern childGuard
    simpa only [d1837, d56, d245, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c117 (pattern : Twelve) (guard : d0 pattern = 1) : d36 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c118 (pattern : Twelve) (guard : d1837 pattern = 1) : d57 pattern ≤ (0 : Int) + d246 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d57, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c92 pattern childGuard
    simpa only [d1837, d57, d246, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d57, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c117 pattern childGuard
    simpa only [d1837, d57, d246, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c119 (pattern : Twelve) (guard : d1837 pattern = 1) : d77 pattern ≤ (0 : Int) + d262 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d77, d262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c116 pattern childGuard
    simpa only [d77, d262, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d77, d262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c118 pattern childGuard
    simpa only [d77, d262, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c120 (pattern : Twelve) (guard : d0 pattern = 1) : d35 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c121 (pattern : Twelve) (guard : d1837 pattern = 1) : d56 pattern ≤ (0 : Int) + d246 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d56, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c92 pattern childGuard
    simpa only [d1837, d56, d246, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d56, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c120 pattern childGuard
    simpa only [d1837, d56, d246, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c122 (pattern : Twelve) (guard : d1837 pattern = 1) : d78 pattern ≤ (0 : Int) + d263 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d78, d263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c121 pattern childGuard
    simpa only [d78, d263, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d78, d263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c102 pattern childGuard
    simpa only [d78, d263, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c123 (pattern : Twelve) (guard : d1837 pattern = 1) : d94 pattern ≤ (0 : Int) + d275 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d94, d275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c119 pattern childGuard
    simpa only [d94, d275, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d94, d275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c122 pattern childGuard
    simpa only [d94, d275, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c124 (pattern : Twelve) (guard : d1837 pattern = 1) : d103 pattern ≤ (0 : Int) + d285 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d103, d285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c114 pattern childGuard
    simpa only [d103, d285, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d103, d285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c123 pattern childGuard
    simpa only [d103, d285, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c125 (pattern : Twelve) (guard : d1837 pattern = 1) : d110 pattern ≤ (0 : Int) + d293 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d110, d293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c105 pattern childGuard
    simpa only [d110, d293, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d110, d293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c124 pattern childGuard
    simpa only [d110, d293, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c126 (pattern : Twelve) (guard : d0 pattern = 1) : d30 pattern ≤ (0 : Int) + d180 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c127 (pattern : Twelve) (guard : d1837 pattern = 1) : d30 pattern ≤ (0 : Int) + d247 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c92 pattern childGuard
    simpa only [d1837, d247, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c126 pattern childGuard
    simpa only [d1837, d247, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c128 (pattern : Twelve) (guard : d0 pattern = 1) : d37 pattern ≤ (0 : Int) + d181 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c129 (pattern : Twelve) (guard : d1837 pattern = 1) : d58 pattern ≤ (0 : Int) + d248 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d58, d248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c92 pattern childGuard
    simpa only [d1837, d58, d248, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d58, d248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c128 pattern childGuard
    simpa only [d1837, d58, d248, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c130 (pattern : Twelve) (guard : d1837 pattern = 1) : d79 pattern ≤ (0 : Int) + d264 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d79, d264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c127 pattern childGuard
    simpa only [d79, d264, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d79, d264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c129 pattern childGuard
    simpa only [d79, d264, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c131 (pattern : Twelve) (guard : d0 pattern = 1) : d30 pattern ≤ (0 : Int) + d181 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c132 (pattern : Twelve) (guard : d1837 pattern = 1) : d30 pattern ≤ (0 : Int) + d248 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c92 pattern childGuard
    simpa only [d1837, d248, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c131 pattern childGuard
    simpa only [d1837, d248, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c133 (pattern : Twelve) (guard : d1837 pattern = 1) : d80 pattern ≤ (0 : Int) + d265 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d80, d265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c132 pattern childGuard
    simpa only [d80, d265, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d80, d265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c102 pattern childGuard
    simpa only [d80, d265, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c134 (pattern : Twelve) (guard : d1837 pattern = 1) : d95 pattern ≤ (0 : Int) + d276 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d95, d276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c130 pattern childGuard
    simpa only [d95, d276, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d95, d276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c133 pattern childGuard
    simpa only [d95, d276, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c135 (pattern : Twelve) (guard : d1 pattern = 1) : d38 pattern ≤ (0 : Int) + d38 pattern := by
  omega
theorem c136 (pattern : Twelve) (guard : d0 pattern = 1) : d39 pattern ≤ (0 : Int) + d183 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c137 (pattern : Twelve) (guard : d1837 pattern = 1) : d59 pattern ≤ (0 : Int) + d249 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d59, d249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c135 pattern childGuard
    simpa only [d1837, d59, d249, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d59, d249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c136 pattern childGuard
    simpa only [d1837, d59, d249, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c138 (pattern : Twelve) (guard : d0 pattern = 1) : d40 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c139 (pattern : Twelve) (guard : d1837 pattern = 1) : d60 pattern ≤ (0 : Int) + d250 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d60, d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c135 pattern childGuard
    simpa only [d1837, d60, d250, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d60, d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c138 pattern childGuard
    simpa only [d1837, d60, d250, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
