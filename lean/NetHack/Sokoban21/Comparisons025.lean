/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons024
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c3500 (pattern : Twelve) (guard : d1866 pattern = 1) : d9 pattern ≤ (0 : Int) + d160 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1866, d9, d160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1333 pattern childGuard
    simpa only [d1866, d9, d160, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1866, d9, d160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2923 pattern childGuard
    simpa only [d1866, d9, d160, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3501 (pattern : Twelve) (guard : d1867 pattern = 1) : d815 pattern ≤ (0 : Int) + d644 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d815, d644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3500 pattern childGuard
    simpa only [d1867, d815, d644, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d815, d644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3347 pattern childGuard
    simpa only [d1867, d815, d644, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3502 (pattern : Twelve) (guard : d1867 pattern = 1) : d820 pattern ≤ (0 : Int) + d670 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d820, d670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3501 pattern childGuard
    simpa only [d820, d670, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d820, d670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d820, d670, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3503 (pattern : Twelve) (guard : d1867 pattern = 1) : d829 pattern ≤ (0 : Int) + d698 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d829, d698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3371 pattern childGuard
    simpa only [d829, d698, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d829, d698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3502 pattern childGuard
    simpa only [d829, d698, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3504 (pattern : Twelve) (guard : d1867 pattern = 1) : d844 pattern ≤ (0 : Int) + d720 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d844, d720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3368 pattern childGuard
    simpa only [d844, d720, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d844, d720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3503 pattern childGuard
    simpa only [d844, d720, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3505 (pattern : Twelve) (guard : d1867 pattern = 1) : d830 pattern ≤ (0 : Int) + d697 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d830, d697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3371 pattern childGuard
    simpa only [d830, d697, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d830, d697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3365 pattern childGuard
    simpa only [d830, d697, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3506 (pattern : Twelve) (guard : d1867 pattern = 1) : d821 pattern ≤ (0 : Int) + d1186 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d821, d1186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3374 pattern childGuard
    simpa only [d821, d1186, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d821, d1186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3298 pattern childGuard
    simpa only [d821, d1186, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3507 (pattern : Twelve) (guard : d1867 pattern = 1) : d822 pattern ≤ (0 : Int) + d822 pattern := by
  omega
theorem c3508 (pattern : Twelve) (guard : d1867 pattern = 1) : d831 pattern ≤ (0 : Int) + d1195 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d831, d1195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3506 pattern childGuard
    simpa only [d831, d1195, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d831, d1195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3507 pattern childGuard
    simpa only [d831, d1195, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3509 (pattern : Twelve) (guard : d1867 pattern = 1) : d845 pattern ≤ (0 : Int) + d1207 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d845, d1207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3505 pattern childGuard
    simpa only [d845, d1207, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d845, d1207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3508 pattern childGuard
    simpa only [d845, d1207, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3510 (pattern : Twelve) (guard : d1867 pattern = 1) : d856 pattern ≤ (0 : Int) + d1221 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d856, d1221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3504 pattern childGuard
    simpa only [d856, d1221, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d856, d1221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3509 pattern childGuard
    simpa only [d856, d1221, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3511 (pattern : Twelve) (guard : d1867 pattern = 1) : d862 pattern ≤ (0 : Int) + d1230 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d862, d1230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3499 pattern childGuard
    simpa only [d862, d1230, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d862, d1230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3510 pattern childGuard
    simpa only [d862, d1230, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3512 (pattern : Twelve) (guard : d1867 pattern = 1) : d863 pattern ≤ (0 : Int) + d1231 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d863, d1231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3492 pattern childGuard
    simpa only [d863, d1231, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d863, d1231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d863, d1231, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3513 (pattern : Twelve) (guard : d1867 pattern = 1) : d867 pattern ≤ (0 : Int) + d1238 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d867, d1238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3511 pattern childGuard
    simpa only [d867, d1238, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d867, d1238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3512 pattern childGuard
    simpa only [d867, d1238, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3514 (pattern : Twelve) (guard : d1867 pattern = 1) : d869 pattern ≤ (0 : Int) + d1241 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d869, d1241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3494 pattern childGuard
    simpa only [d869, d1241, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d869, d1241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3513 pattern childGuard
    simpa only [d869, d1241, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3515 (pattern : Twelve) (guard : d1867 pattern = 1) : d838 pattern ≤ (0 : Int) + d1208 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d838, d1208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3265 pattern childGuard
    simpa only [d838, d1208, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d838, d1208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3487 pattern childGuard
    simpa only [d838, d1208, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3516 (pattern : Twelve) (guard : d1867 pattern = 1) : d853 pattern ≤ (0 : Int) + d1222 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d853, d1222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3515 pattern childGuard
    simpa only [d853, d1222, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d853, d1222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3489 pattern childGuard
    simpa only [d853, d1222, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3517 (pattern : Twelve) (guard : d1867 pattern = 1) : d861 pattern ≤ (0 : Int) + d1232 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d861, d1232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3516 pattern childGuard
    simpa only [d861, d1232, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d861, d1232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3492 pattern childGuard
    simpa only [d861, d1232, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3518 (pattern : Twelve) (guard : d1867 pattern = 1) : d842 pattern ≤ (0 : Int) + d1209 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d842, d1209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3329 pattern childGuard
    simpa only [d842, d1209, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d842, d1209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3496 pattern childGuard
    simpa only [d842, d1209, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3519 (pattern : Twelve) (guard : d1867 pattern = 1) : d855 pattern ≤ (0 : Int) + d1223 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d855, d1223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3518 pattern childGuard
    simpa only [d855, d1223, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d855, d1223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3498 pattern childGuard
    simpa only [d855, d1223, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3520 (pattern : Twelve) (guard : d1867 pattern = 1) : d862 pattern ≤ (0 : Int) + d1233 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d862, d1233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3519 pattern childGuard
    simpa only [d862, d1233, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d862, d1233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3510 pattern childGuard
    simpa only [d862, d1233, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3521 (pattern : Twelve) (guard : d1867 pattern = 1) : d867 pattern ≤ (0 : Int) + d1239 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d867, d1239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3520 pattern childGuard
    simpa only [d867, d1239, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d867, d1239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3512 pattern childGuard
    simpa only [d867, d1239, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3522 (pattern : Twelve) (guard : d1867 pattern = 1) : d869 pattern ≤ (0 : Int) + d1242 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d869, d1242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3517 pattern childGuard
    simpa only [d869, d1242, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d869, d1242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3521 pattern childGuard
    simpa only [d869, d1242, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3523 (pattern : Twelve) (guard : d1867 pattern = 1) : d869 pattern ≤ (0 : Int) + d1244 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3514 pattern childGuard
    simpa only [d1244, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3522 pattern childGuard
    simpa only [d1244, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3524 (pattern : Twelve) (guard : d1867 pattern = 1) : d869 pattern ≤ (0 : Int) + d1245 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3523 pattern childGuard
    simpa only [d1245, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3522 pattern childGuard
    simpa only [d1245, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3525 (pattern : Twelve) (guard : d0 pattern = 1) : d8 pattern ≤ (0 : Int) + d157 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3526 (pattern : Twelve) (guard : d1867 pattern = 1) : d872 pattern ≤ (0 : Int) + d157 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3258 pattern childGuard
    simpa only [d1867, d872, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3525 pattern childGuard
    simpa only [d1867, d872, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3527 (pattern : Twelve) (guard : d1867 pattern = 1) : d874 pattern ≤ (0 : Int) + d661 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d874, d661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3297 pattern childGuard
    simpa only [d874, d661, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d874, d661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3526 pattern childGuard
    simpa only [d874, d661, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3528 (pattern : Twelve) (guard : d1867 pattern = 1) : d875 pattern ≤ (0 : Int) + d1183 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d875, d1183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3469 pattern childGuard
    simpa only [d875, d1183, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d875, d1183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3526 pattern childGuard
    simpa only [d875, d1183, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3529 (pattern : Twelve) (guard : d1867 pattern = 1) : d882 pattern ≤ (0 : Int) + d1193 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d882, d1193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3527 pattern childGuard
    simpa only [d882, d1193, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d882, d1193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3528 pattern childGuard
    simpa only [d882, d1193, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3530 (pattern : Twelve) (guard : d1867 pattern = 1) : d890 pattern ≤ (0 : Int) + d1208 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d890, d1208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3265 pattern childGuard
    simpa only [d890, d1208, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d890, d1208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3529 pattern childGuard
    simpa only [d890, d1208, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3531 (pattern : Twelve) (guard : d1867 pattern = 1) : d876 pattern ≤ (0 : Int) + d1187 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d876, d1187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3274 pattern childGuard
    simpa only [d876, d1187, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d876, d1187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3298 pattern childGuard
    simpa only [d876, d1187, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3532 (pattern : Twelve) (guard : d1867 pattern = 1) : d883 pattern ≤ (0 : Int) + d1196 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d883, d1196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3531 pattern childGuard
    simpa only [d883, d1196, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d883, d1196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3375 pattern childGuard
    simpa only [d883, d1196, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3533 (pattern : Twelve) (guard : d1867 pattern = 1) : d891 pattern ≤ (0 : Int) + d1210 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d891, d1210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3297 pattern childGuard
    simpa only [d891, d1210, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d891, d1210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3532 pattern childGuard
    simpa only [d891, d1210, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3534 (pattern : Twelve) (guard : d1867 pattern = 1) : d898 pattern ≤ (0 : Int) + d1224 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d898, d1224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3530 pattern childGuard
    simpa only [d898, d1224, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d898, d1224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3533 pattern childGuard
    simpa only [d898, d1224, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3535 (pattern : Twelve) (guard : d1867 pattern = 1) : d877 pattern ≤ (0 : Int) + d674 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d877, d674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3297 pattern childGuard
    simpa only [d877, d674, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d877, d674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3501 pattern childGuard
    simpa only [d877, d674, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3536 (pattern : Twelve) (guard : d1867 pattern = 1) : d884 pattern ≤ (0 : Int) + d705 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d884, d705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3535 pattern childGuard
    simpa only [d884, d705, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d884, d705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3480 pattern childGuard
    simpa only [d884, d705, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3537 (pattern : Twelve) (guard : d1867 pattern = 1) : d892 pattern ≤ (0 : Int) + d731 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d892, d731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3333 pattern childGuard
    simpa only [d892, d731, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d892, d731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3536 pattern childGuard
    simpa only [d892, d731, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3538 (pattern : Twelve) (guard : d1867 pattern = 1) : d893 pattern ≤ (0 : Int) + d1211 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d893, d1211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3483 pattern childGuard
    simpa only [d893, d1211, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d893, d1211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3532 pattern childGuard
    simpa only [d893, d1211, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3539 (pattern : Twelve) (guard : d1867 pattern = 1) : d899 pattern ≤ (0 : Int) + d1225 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d899, d1225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3537 pattern childGuard
    simpa only [d899, d1225, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d899, d1225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3538 pattern childGuard
    simpa only [d899, d1225, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3540 (pattern : Twelve) (guard : d1867 pattern = 1) : d902 pattern ≤ (0 : Int) + d1234 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d902, d1234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3534 pattern childGuard
    simpa only [d902, d1234, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d902, d1234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3539 pattern childGuard
    simpa only [d902, d1234, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3541 (pattern : Twelve) (guard : d1867 pattern = 1) : d878 pattern ≤ (0 : Int) + d1188 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d878, d1188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3469 pattern childGuard
    simpa only [d878, d1188, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d878, d1188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3370 pattern childGuard
    simpa only [d878, d1188, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3542 (pattern : Twelve) (guard : d1867 pattern = 1) : d885 pattern ≤ (0 : Int) + d1197 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d885, d1197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3535 pattern childGuard
    simpa only [d885, d1197, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d885, d1197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3541 pattern childGuard
    simpa only [d885, d1197, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3543 (pattern : Twelve) (guard : d1867 pattern = 1) : d894 pattern ≤ (0 : Int) + d1212 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d894, d1212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3329 pattern childGuard
    simpa only [d894, d1212, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d894, d1212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3542 pattern childGuard
    simpa only [d894, d1212, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3544 (pattern : Twelve) (guard : d1867 pattern = 1) : d879 pattern ≤ (0 : Int) + d666 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d879, d666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3297 pattern childGuard
    simpa only [d879, d666, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d879, d666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3449 pattern childGuard
    simpa only [d879, d666, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3545 (pattern : Twelve) (guard : d1867 pattern = 1) : d886 pattern ≤ (0 : Int) + d704 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d886, d704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3306 pattern childGuard
    simpa only [d886, d704, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d886, d704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3544 pattern childGuard
    simpa only [d886, d704, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3546 (pattern : Twelve) (guard : d1867 pattern = 1) : d895 pattern ≤ (0 : Int) + d1213 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d895, d1213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3545 pattern childGuard
    simpa only [d895, d1213, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d895, d1213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3532 pattern childGuard
    simpa only [d895, d1213, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3547 (pattern : Twelve) (guard : d1867 pattern = 1) : d900 pattern ≤ (0 : Int) + d1226 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d900, d1226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3543 pattern childGuard
    simpa only [d900, d1226, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d900, d1226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3546 pattern childGuard
    simpa only [d900, d1226, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3548 (pattern : Twelve) (guard : d1866 pattern = 1) : d117 pattern ≤ (0 : Int) + d159 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1866, d117, d159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2922 pattern childGuard
    simpa only [d1866, d117, d159, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1866, d117, d159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1334 pattern childGuard
    simpa only [d1866, d117, d159, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3549 (pattern : Twelve) (guard : d1867 pattern = 1) : d873 pattern ≤ (0 : Int) + d639 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d873, d639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3548 pattern childGuard
    simpa only [d1867, d873, d639, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d873, d639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3369 pattern childGuard
    simpa only [d1867, d873, d639, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3550 (pattern : Twelve) (guard : d1867 pattern = 1) : d880 pattern ≤ (0 : Int) + d679 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d880, d679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3549 pattern childGuard
    simpa only [d880, d679, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d880, d679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d880, d679, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3551 (pattern : Twelve) (guard : d1867 pattern = 1) : d887 pattern ≤ (0 : Int) + d708 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d887, d708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3458 pattern childGuard
    simpa only [d887, d708, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d887, d708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3550 pattern childGuard
    simpa only [d887, d708, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3552 (pattern : Twelve) (guard : d1867 pattern = 1) : d896 pattern ≤ (0 : Int) + d1214 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d896, d1214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3368 pattern childGuard
    simpa only [d896, d1214, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d896, d1214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3551 pattern childGuard
    simpa only [d896, d1214, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3553 (pattern : Twelve) (guard : d1867 pattern = 1) : d881 pattern ≤ (0 : Int) + d676 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d881, d676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3305 pattern childGuard
    simpa only [d881, d676, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d881, d676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3446 pattern childGuard
    simpa only [d881, d676, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3554 (pattern : Twelve) (guard : d1867 pattern = 1) : d888 pattern ≤ (0 : Int) + d707 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d888, d707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3553 pattern childGuard
    simpa only [d888, d707, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d888, d707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3450 pattern childGuard
    simpa only [d888, d707, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3555 (pattern : Twelve) (guard : d1867 pattern = 1) : d889 pattern ≤ (0 : Int) + d1198 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d889, d1198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3375 pattern childGuard
    simpa only [d889, d1198, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d889, d1198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d889, d1198, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3556 (pattern : Twelve) (guard : d1867 pattern = 1) : d897 pattern ≤ (0 : Int) + d1215 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d897, d1215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3554 pattern childGuard
    simpa only [d897, d1215, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d897, d1215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3555 pattern childGuard
    simpa only [d897, d1215, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3557 (pattern : Twelve) (guard : d1867 pattern = 1) : d901 pattern ≤ (0 : Int) + d1227 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d901, d1227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3552 pattern childGuard
    simpa only [d901, d1227, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d901, d1227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3556 pattern childGuard
    simpa only [d901, d1227, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3558 (pattern : Twelve) (guard : d1867 pattern = 1) : d903 pattern ≤ (0 : Int) + d1235 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d903, d1235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3547 pattern childGuard
    simpa only [d903, d1235, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d903, d1235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3557 pattern childGuard
    simpa only [d903, d1235, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3559 (pattern : Twelve) (guard : d1867 pattern = 1) : d904 pattern ≤ (0 : Int) + d1236 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d904, d1236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3539 pattern childGuard
    simpa only [d904, d1236, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d904, d1236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d904, d1236, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3560 (pattern : Twelve) (guard : d1867 pattern = 1) : d905 pattern ≤ (0 : Int) + d1240 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d905, d1240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3558 pattern childGuard
    simpa only [d905, d1240, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d905, d1240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3559 pattern childGuard
    simpa only [d905, d1240, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3561 (pattern : Twelve) (guard : d1867 pattern = 1) : d906 pattern ≤ (0 : Int) + d1243 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d906, d1243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3540 pattern childGuard
    simpa only [d906, d1243, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d906, d1243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3560 pattern childGuard
    simpa only [d906, d1243, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3562 (pattern : Twelve) (guard : d1867 pattern = 1) : d907 pattern ≤ (0 : Int) + d1246 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d907, d1246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3524 pattern childGuard
    simpa only [d907, d1246, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d907, d1246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3561 pattern childGuard
    simpa only [d907, d1246, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3563 (pattern : Twelve) (guard : d1867 pattern = 1) : d1275 pattern ≤ (0 : Int) + d636 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d1275, d636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3468 pattern childGuard
    simpa only [d1867, d1275, d636, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d1275, d636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3525 pattern childGuard
    simpa only [d1867, d1275, d636, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3564 (pattern : Twelve) (guard : d1867 pattern = 1) : d1278 pattern ≤ (0 : Int) + d1183 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1278, d1183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3563 pattern childGuard
    simpa only [d1278, d1183, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1278, d1183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3526 pattern childGuard
    simpa only [d1278, d1183, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3565 (pattern : Twelve) (guard : d1867 pattern = 1) : d1284 pattern ≤ (0 : Int) + d1564 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1284, d1564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3564 pattern childGuard
    simpa only [d1284, d1564, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1284, d1564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3526 pattern childGuard
    simpa only [d1284, d1564, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3566 (pattern : Twelve) (guard : d1867 pattern = 1) : d1293 pattern ≤ (0 : Int) + d1576 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1293, d1576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3474 pattern childGuard
    simpa only [d1293, d1576, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1293, d1576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3565 pattern childGuard
    simpa only [d1293, d1576, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3567 (pattern : Twelve) (guard : d1867 pattern = 1) : d1294 pattern ≤ (0 : Int) + d1577 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1294, d1577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3274 pattern childGuard
    simpa only [d1294, d1577, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1294, d1577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d1294, d1577, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3568 (pattern : Twelve) (guard : d1867 pattern = 1) : d1305 pattern ≤ (0 : Int) + d1591 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1305, d1591, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3566 pattern childGuard
    simpa only [d1305, d1591, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1305, d1591, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3567 pattern childGuard
    simpa only [d1305, d1591, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3569 (pattern : Twelve) (guard : d1867 pattern = 1) : d1276 pattern ≤ (0 : Int) + d644 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d1276, d644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3500 pattern childGuard
    simpa only [d1867, d1276, d644, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d1276, d644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3448 pattern childGuard
    simpa only [d1867, d1276, d644, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3570 (pattern : Twelve) (guard : d1867 pattern = 1) : d1279 pattern ≤ (0 : Int) + d1184 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1279, d1184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3563 pattern childGuard
    simpa only [d1279, d1184, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1279, d1184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3569 pattern childGuard
    simpa only [d1279, d1184, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3571 (pattern : Twelve) (guard : d1867 pattern = 1) : d1280 pattern ≤ (0 : Int) + d1557 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1280, d1557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3526 pattern childGuard
    simpa only [d1280, d1557, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1280, d1557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d1280, d1557, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3572 (pattern : Twelve) (guard : d1867 pattern = 1) : d1285 pattern ≤ (0 : Int) + d1565 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1285, d1565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3570 pattern childGuard
    simpa only [d1285, d1565, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1285, d1565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3571 pattern childGuard
    simpa only [d1285, d1565, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3573 (pattern : Twelve) (guard : d1867 pattern = 1) : d1295 pattern ≤ (0 : Int) + d1578 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1295, d1578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3483 pattern childGuard
    simpa only [d1295, d1578, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1295, d1578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3572 pattern childGuard
    simpa only [d1295, d1578, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3574 (pattern : Twelve) (guard : d1867 pattern = 1) : d1286 pattern ≤ (0 : Int) + d1566 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1286, d1566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3475 pattern childGuard
    simpa only [d1286, d1566, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1286, d1566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3276 pattern childGuard
    simpa only [d1286, d1566, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3575 (pattern : Twelve) (guard : d1867 pattern = 1) : d1296 pattern ≤ (0 : Int) + d1579 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1296, d1579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3574 pattern childGuard
    simpa only [d1296, d1579, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1296, d1579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d1296, d1579, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3576 (pattern : Twelve) (guard : d1867 pattern = 1) : d1306 pattern ≤ (0 : Int) + d1592 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1306, d1592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3573 pattern childGuard
    simpa only [d1306, d1592, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1306, d1592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3575 pattern childGuard
    simpa only [d1306, d1592, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3577 (pattern : Twelve) (guard : d1867 pattern = 1) : d1313 pattern ≤ (0 : Int) + d1600 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1313, d1600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3568 pattern childGuard
    simpa only [d1313, d1600, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1313, d1600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3576 pattern childGuard
    simpa only [d1313, d1600, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3578 (pattern : Twelve) (guard : d1867 pattern = 1) : d1293 pattern ≤ (0 : Int) + d1580 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1293, d1580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3297 pattern childGuard
    simpa only [d1293, d1580, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1293, d1580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3565 pattern childGuard
    simpa only [d1293, d1580, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3579 (pattern : Twelve) (guard : d1867 pattern = 1) : d1305 pattern ≤ (0 : Int) + d1593 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1305, d1593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3578 pattern childGuard
    simpa only [d1305, d1593, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1305, d1593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3567 pattern childGuard
    simpa only [d1305, d1593, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3580 (pattern : Twelve) (guard : d1867 pattern = 1) : d1313 pattern ≤ (0 : Int) + d1601 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1313, d1601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3579 pattern childGuard
    simpa only [d1313, d1601, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1313, d1601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3576 pattern childGuard
    simpa only [d1313, d1601, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3581 (pattern : Twelve) (guard : d1867 pattern = 1) : d1313 pattern ≤ (0 : Int) + d1607 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3577 pattern childGuard
    simpa only [d1607, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3580 pattern childGuard
    simpa only [d1607, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3582 (pattern : Twelve) (guard : d1867 pattern = 1) : d1281 pattern ≤ (0 : Int) + d1558 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1281, d1558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3526 pattern childGuard
    simpa only [d1281, d1558, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1281, d1558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3449 pattern childGuard
    simpa only [d1281, d1558, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3583 (pattern : Twelve) (guard : d1867 pattern = 1) : d1287 pattern ≤ (0 : Int) + d1567 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1287, d1567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3570 pattern childGuard
    simpa only [d1287, d1567, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1287, d1567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3582 pattern childGuard
    simpa only [d1287, d1567, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3584 (pattern : Twelve) (guard : d1867 pattern = 1) : d1297 pattern ≤ (0 : Int) + d1581 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1297, d1581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3306 pattern childGuard
    simpa only [d1297, d1581, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1297, d1581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3583 pattern childGuard
    simpa only [d1297, d1581, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3585 (pattern : Twelve) (guard : d1867 pattern = 1) : d1298 pattern ≤ (0 : Int) + d1582 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1298, d1582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3475 pattern childGuard
    simpa only [d1298, d1582, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1298, d1582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d1298, d1582, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3586 (pattern : Twelve) (guard : d1867 pattern = 1) : d1307 pattern ≤ (0 : Int) + d1594 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1307, d1594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3584 pattern childGuard
    simpa only [d1307, d1594, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1307, d1594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3585 pattern childGuard
    simpa only [d1307, d1594, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3587 (pattern : Twelve) (guard : d1866 pattern = 1) : d15 pattern ≤ (0 : Int) + d13 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1866, d15, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2933 pattern childGuard
    simpa only [d1866, d15, d13, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1866, d15, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3025 pattern childGuard
    simpa only [d1866, d15, d13, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3588 (pattern : Twelve) (guard : d1867 pattern = 1) : d1277 pattern ≤ (0 : Int) + d21 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d1277, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3587 pattern childGuard
    simpa only [d1867, d1277, d21, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d1277, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3445 pattern childGuard
    simpa only [d1867, d1277, d21, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3589 (pattern : Twelve) (guard : d1867 pattern = 1) : d1282 pattern ≤ (0 : Int) + d1186 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1282, d1186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3569 pattern childGuard
    simpa only [d1282, d1186, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1282, d1186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3588 pattern childGuard
    simpa only [d1282, d1186, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3590 (pattern : Twelve) (guard : d1867 pattern = 1) : d1288 pattern ≤ (0 : Int) + d1568 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1288, d1568, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3589 pattern childGuard
    simpa only [d1288, d1568, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1288, d1568, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3450 pattern childGuard
    simpa only [d1288, d1568, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3591 (pattern : Twelve) (guard : d1867 pattern = 1) : d1299 pattern ≤ (0 : Int) + d1583 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1299, d1583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3505 pattern childGuard
    simpa only [d1299, d1583, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1299, d1583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3590 pattern childGuard
    simpa only [d1299, d1583, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3592 (pattern : Twelve) (guard : d1867 pattern = 1) : d1289 pattern ≤ (0 : Int) + d1569 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1289, d1569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3506 pattern childGuard
    simpa only [d1289, d1569, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1289, d1569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3375 pattern childGuard
    simpa only [d1289, d1569, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3593 (pattern : Twelve) (guard : d1867 pattern = 1) : d1300 pattern ≤ (0 : Int) + d1584 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1300, d1584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3592 pattern childGuard
    simpa only [d1300, d1584, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1300, d1584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d1300, d1584, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3594 (pattern : Twelve) (guard : d1867 pattern = 1) : d1308 pattern ≤ (0 : Int) + d1595 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1308, d1595, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3591 pattern childGuard
    simpa only [d1308, d1595, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1308, d1595, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3593 pattern childGuard
    simpa only [d1308, d1595, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3595 (pattern : Twelve) (guard : d1867 pattern = 1) : d1314 pattern ≤ (0 : Int) + d1602 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1314, d1602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3586 pattern childGuard
    simpa only [d1314, d1602, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1314, d1602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3594 pattern childGuard
    simpa only [d1314, d1602, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3596 (pattern : Twelve) (guard : d1867 pattern = 1) : d1315 pattern ≤ (0 : Int) + d1603 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1315, d1603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3576 pattern childGuard
    simpa only [d1315, d1603, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1315, d1603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d1315, d1603, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3597 (pattern : Twelve) (guard : d1867 pattern = 1) : d1319 pattern ≤ (0 : Int) + d1608 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1319, d1608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3595 pattern childGuard
    simpa only [d1319, d1608, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1319, d1608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3596 pattern childGuard
    simpa only [d1319, d1608, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3598 (pattern : Twelve) (guard : d1867 pattern = 1) : d1321 pattern ≤ (0 : Int) + d1610 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1321, d1610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3581 pattern childGuard
    simpa only [d1321, d1610, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1321, d1610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3597 pattern childGuard
    simpa only [d1321, d1610, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3599 (pattern : Twelve) (guard : d1867 pattern = 1) : d1321 pattern ≤ (0 : Int) + d1611 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1321, d1611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3580 pattern childGuard
    simpa only [d1321, d1611, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1321, d1611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3597 pattern childGuard
    simpa only [d1321, d1611, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3600 (pattern : Twelve) (guard : d1867 pattern = 1) : d1321 pattern ≤ (0 : Int) + d1613 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3598 pattern childGuard
    simpa only [d1613, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3599 pattern childGuard
    simpa only [d1613, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3601 (pattern : Twelve) (guard : d1867 pattern = 1) : d1321 pattern ≤ (0 : Int) + d1614 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3600 pattern childGuard
    simpa only [d1614, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3599 pattern childGuard
    simpa only [d1614, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3602 (pattern : Twelve) (guard : d1866 pattern = 1) : d11 pattern ≤ (0 : Int) + d157 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1866, d11, d157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2831 pattern childGuard
    simpa only [d1866, d11, d157, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1866, d11, d157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2923 pattern childGuard
    simpa only [d1866, d11, d157, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3603 (pattern : Twelve) (guard : d0 pattern = 1) : d16 pattern ≤ (0 : Int) + d160 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3604 (pattern : Twelve) (guard : d1867 pattern = 1) : d1324 pattern ≤ (0 : Int) + d635 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d1324, d635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3602 pattern childGuard
    simpa only [d1867, d1324, d635, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d1324, d635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3603 pattern childGuard
    simpa only [d1867, d1324, d635, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3605 (pattern : Twelve) (guard : d1867 pattern = 1) : d1325 pattern ≤ (0 : Int) + d1559 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1325, d1559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3563 pattern childGuard
    simpa only [d1325, d1559, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1325, d1559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3604 pattern childGuard
    simpa only [d1325, d1559, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3606 (pattern : Twelve) (guard : d1867 pattern = 1) : d1326 pattern ≤ (0 : Int) + d1560 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1326, d1560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3526 pattern childGuard
    simpa only [d1326, d1560, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1326, d1560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3604 pattern childGuard
    simpa only [d1326, d1560, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3607 (pattern : Twelve) (guard : d1867 pattern = 1) : d1333 pattern ≤ (0 : Int) + d1570 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1333, d1570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3605 pattern childGuard
    simpa only [d1333, d1570, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1333, d1570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3606 pattern childGuard
    simpa only [d1333, d1570, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3608 (pattern : Twelve) (guard : d1867 pattern = 1) : d1339 pattern ≤ (0 : Int) + d1585 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1339, d1585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3297 pattern childGuard
    simpa only [d1339, d1585, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1339, d1585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3607 pattern childGuard
    simpa only [d1339, d1585, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3609 (pattern : Twelve) (guard : d1867 pattern = 1) : d1345 pattern ≤ (0 : Int) + d1596 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1345, d1596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3608 pattern childGuard
    simpa only [d1345, d1596, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1345, d1596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3567 pattern childGuard
    simpa only [d1345, d1596, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3610 (pattern : Twelve) (guard : d1867 pattern = 1) : d1327 pattern ≤ (0 : Int) + d1185 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1327, d1185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3563 pattern childGuard
    simpa only [d1327, d1185, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1327, d1185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3449 pattern childGuard
    simpa only [d1327, d1185, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3611 (pattern : Twelve) (guard : d1867 pattern = 1) : d1334 pattern ≤ (0 : Int) + d1571 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1334, d1571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3610 pattern childGuard
    simpa only [d1334, d1571, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1334, d1571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3571 pattern childGuard
    simpa only [d1334, d1571, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3612 (pattern : Twelve) (guard : d1867 pattern = 1) : d1340 pattern ≤ (0 : Int) + d1586 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1340, d1586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3483 pattern childGuard
    simpa only [d1340, d1586, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1340, d1586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3611 pattern childGuard
    simpa only [d1340, d1586, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3613 (pattern : Twelve) (guard : d1867 pattern = 1) : d1346 pattern ≤ (0 : Int) + d1597 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1346, d1597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3612 pattern childGuard
    simpa only [d1346, d1597, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1346, d1597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3575 pattern childGuard
    simpa only [d1346, d1597, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3614 (pattern : Twelve) (guard : d1867 pattern = 1) : d1349 pattern ≤ (0 : Int) + d1604 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1349, d1604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3609 pattern childGuard
    simpa only [d1349, d1604, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1349, d1604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3613 pattern childGuard
    simpa only [d1349, d1604, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3615 (pattern : Twelve) (guard : d1867 pattern = 1) : d1328 pattern ≤ (0 : Int) + d1561 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1328, d1561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3526 pattern childGuard
    simpa only [d1328, d1561, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1328, d1561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3588 pattern childGuard
    simpa only [d1328, d1561, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3616 (pattern : Twelve) (guard : d1867 pattern = 1) : d1335 pattern ≤ (0 : Int) + d1572 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1335, d1572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3610 pattern childGuard
    simpa only [d1335, d1572, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1335, d1572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3615 pattern childGuard
    simpa only [d1335, d1572, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3617 (pattern : Twelve) (guard : d1867 pattern = 1) : d1341 pattern ≤ (0 : Int) + d1587 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1341, d1587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3306 pattern childGuard
    simpa only [d1341, d1587, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1341, d1587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3616 pattern childGuard
    simpa only [d1341, d1587, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3618 (pattern : Twelve) (guard : d1867 pattern = 1) : d1329 pattern ≤ (0 : Int) + d1562 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1329, d1562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3274 pattern childGuard
    simpa only [d1329, d1562, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1329, d1562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3291 pattern childGuard
    simpa only [d1329, d1562, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3619 (pattern : Twelve) (guard : d1867 pattern = 1) : d1336 pattern ≤ (0 : Int) + d1573 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1336, d1573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3475 pattern childGuard
    simpa only [d1336, d1573, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1336, d1573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3618 pattern childGuard
    simpa only [d1336, d1573, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3620 (pattern : Twelve) (guard : d1867 pattern = 1) : d1342 pattern ≤ (0 : Int) + d1588 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1342, d1588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3619 pattern childGuard
    simpa only [d1342, d1588, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1342, d1588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d1342, d1588, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3621 (pattern : Twelve) (guard : d1867 pattern = 1) : d1347 pattern ≤ (0 : Int) + d1598 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1347, d1598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3617 pattern childGuard
    simpa only [d1347, d1598, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1347, d1598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3620 pattern childGuard
    simpa only [d1347, d1598, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3622 (pattern : Twelve) (guard : d1867 pattern = 1) : d1330 pattern ≤ (0 : Int) + d670 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1330, d670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3569 pattern childGuard
    simpa only [d1330, d670, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1330, d670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d1330, d670, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3623 (pattern : Twelve) (guard : d1867 pattern = 1) : d1331 pattern ≤ (0 : Int) + d822 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1331, d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3588 pattern childGuard
    simpa only [d1331, d822, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1331, d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d1331, d822, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3624 (pattern : Twelve) (guard : d1867 pattern = 1) : d1337 pattern ≤ (0 : Int) + d1574 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1337, d1574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3622 pattern childGuard
    simpa only [d1337, d1574, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1337, d1574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3623 pattern childGuard
    simpa only [d1337, d1574, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3625 (pattern : Twelve) (guard : d1867 pattern = 1) : d1343 pattern ≤ (0 : Int) + d1589 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1343, d1589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3505 pattern childGuard
    simpa only [d1343, d1589, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1343, d1589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3624 pattern childGuard
    simpa only [d1343, d1589, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3626 (pattern : Twelve) (guard : d1867 pattern = 1) : d1332 pattern ≤ (0 : Int) + d1563 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1332, d1563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3374 pattern childGuard
    simpa only [d1332, d1563, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1332, d1563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3302 pattern childGuard
    simpa only [d1332, d1563, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3627 (pattern : Twelve) (guard : d1867 pattern = 1) : d1338 pattern ≤ (0 : Int) + d1575 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1338, d1575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3626 pattern childGuard
    simpa only [d1338, d1575, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1338, d1575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3459 pattern childGuard
    simpa only [d1338, d1575, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3628 (pattern : Twelve) (guard : d1867 pattern = 1) : d1344 pattern ≤ (0 : Int) + d1590 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1344, d1590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3627 pattern childGuard
    simpa only [d1344, d1590, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1344, d1590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d1344, d1590, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3629 (pattern : Twelve) (guard : d1867 pattern = 1) : d1348 pattern ≤ (0 : Int) + d1599 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1348, d1599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3625 pattern childGuard
    simpa only [d1348, d1599, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1348, d1599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3628 pattern childGuard
    simpa only [d1348, d1599, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3630 (pattern : Twelve) (guard : d1867 pattern = 1) : d1350 pattern ≤ (0 : Int) + d1605 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1350, d1605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3621 pattern childGuard
    simpa only [d1350, d1605, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1350, d1605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3629 pattern childGuard
    simpa only [d1350, d1605, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3631 (pattern : Twelve) (guard : d1867 pattern = 1) : d1351 pattern ≤ (0 : Int) + d1606 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1351, d1606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3613 pattern childGuard
    simpa only [d1351, d1606, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1351, d1606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d1351, d1606, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3632 (pattern : Twelve) (guard : d1867 pattern = 1) : d1352 pattern ≤ (0 : Int) + d1609 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1352, d1609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3630 pattern childGuard
    simpa only [d1352, d1609, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1352, d1609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3631 pattern childGuard
    simpa only [d1352, d1609, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3633 (pattern : Twelve) (guard : d1867 pattern = 1) : d1353 pattern ≤ (0 : Int) + d1612 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1353, d1612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3614 pattern childGuard
    simpa only [d1353, d1612, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1353, d1612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3632 pattern childGuard
    simpa only [d1353, d1612, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3634 (pattern : Twelve) (guard : d1867 pattern = 1) : d1354 pattern ≤ (0 : Int) + d1615 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1354, d1615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3601 pattern childGuard
    simpa only [d1354, d1615, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1354, d1615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3633 pattern childGuard
    simpa only [d1354, d1615, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3635 (pattern : Twelve) (guard : d1867 pattern = 1) : d1649 pattern ≤ (0 : Int) + d1788 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1649, d1788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3274 pattern childGuard
    simpa only [d1649, d1788, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1649, d1788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3604 pattern childGuard
    simpa only [d1649, d1788, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3636 (pattern : Twelve) (guard : d1867 pattern = 1) : d1650 pattern ≤ (0 : Int) + d1789 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1650, d1789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3374 pattern childGuard
    simpa only [d1650, d1789, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1650, d1789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d1650, d1789, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3637 (pattern : Twelve) (guard : d1867 pattern = 1) : d1656 pattern ≤ (0 : Int) + d1797 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1656, d1797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3635 pattern childGuard
    simpa only [d1656, d1797, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1656, d1797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3636 pattern childGuard
    simpa only [d1656, d1797, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3638 (pattern : Twelve) (guard : d1867 pattern = 1) : d1644 pattern ≤ (0 : Int) + d1780 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1644, d1780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3604 pattern childGuard
    simpa only [d1644, d1780, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1644, d1780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3291 pattern childGuard
    simpa only [d1644, d1780, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3639 (pattern : Twelve) (guard : d1867 pattern = 1) : d1645 pattern ≤ (0 : Int) + d1781 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1645, d1781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3604 pattern childGuard
    simpa only [d1645, d1781, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1645, d1781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d1645, d1781, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
