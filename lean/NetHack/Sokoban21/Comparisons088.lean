/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons087
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c12320 (pattern : Twelve) (guard : d1865 pattern = 1) : d518 pattern ≤ (1 : Int) + d819 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d518, d819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12262 pattern childGuard
    simpa only [d518, d819, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d518, d819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12319 pattern childGuard
    simpa only [d518, d819, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12321 (pattern : Twelve) (guard : d1865 pattern = 1) : d546 pattern ≤ (1 : Int) + d828 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d546, d828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12317 pattern childGuard
    simpa only [d546, d828, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d546, d828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12320 pattern childGuard
    simpa only [d546, d828, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12322 (pattern : Twelve) (guard : d1865 pattern = 1) : d569 pattern ≤ (1 : Int) + d842 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d569, d842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12314 pattern childGuard
    simpa only [d569, d842, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d569, d842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12321 pattern childGuard
    simpa only [d569, d842, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12323 (pattern : Twelve) (guard : d1865 pattern = 1) : d547 pattern ≤ (1 : Int) + d34 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12317 pattern childGuard
    simpa only [d547, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12298 pattern childGuard
    simpa only [d547, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12324 (pattern : Twelve) (guard : d1865 pattern = 1) : d570 pattern ≤ (1 : Int) + d843 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d570, d843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12323 pattern childGuard
    simpa only [d570, d843, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d570, d843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12274 pattern childGuard
    simpa only [d570, d843, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12325 (pattern : Twelve) (guard : d1865 pattern = 1) : d592 pattern ≤ (1 : Int) + d855 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d592, d855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12322 pattern childGuard
    simpa only [d592, d855, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d592, d855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12324 pattern childGuard
    simpa only [d592, d855, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12326 (pattern : Twelve) (guard : d0 pattern = 1) : d14 pattern ≤ (1 : Int) + d2 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c12327 (pattern : Twelve) (guard : d1865 pattern = 1) : d493 pattern ≤ (1 : Int) + d2 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11127 pattern childGuard
    simpa only [d1865, d493, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12326 pattern childGuard
    simpa only [d1865, d493, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12328 (pattern : Twelve) (guard : d1865 pattern = 1) : d494 pattern ≤ (1 : Int) + d4 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12142 pattern childGuard
    simpa only [d1865, d494, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11128 pattern childGuard
    simpa only [d1865, d494, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12329 (pattern : Twelve) (guard : d1865 pattern = 1) : d519 pattern ≤ (1 : Int) + d38 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d519, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12327 pattern childGuard
    simpa only [d519, d38, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d519, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12328 pattern childGuard
    simpa only [d519, d38, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12330 (pattern : Twelve) (guard : d1865 pattern = 1) : d520 pattern ≤ (1 : Int) + d39 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d520, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12294 pattern childGuard
    simpa only [d520, d39, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d520, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12242 pattern childGuard
    simpa only [d520, d39, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12331 (pattern : Twelve) (guard : d1865 pattern = 1) : d548 pattern ≤ (1 : Int) + d59 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d548, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12329 pattern childGuard
    simpa only [d548, d59, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d548, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12330 pattern childGuard
    simpa only [d548, d59, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12332 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (1 : Int) + d15 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c12333 (pattern : Twelve) (guard : d1865 pattern = 1) : d494 pattern ≤ (1 : Int) + d24 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d494, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12142 pattern childGuard
    simpa only [d1865, d494, d24, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d494, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12332 pattern childGuard
    simpa only [d1865, d494, d24, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12334 (pattern : Twelve) (guard : d1865 pattern = 1) : d521 pattern ≤ (1 : Int) + d41 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d521, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12260 pattern childGuard
    simpa only [d521, d41, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d521, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12333 pattern childGuard
    simpa only [d521, d41, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12335 (pattern : Twelve) (guard : d1865 pattern = 1) : d487 pattern ≤ (1 : Int) + d815 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d487, d815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11138 pattern childGuard
    simpa only [d1865, d487, d815, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d487, d815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12318 pattern childGuard
    simpa only [d1865, d487, d815, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12336 (pattern : Twelve) (guard : d1865 pattern = 1) : d520 pattern ≤ (1 : Int) + d820 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d520, d820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12335 pattern childGuard
    simpa only [d520, d820, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d520, d820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12242 pattern childGuard
    simpa only [d520, d820, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12337 (pattern : Twelve) (guard : d1865 pattern = 1) : d549 pattern ≤ (1 : Int) + d829 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d549, d829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12334 pattern childGuard
    simpa only [d549, d829, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d549, d829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12336 pattern childGuard
    simpa only [d549, d829, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12338 (pattern : Twelve) (guard : d1865 pattern = 1) : d571 pattern ≤ (1 : Int) + d844 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d571, d844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12331 pattern childGuard
    simpa only [d571, d844, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d571, d844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12337 pattern childGuard
    simpa only [d571, d844, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12339 (pattern : Twelve) (guard : d1865 pattern = 1) : d520 pattern ≤ (1 : Int) + d40 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d520, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12260 pattern childGuard
    simpa only [d520, d40, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d520, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12242 pattern childGuard
    simpa only [d520, d40, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12340 (pattern : Twelve) (guard : d1865 pattern = 1) : d549 pattern ≤ (1 : Int) + d830 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d549, d830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12334 pattern childGuard
    simpa only [d549, d830, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d549, d830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12339 pattern childGuard
    simpa only [d549, d830, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12341 (pattern : Twelve) (guard : d1 pattern = 1) : d4 pattern ≤ (1 : Int) + d13 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12142 pattern childGuard
    simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11231 pattern childGuard
    simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12342 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (1 : Int) + d14 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c12343 (pattern : Twelve) (guard : d1865 pattern = 1) : d494 pattern ≤ (1 : Int) + d21 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d494, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12341 pattern childGuard
    simpa only [d1865, d494, d21, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d494, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12342 pattern childGuard
    simpa only [d1865, d494, d21, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12344 (pattern : Twelve) (guard : d1865 pattern = 1) : d521 pattern ≤ (1 : Int) + d821 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d521, d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12272 pattern childGuard
    simpa only [d521, d821, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d521, d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12343 pattern childGuard
    simpa only [d521, d821, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12345 (pattern : Twelve) (guard : d1865 pattern = 1) : d495 pattern ≤ (1 : Int) + d21 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d495, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11371 pattern childGuard
    simpa only [d1865, d495, d21, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d495, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12342 pattern childGuard
    simpa only [d1865, d495, d21, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12346 (pattern : Twelve) (guard : d1865 pattern = 1) : d522 pattern ≤ (1 : Int) + d822 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d522, d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12345 pattern childGuard
    simpa only [d522, d822, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d522, d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12242 pattern childGuard
    simpa only [d522, d822, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12347 (pattern : Twelve) (guard : d1865 pattern = 1) : d550 pattern ≤ (1 : Int) + d831 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d550, d831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12344 pattern childGuard
    simpa only [d550, d831, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d550, d831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12346 pattern childGuard
    simpa only [d550, d831, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12348 (pattern : Twelve) (guard : d1865 pattern = 1) : d572 pattern ≤ (1 : Int) + d845 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d572, d845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12340 pattern childGuard
    simpa only [d572, d845, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d572, d845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12347 pattern childGuard
    simpa only [d572, d845, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12349 (pattern : Twelve) (guard : d1865 pattern = 1) : d593 pattern ≤ (1 : Int) + d856 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d593, d856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12338 pattern childGuard
    simpa only [d593, d856, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d593, d856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12348 pattern childGuard
    simpa only [d593, d856, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12350 (pattern : Twelve) (guard : d1865 pattern = 1) : d608 pattern ≤ (1 : Int) + d862 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d608, d862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12325 pattern childGuard
    simpa only [d608, d862, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d608, d862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12349 pattern childGuard
    simpa only [d608, d862, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12351 (pattern : Twelve) (guard : d0 pattern = 1) : d14 pattern ≤ (1 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c12352 (pattern : Twelve) (guard : d1865 pattern = 1) : d496 pattern ≤ (1 : Int) + d0 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11049 pattern childGuard
    simpa only [d1865, d496, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12351 pattern childGuard
    simpa only [d1865, d496, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12353 (pattern : Twelve) (guard : d1865 pattern = 1) : d523 pattern ≤ (1 : Int) + d30 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d523, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12352 pattern childGuard
    simpa only [d523, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d523, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12294 pattern childGuard
    simpa only [d523, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12354 (pattern : Twelve) (guard : d1865 pattern = 1) : d551 pattern ≤ (1 : Int) + d56 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d551, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12353 pattern childGuard
    simpa only [d551, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d551, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12296 pattern childGuard
    simpa only [d551, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12355 (pattern : Twelve) (guard : d1865 pattern = 1) : d573 pattern ≤ (1 : Int) + d840 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d573, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12354 pattern childGuard
    simpa only [d573, d840, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d573, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12300 pattern childGuard
    simpa only [d573, d840, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12356 (pattern : Twelve) (guard : d1865 pattern = 1) : d594 pattern ≤ (1 : Int) + d854 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d594, d854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12355 pattern childGuard
    simpa only [d594, d854, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d594, d854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12304 pattern childGuard
    simpa only [d594, d854, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12357 (pattern : Twelve) (guard : d1865 pattern = 1) : d609 pattern ≤ (1 : Int) + d863 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d609, d863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12356 pattern childGuard
    simpa only [d609, d863, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d609, d863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12242 pattern childGuard
    simpa only [d609, d863, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12358 (pattern : Twelve) (guard : d1865 pattern = 1) : d619 pattern ≤ (1 : Int) + d867 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d619, d867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12350 pattern childGuard
    simpa only [d619, d867, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d619, d867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12357 pattern childGuard
    simpa only [d619, d867, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12359 (pattern : Twelve) (guard : d1865 pattern = 1) : d624 pattern ≤ (1 : Int) + d869 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d624, d869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12307 pattern childGuard
    simpa only [d624, d869, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d624, d869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12358 pattern childGuard
    simpa only [d624, d869, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12360 (pattern : Twelve) (guard : d1865 pattern = 1) : d513 pattern ≤ (1 : Int) + d27 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d513, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12233 pattern childGuard
    simpa only [d513, d27, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d513, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12223 pattern childGuard
    simpa only [d513, d27, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12361 (pattern : Twelve) (guard : d1865 pattern = 1) : d513 pattern ≤ (1 : Int) + d824 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12360 pattern childGuard
    simpa only [d824, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12285 pattern childGuard
    simpa only [d824, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12362 (pattern : Twelve) (guard : d1865 pattern = 1) : d574 pattern ≤ (1 : Int) + d838 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d574, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12281 pattern childGuard
    simpa only [d574, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d574, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12361 pattern childGuard
    simpa only [d574, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12363 (pattern : Twelve) (guard : d1865 pattern = 1) : d524 pattern ≤ (1 : Int) + d817 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d524, d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12271 pattern childGuard
    simpa only [d524, d817, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d524, d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12239 pattern childGuard
    simpa only [d524, d817, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12364 (pattern : Twelve) (guard : d1865 pattern = 1) : d552 pattern ≤ (1 : Int) + d825 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d552, d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12363 pattern childGuard
    simpa only [d552, d825, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d552, d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12243 pattern childGuard
    simpa only [d552, d825, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12365 (pattern : Twelve) (guard : d1865 pattern = 1) : d575 pattern ≤ (1 : Int) + d839 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d575, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12233 pattern childGuard
    simpa only [d575, d839, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d575, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12364 pattern childGuard
    simpa only [d575, d839, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12366 (pattern : Twelve) (guard : d1865 pattern = 1) : d595 pattern ≤ (1 : Int) + d853 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d595, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12362 pattern childGuard
    simpa only [d595, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d595, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12365 pattern childGuard
    simpa only [d595, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12367 (pattern : Twelve) (guard : d1865 pattern = 1) : d509 pattern ≤ (1 : Int) + d30 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d509, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12281 pattern childGuard
    simpa only [d509, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d509, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12294 pattern childGuard
    simpa only [d509, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12368 (pattern : Twelve) (guard : d1865 pattern = 1) : d525 pattern ≤ (1 : Int) + d35 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d525, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12281 pattern childGuard
    simpa only [d525, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d525, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12254 pattern childGuard
    simpa only [d525, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12369 (pattern : Twelve) (guard : d1865 pattern = 1) : d553 pattern ≤ (1 : Int) + d56 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d553, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12367 pattern childGuard
    simpa only [d553, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d553, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12368 pattern childGuard
    simpa only [d553, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12370 (pattern : Twelve) (guard : d1865 pattern = 1) : d554 pattern ≤ (1 : Int) + d826 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d554, d826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12298 pattern childGuard
    simpa only [d554, d826, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d554, d826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12264 pattern childGuard
    simpa only [d554, d826, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12371 (pattern : Twelve) (guard : d1865 pattern = 1) : d576 pattern ≤ (1 : Int) + d840 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d576, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12369 pattern childGuard
    simpa only [d576, d840, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d576, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12370 pattern childGuard
    simpa only [d576, d840, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12372 (pattern : Twelve) (guard : d1865 pattern = 1) : d555 pattern ≤ (1 : Int) + d827 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d555, d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12298 pattern childGuard
    simpa only [d555, d827, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d555, d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12268 pattern childGuard
    simpa only [d555, d827, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12373 (pattern : Twelve) (guard : d1865 pattern = 1) : d577 pattern ≤ (1 : Int) + d841 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d577, d841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12372 pattern childGuard
    simpa only [d577, d841, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d577, d841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12274 pattern childGuard
    simpa only [d577, d841, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12374 (pattern : Twelve) (guard : d1865 pattern = 1) : d596 pattern ≤ (1 : Int) + d854 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d596, d854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12371 pattern childGuard
    simpa only [d596, d854, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d596, d854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12373 pattern childGuard
    simpa only [d596, d854, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12375 (pattern : Twelve) (guard : d1865 pattern = 1) : d610 pattern ≤ (1 : Int) + d861 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d610, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12366 pattern childGuard
    simpa only [d610, d861, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d610, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12374 pattern childGuard
    simpa only [d610, d861, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12376 (pattern : Twelve) (guard : d1865 pattern = 1) : d578 pattern ≤ (1 : Int) + d839 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d578, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12233 pattern childGuard
    simpa only [d578, d839, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d578, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12274 pattern childGuard
    simpa only [d578, d839, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12377 (pattern : Twelve) (guard : d1865 pattern = 1) : d597 pattern ≤ (1 : Int) + d853 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d597, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12362 pattern childGuard
    simpa only [d597, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d597, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12376 pattern childGuard
    simpa only [d597, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12378 (pattern : Twelve) (guard : d1865 pattern = 1) : d544 pattern ≤ (1 : Int) + d56 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d544, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12367 pattern childGuard
    simpa only [d544, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d544, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12296 pattern childGuard
    simpa only [d544, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12379 (pattern : Twelve) (guard : d1865 pattern = 1) : d544 pattern ≤ (1 : Int) + d840 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12378 pattern childGuard
    simpa only [d840, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12300 pattern childGuard
    simpa only [d840, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12380 (pattern : Twelve) (guard : d1865 pattern = 1) : d598 pattern ≤ (1 : Int) + d854 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d598, d854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12379 pattern childGuard
    simpa only [d598, d854, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d598, d854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12304 pattern childGuard
    simpa only [d598, d854, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12381 (pattern : Twelve) (guard : d1865 pattern = 1) : d611 pattern ≤ (1 : Int) + d861 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d611, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12377 pattern childGuard
    simpa only [d611, d861, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d611, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12380 pattern childGuard
    simpa only [d611, d861, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12382 (pattern : Twelve) (guard : d1865 pattern = 1) : d620 pattern ≤ (1 : Int) + d861 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12375 pattern childGuard
    simpa only [d620, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12381 pattern childGuard
    simpa only [d620, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12383 (pattern : Twelve) (guard : d1865 pattern = 1) : d556 pattern ≤ (1 : Int) + d828 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d556, d828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12298 pattern childGuard
    simpa only [d556, d828, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d556, d828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12320 pattern childGuard
    simpa only [d556, d828, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12384 (pattern : Twelve) (guard : d1865 pattern = 1) : d579 pattern ≤ (1 : Int) + d842 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d579, d842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12367 pattern childGuard
    simpa only [d579, d842, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d579, d842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12383 pattern childGuard
    simpa only [d579, d842, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12385 (pattern : Twelve) (guard : d1865 pattern = 1) : d580 pattern ≤ (1 : Int) + d843 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d580, d843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12298 pattern childGuard
    simpa only [d580, d843, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d580, d843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12274 pattern childGuard
    simpa only [d580, d843, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12386 (pattern : Twelve) (guard : d1865 pattern = 1) : d599 pattern ≤ (1 : Int) + d855 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d599, d855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12384 pattern childGuard
    simpa only [d599, d855, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d599, d855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12385 pattern childGuard
    simpa only [d599, d855, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12387 (pattern : Twelve) (guard : d1865 pattern = 1) : d521 pattern ≤ (1 : Int) + d38 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d521, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12294 pattern childGuard
    simpa only [d521, d38, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d521, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12328 pattern childGuard
    simpa only [d521, d38, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12388 (pattern : Twelve) (guard : d1865 pattern = 1) : d549 pattern ≤ (1 : Int) + d59 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d549, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12387 pattern childGuard
    simpa only [d549, d59, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d549, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12330 pattern childGuard
    simpa only [d549, d59, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12389 (pattern : Twelve) (guard : d1865 pattern = 1) : d549 pattern ≤ (1 : Int) + d844 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12388 pattern childGuard
    simpa only [d844, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12337 pattern childGuard
    simpa only [d844, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12390 (pattern : Twelve) (guard : d1865 pattern = 1) : d600 pattern ≤ (1 : Int) + d856 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d600, d856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12389 pattern childGuard
    simpa only [d600, d856, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d600, d856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12348 pattern childGuard
    simpa only [d600, d856, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12391 (pattern : Twelve) (guard : d1865 pattern = 1) : d612 pattern ≤ (1 : Int) + d862 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d612, d862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12386 pattern childGuard
    simpa only [d612, d862, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d612, d862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12390 pattern childGuard
    simpa only [d612, d862, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12392 (pattern : Twelve) (guard : d1865 pattern = 1) : d613 pattern ≤ (1 : Int) + d863 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d613, d863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12380 pattern childGuard
    simpa only [d613, d863, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d613, d863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12242 pattern childGuard
    simpa only [d613, d863, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12393 (pattern : Twelve) (guard : d1865 pattern = 1) : d621 pattern ≤ (1 : Int) + d867 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d621, d867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12391 pattern childGuard
    simpa only [d621, d867, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d621, d867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12392 pattern childGuard
    simpa only [d621, d867, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12394 (pattern : Twelve) (guard : d1865 pattern = 1) : d625 pattern ≤ (1 : Int) + d869 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d625, d869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12382 pattern childGuard
    simpa only [d625, d869, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d625, d869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12393 pattern childGuard
    simpa only [d625, d869, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12395 (pattern : Twelve) (guard : d1865 pattern = 1) : d627 pattern ≤ (1 : Int) + d869 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12359 pattern childGuard
    simpa only [d627, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12394 pattern childGuard
    simpa only [d627, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12396 (pattern : Twelve) (guard : d1865 pattern = 1) : d628 pattern ≤ (1 : Int) + d869 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12395 pattern childGuard
    simpa only [d628, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12394 pattern childGuard
    simpa only [d628, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12397 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (1 : Int) + d8 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c12398 (pattern : Twelve) (guard : d1865 pattern = 1) : d479 pattern ≤ (1 : Int) + d872 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d479, d872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11212 pattern childGuard
    simpa only [d1865, d479, d872, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d479, d872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12397 pattern childGuard
    simpa only [d1865, d479, d872, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12399 (pattern : Twelve) (guard : d1865 pattern = 1) : d513 pattern ≤ (1 : Int) + d874 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d513, d874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12233 pattern childGuard
    simpa only [d513, d874, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d513, d874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12398 pattern childGuard
    simpa only [d513, d874, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12400 (pattern : Twelve) (guard : d1865 pattern = 1) : d513 pattern ≤ (1 : Int) + d875 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d513, d875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12262 pattern childGuard
    simpa only [d513, d875, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d513, d875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12398 pattern childGuard
    simpa only [d513, d875, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12401 (pattern : Twelve) (guard : d1865 pattern = 1) : d513 pattern ≤ (1 : Int) + d882 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12399 pattern childGuard
    simpa only [d882, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12400 pattern childGuard
    simpa only [d882, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12402 (pattern : Twelve) (guard : d1865 pattern = 1) : d574 pattern ≤ (1 : Int) + d890 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d574, d890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12281 pattern childGuard
    simpa only [d574, d890, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d574, d890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12401 pattern childGuard
    simpa only [d574, d890, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12403 (pattern : Twelve) (guard : d1865 pattern = 1) : d526 pattern ≤ (1 : Int) + d876 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d526, d876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12271 pattern childGuard
    simpa only [d526, d876, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d526, d876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12345 pattern childGuard
    simpa only [d526, d876, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12404 (pattern : Twelve) (guard : d1865 pattern = 1) : d557 pattern ≤ (1 : Int) + d883 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d557, d883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12403 pattern childGuard
    simpa only [d557, d883, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d557, d883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12243 pattern childGuard
    simpa only [d557, d883, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12405 (pattern : Twelve) (guard : d1865 pattern = 1) : d581 pattern ≤ (1 : Int) + d891 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d581, d891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12233 pattern childGuard
    simpa only [d581, d891, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d581, d891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12404 pattern childGuard
    simpa only [d581, d891, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12406 (pattern : Twelve) (guard : d1865 pattern = 1) : d601 pattern ≤ (1 : Int) + d898 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d601, d898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12402 pattern childGuard
    simpa only [d601, d898, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d601, d898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12405 pattern childGuard
    simpa only [d601, d898, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12407 (pattern : Twelve) (guard : d1865 pattern = 1) : d509 pattern ≤ (1 : Int) + d877 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d509, d877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12233 pattern childGuard
    simpa only [d509, d877, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d509, d877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12335 pattern childGuard
    simpa only [d509, d877, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12408 (pattern : Twelve) (guard : d1865 pattern = 1) : d544 pattern ≤ (1 : Int) + d884 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d544, d884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12407 pattern childGuard
    simpa only [d544, d884, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d544, d884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12299 pattern childGuard
    simpa only [d544, d884, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12409 (pattern : Twelve) (guard : d1865 pattern = 1) : d582 pattern ≤ (1 : Int) + d892 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d582, d892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12369 pattern childGuard
    simpa only [d582, d892, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d582, d892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12408 pattern childGuard
    simpa only [d582, d892, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12410 (pattern : Twelve) (guard : d1865 pattern = 1) : d583 pattern ≤ (1 : Int) + d893 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d583, d893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12303 pattern childGuard
    simpa only [d583, d893, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d583, d893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12404 pattern childGuard
    simpa only [d583, d893, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12411 (pattern : Twelve) (guard : d1865 pattern = 1) : d602 pattern ≤ (1 : Int) + d899 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d602, d899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12409 pattern childGuard
    simpa only [d602, d899, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d602, d899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12410 pattern childGuard
    simpa only [d602, d899, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12412 (pattern : Twelve) (guard : d1865 pattern = 1) : d614 pattern ≤ (1 : Int) + d902 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d614, d902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12406 pattern childGuard
    simpa only [d614, d902, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d614, d902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12411 pattern childGuard
    simpa only [d614, d902, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12413 (pattern : Twelve) (guard : d1865 pattern = 1) : d544 pattern ≤ (1 : Int) + d892 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12378 pattern childGuard
    simpa only [d892, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12408 pattern childGuard
    simpa only [d892, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12414 (pattern : Twelve) (guard : d1865 pattern = 1) : d603 pattern ≤ (1 : Int) + d899 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d603, d899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12413 pattern childGuard
    simpa only [d603, d899, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d603, d899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12410 pattern childGuard
    simpa only [d603, d899, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12415 (pattern : Twelve) (guard : d1865 pattern = 1) : d615 pattern ≤ (1 : Int) + d902 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d615, d902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12406 pattern childGuard
    simpa only [d615, d902, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d615, d902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12414 pattern childGuard
    simpa only [d615, d902, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12416 (pattern : Twelve) (guard : d1865 pattern = 1) : d622 pattern ≤ (1 : Int) + d902 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12412 pattern childGuard
    simpa only [d622, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12415 pattern childGuard
    simpa only [d622, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12417 (pattern : Twelve) (guard : d1865 pattern = 1) : d527 pattern ≤ (1 : Int) + d878 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d527, d878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12262 pattern childGuard
    simpa only [d527, d878, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d527, d878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12333 pattern childGuard
    simpa only [d527, d878, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12418 (pattern : Twelve) (guard : d1865 pattern = 1) : d558 pattern ≤ (1 : Int) + d885 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d558, d885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12407 pattern childGuard
    simpa only [d558, d885, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d558, d885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12417 pattern childGuard
    simpa only [d558, d885, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12419 (pattern : Twelve) (guard : d1865 pattern = 1) : d584 pattern ≤ (1 : Int) + d894 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d584, d894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12367 pattern childGuard
    simpa only [d584, d894, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d584, d894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12418 pattern childGuard
    simpa only [d584, d894, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12420 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (1 : Int) + d117 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c12421 (pattern : Twelve) (guard : d1865 pattern = 1) : d492 pattern ≤ (1 : Int) + d119 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d492, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11190 pattern childGuard
    simpa only [d1865, d492, d119, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d492, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12420 pattern childGuard
    simpa only [d1865, d492, d119, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12422 (pattern : Twelve) (guard : d1865 pattern = 1) : d518 pattern ≤ (1 : Int) + d879 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d518, d879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12233 pattern childGuard
    simpa only [d518, d879, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d518, d879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12421 pattern childGuard
    simpa only [d518, d879, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12423 (pattern : Twelve) (guard : d1865 pattern = 1) : d556 pattern ≤ (1 : Int) + d886 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d556, d886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12298 pattern childGuard
    simpa only [d556, d886, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d556, d886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12422 pattern childGuard
    simpa only [d556, d886, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12424 (pattern : Twelve) (guard : d1865 pattern = 1) : d585 pattern ≤ (1 : Int) + d895 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d585, d895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12423 pattern childGuard
    simpa only [d585, d895, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d585, d895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12404 pattern childGuard
    simpa only [d585, d895, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12425 (pattern : Twelve) (guard : d1865 pattern = 1) : d604 pattern ≤ (1 : Int) + d900 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d604, d900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12419 pattern childGuard
    simpa only [d604, d900, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d604, d900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12424 pattern childGuard
    simpa only [d604, d900, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12426 (pattern : Twelve) (guard : d1 pattern = 1) : d5 pattern ≤ (1 : Int) + d14 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11385 pattern childGuard
    simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11234 pattern childGuard
    simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12427 (pattern : Twelve) (guard : d1865 pattern = 1) : d497 pattern ≤ (1 : Int) + d22 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d497, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12426 pattern childGuard
    simpa only [d1865, d497, d22, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d497, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11237 pattern childGuard
    simpa only [d1865, d497, d22, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12428 (pattern : Twelve) (guard : d1865 pattern = 1) : d528 pattern ≤ (1 : Int) + d127 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d528, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12260 pattern childGuard
    simpa only [d528, d127, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d528, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12427 pattern childGuard
    simpa only [d528, d127, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12429 (pattern : Twelve) (guard : d1865 pattern = 1) : d492 pattern ≤ (1 : Int) + d873 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d492, d873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11268 pattern childGuard
    simpa only [d1865, d492, d873, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d492, d873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12332 pattern childGuard
    simpa only [d1865, d492, d873, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12430 (pattern : Twelve) (guard : d1865 pattern = 1) : d529 pattern ≤ (1 : Int) + d880 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d529, d880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12429 pattern childGuard
    simpa only [d529, d880, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d529, d880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12242 pattern childGuard
    simpa only [d529, d880, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12431 (pattern : Twelve) (guard : d1865 pattern = 1) : d559 pattern ≤ (1 : Int) + d887 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d559, d887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12428 pattern childGuard
    simpa only [d559, d887, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d559, d887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12430 pattern childGuard
    simpa only [d559, d887, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12432 (pattern : Twelve) (guard : d1865 pattern = 1) : d586 pattern ≤ (1 : Int) + d896 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d586, d896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12388 pattern childGuard
    simpa only [d586, d896, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d586, d896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12431 pattern childGuard
    simpa only [d586, d896, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12433 (pattern : Twelve) (guard : d1865 pattern = 1) : d497 pattern ≤ (1 : Int) + d118 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d497, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11385 pattern childGuard
    simpa only [d1865, d497, d118, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d497, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12342 pattern childGuard
    simpa only [d1865, d497, d118, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12434 (pattern : Twelve) (guard : d1865 pattern = 1) : d528 pattern ≤ (1 : Int) + d881 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d528, d881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12260 pattern childGuard
    simpa only [d528, d881, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d528, d881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12433 pattern childGuard
    simpa only [d528, d881, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12435 (pattern : Twelve) (guard : d1865 pattern = 1) : d529 pattern ≤ (1 : Int) + d125 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d529, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12421 pattern childGuard
    simpa only [d529, d125, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d529, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12242 pattern childGuard
    simpa only [d529, d125, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12436 (pattern : Twelve) (guard : d1865 pattern = 1) : d559 pattern ≤ (1 : Int) + d888 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d559, d888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12434 pattern childGuard
    simpa only [d559, d888, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d559, d888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12435 pattern childGuard
    simpa only [d559, d888, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12437 (pattern : Twelve) (guard : d1865 pattern = 1) : d530 pattern ≤ (1 : Int) + d42 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d530, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12272 pattern childGuard
    simpa only [d530, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d530, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12267 pattern childGuard
    simpa only [d530, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12438 (pattern : Twelve) (guard : d1865 pattern = 1) : d531 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12254 pattern childGuard
    simpa only [d531, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12242 pattern childGuard
    simpa only [d531, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12439 (pattern : Twelve) (guard : d1865 pattern = 1) : d560 pattern ≤ (1 : Int) + d889 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d560, d889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12437 pattern childGuard
    simpa only [d560, d889, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d560, d889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12438 pattern childGuard
    simpa only [d560, d889, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12440 (pattern : Twelve) (guard : d1865 pattern = 1) : d587 pattern ≤ (1 : Int) + d897 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d587, d897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12436 pattern childGuard
    simpa only [d587, d897, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d587, d897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12439 pattern childGuard
    simpa only [d587, d897, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12441 (pattern : Twelve) (guard : d1865 pattern = 1) : d605 pattern ≤ (1 : Int) + d901 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d605, d901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12432 pattern childGuard
    simpa only [d605, d901, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d605, d901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12440 pattern childGuard
    simpa only [d605, d901, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12442 (pattern : Twelve) (guard : d1865 pattern = 1) : d616 pattern ≤ (1 : Int) + d903 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d616, d903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12425 pattern childGuard
    simpa only [d616, d903, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d616, d903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12441 pattern childGuard
    simpa only [d616, d903, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12443 (pattern : Twelve) (guard : d1865 pattern = 1) : d617 pattern ≤ (1 : Int) + d904 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d617, d904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12414 pattern childGuard
    simpa only [d617, d904, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d617, d904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12242 pattern childGuard
    simpa only [d617, d904, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12444 (pattern : Twelve) (guard : d1865 pattern = 1) : d623 pattern ≤ (1 : Int) + d905 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d623, d905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12442 pattern childGuard
    simpa only [d623, d905, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d623, d905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12443 pattern childGuard
    simpa only [d623, d905, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12445 (pattern : Twelve) (guard : d1865 pattern = 1) : d626 pattern ≤ (1 : Int) + d906 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d626, d906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12416 pattern childGuard
    simpa only [d626, d906, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d626, d906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12444 pattern childGuard
    simpa only [d626, d906, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12446 (pattern : Twelve) (guard : d1865 pattern = 1) : d629 pattern ≤ (1 : Int) + d907 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d629, d907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12396 pattern childGuard
    simpa only [d629, d907, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d629, d907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12445 pattern childGuard
    simpa only [d629, d907, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12447 (pattern : Twelve) (guard : d0 pattern = 1) : d158 pattern ≤ (1 : Int) + d8 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c12448 (pattern : Twelve) (guard : d1865 pattern = 1) : d162 pattern ≤ (1 : Int) + d1275 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d162, d1275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11061 pattern childGuard
    simpa only [d1865, d162, d1275, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d162, d1275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12447 pattern childGuard
    simpa only [d1865, d162, d1275, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12449 (pattern : Twelve) (guard : d1865 pattern = 1) : d500 pattern ≤ (1 : Int) + d1278 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d500, d1278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12448 pattern childGuard
    simpa only [d500, d1278, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d500, d1278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12398 pattern childGuard
    simpa only [d500, d1278, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12450 (pattern : Twelve) (guard : d1865 pattern = 1) : d1105 pattern ≤ (1 : Int) + d872 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d1105, d872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12052 pattern childGuard
    simpa only [d1865, d1105, d872, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d1105, d872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12397 pattern childGuard
    simpa only [d1865, d1105, d872, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12451 (pattern : Twelve) (guard : d1865 pattern = 1) : d1108 pattern ≤ (1 : Int) + d872 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12450 pattern childGuard
    simpa only [d1108, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12398 pattern childGuard
    simpa only [d1108, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12452 (pattern : Twelve) (guard : d1865 pattern = 1) : d1118 pattern ≤ (1 : Int) + d1284 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1118, d1284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12449 pattern childGuard
    simpa only [d1118, d1284, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1118, d1284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12451 pattern childGuard
    simpa only [d1118, d1284, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12453 (pattern : Twelve) (guard : d1865 pattern = 1) : d1132 pattern ≤ (1 : Int) + d1293 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1132, d1293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12235 pattern childGuard
    simpa only [d1132, d1293, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1132, d1293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12452 pattern childGuard
    simpa only [d1132, d1293, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12454 (pattern : Twelve) (guard : d1865 pattern = 1) : d501 pattern ≤ (1 : Int) + d19 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12237 pattern childGuard
    simpa only [d501, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12271 pattern childGuard
    simpa only [d501, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12455 (pattern : Twelve) (guard : d1865 pattern = 1) : d1119 pattern ≤ (1 : Int) + d19 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12454 pattern childGuard
    simpa only [d1119, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12271 pattern childGuard
    simpa only [d1119, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12456 (pattern : Twelve) (guard : d1865 pattern = 1) : d482 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11404 pattern childGuard
    simpa only [d1865, d482, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11237 pattern childGuard
    simpa only [d1865, d482, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12457 (pattern : Twelve) (guard : d1865 pattern = 1) : d495 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11232 pattern childGuard
    simpa only [d1865, d495, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11237 pattern childGuard
    simpa only [d1865, d495, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12458 (pattern : Twelve) (guard : d1865 pattern = 1) : d1109 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12456 pattern childGuard
    simpa only [d1109, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12457 pattern childGuard
    simpa only [d1109, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12459 (pattern : Twelve) (guard : d1865 pattern = 1) : d522 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12457 pattern childGuard
    simpa only [d522, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12242 pattern childGuard
    simpa only [d522, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
