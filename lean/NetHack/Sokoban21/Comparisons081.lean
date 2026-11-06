/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons080
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c11340 (pattern : Twelve) (guard : d1 pattern = 1) : d10 pattern ≤ (1 : Int) + d16 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d10, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11221 pattern childGuard
    simpa only [d10, d16, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d10, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11274 pattern childGuard
    simpa only [d10, d16, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11341 (pattern : Twelve) (guard : d1 pattern = 1) : d11 pattern ≤ (1 : Int) + d12 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11223 pattern childGuard
    simpa only [d11, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11276 pattern childGuard
    simpa only [d11, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11342 (pattern : Twelve) (guard : d1 pattern = 1) : d19 pattern ≤ (1 : Int) + d25 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d19, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11340 pattern childGuard
    simpa only [d19, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d19, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11341 pattern childGuard
    simpa only [d19, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11343 (pattern : Twelve) (guard : d1848 pattern = 1) : d29 pattern ≤ (1 : Int) + d25 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11342 pattern childGuard
    simpa only [d1848, d29, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11068 pattern childGuard
    simpa only [d1848, d29, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11344 (pattern : Twelve) (guard : d1901 pattern = 1) : d29 pattern ≤ (1 : Int) + d25 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11339 pattern childGuard
    simpa only [d1901, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11343 pattern childGuard
    simpa only [d1901, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11345 (pattern : Twelve) (guard : d1901 pattern = 1) : d1449 pattern ≤ (1 : Int) + d1650 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1449, d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11344 pattern childGuard
    simpa only [d1449, d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1449, d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11154 pattern childGuard
    simpa only [d1449, d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11346 (pattern : Twelve) (guard : d1901 pattern = 1) : d1455 pattern ≤ (1 : Int) + d1656 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1455, d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11338 pattern childGuard
    simpa only [d1455, d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1455, d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11345 pattern childGuard
    simpa only [d1455, d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11347 (pattern : Twelve) (guard : d0 pattern = 1) : d1444 pattern ≤ (1 : Int) + d1644 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11348 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (1 : Int) + d20 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11349 (pattern : Twelve) (guard : d1848 pattern = 1) : d1280 pattern ≤ (1 : Int) + d1644 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d1280, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11334 pattern childGuard
    simpa only [d1848, d1280, d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d1280, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11348 pattern childGuard
    simpa only [d1848, d1280, d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11350 (pattern : Twelve) (guard : d1901 pattern = 1) : d1445 pattern ≤ (1 : Int) + d1644 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1901, d1445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11347 pattern childGuard
    simpa only [d1901, d1445, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1901, d1445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11349 pattern childGuard
    simpa only [d1901, d1445, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11351 (pattern : Twelve) (guard : d1901 pattern = 1) : d1450 pattern ≤ (1 : Int) + d1652 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1450, d1652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11248 pattern childGuard
    simpa only [d1450, d1652, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1450, d1652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11350 pattern childGuard
    simpa only [d1450, d1652, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11352 (pattern : Twelve) (guard : d0 pattern = 1) : d29 pattern ≤ (1 : Int) + d821 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11353 (pattern : Twelve) (guard : d1848 pattern = 1) : d29 pattern ≤ (1 : Int) + d821 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d29, d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11342 pattern childGuard
    simpa only [d1848, d29, d821, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d29, d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11144 pattern childGuard
    simpa only [d1848, d29, d821, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11354 (pattern : Twelve) (guard : d1901 pattern = 1) : d29 pattern ≤ (1 : Int) + d821 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11352 pattern childGuard
    simpa only [d1901, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11353 pattern childGuard
    simpa only [d1901, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11355 (pattern : Twelve) (guard : d1901 pattern = 1) : d1449 pattern ≤ (1 : Int) + d1653 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1449, d1653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11354 pattern childGuard
    simpa only [d1449, d1653, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1449, d1653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11154 pattern childGuard
    simpa only [d1449, d1653, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11356 (pattern : Twelve) (guard : d1901 pattern = 1) : d1456 pattern ≤ (1 : Int) + d1658 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1456, d1658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11351 pattern childGuard
    simpa only [d1456, d1658, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1456, d1658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11355 pattern childGuard
    simpa only [d1456, d1658, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11357 (pattern : Twelve) (guard : d1901 pattern = 1) : d1459 pattern ≤ (1 : Int) + d1936 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1459, d1936, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11346 pattern childGuard
    simpa only [d1459, d1936, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1459, d1936, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11356 pattern childGuard
    simpa only [d1459, d1936, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11358 (pattern : Twelve) (guard : d1901 pattern = 1) : d1450 pattern ≤ (1 : Int) + d1649 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1450, d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11256 pattern childGuard
    simpa only [d1450, d1649, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1450, d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11337 pattern childGuard
    simpa only [d1450, d1649, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11359 (pattern : Twelve) (guard : d1901 pattern = 1) : d1456 pattern ≤ (1 : Int) + d1656 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1456, d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11358 pattern childGuard
    simpa only [d1456, d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1456, d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11345 pattern childGuard
    simpa only [d1456, d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11360 (pattern : Twelve) (guard : d1901 pattern = 1) : d1456 pattern ≤ (1 : Int) + d1936 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1936, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11359 pattern childGuard
    simpa only [d1936, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1936, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11356 pattern childGuard
    simpa only [d1936, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11361 (pattern : Twelve) (guard : d1901 pattern = 1) : d1463 pattern ≤ (1 : Int) + d1936 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11357 pattern childGuard
    simpa only [d1463, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11360 pattern childGuard
    simpa only [d1463, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11362 (pattern : Twelve) (guard : d0 pattern = 1) : d1330 pattern ≤ (1 : Int) + d1646 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11363 (pattern : Twelve) (guard : d1 pattern = 1) : d3 pattern ≤ (1 : Int) + d12 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11190 pattern childGuard
    simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11276 pattern childGuard
    simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11364 (pattern : Twelve) (guard : d1 pattern = 1) : d117 pattern ≤ (1 : Int) + d13 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d117, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11267 pattern childGuard
    simpa only [d117, d13, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d117, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11231 pattern childGuard
    simpa only [d117, d13, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11365 (pattern : Twelve) (guard : d1 pattern = 1) : d119 pattern ≤ (1 : Int) + d20 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d119, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11363 pattern childGuard
    simpa only [d119, d20, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d119, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11364 pattern childGuard
    simpa only [d119, d20, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11366 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (1 : Int) + d22 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11367 (pattern : Twelve) (guard : d1848 pattern = 1) : d125 pattern ≤ (1 : Int) + d1646 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d125, d1646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11365 pattern childGuard
    simpa only [d1848, d125, d1646, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d125, d1646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11366 pattern childGuard
    simpa only [d1848, d125, d1646, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11368 (pattern : Twelve) (guard : d1901 pattern = 1) : d1446 pattern ≤ (1 : Int) + d1646 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1901, d1446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11362 pattern childGuard
    simpa only [d1901, d1446, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1901, d1446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11367 pattern childGuard
    simpa only [d1901, d1446, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11369 (pattern : Twelve) (guard : d1901 pattern = 1) : d1451 pattern ≤ (1 : Int) + d1816 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1451, d1816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11280 pattern childGuard
    simpa only [d1451, d1816, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1451, d1816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11368 pattern childGuard
    simpa only [d1451, d1816, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11370 (pattern : Twelve) (guard : d0 pattern = 1) : d42 pattern ≤ (1 : Int) + d822 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11371 (pattern : Twelve) (guard : d1 pattern = 1) : d16 pattern ≤ (1 : Int) + d13 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d16, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11274 pattern childGuard
    simpa only [d16, d13, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d16, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11231 pattern childGuard
    simpa only [d16, d13, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11372 (pattern : Twelve) (guard : d1 pattern = 1) : d12 pattern ≤ (1 : Int) + d14 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d12, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11276 pattern childGuard
    simpa only [d12, d14, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d12, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11234 pattern childGuard
    simpa only [d12, d14, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11373 (pattern : Twelve) (guard : d1 pattern = 1) : d25 pattern ≤ (1 : Int) + d21 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d25, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11371 pattern childGuard
    simpa only [d25, d21, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d25, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11372 pattern childGuard
    simpa only [d25, d21, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11374 (pattern : Twelve) (guard : d1848 pattern = 1) : d42 pattern ≤ (1 : Int) + d822 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d42, d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11373 pattern childGuard
    simpa only [d1848, d42, d822, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d42, d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11237 pattern childGuard
    simpa only [d1848, d42, d822, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11375 (pattern : Twelve) (guard : d1901 pattern = 1) : d42 pattern ≤ (1 : Int) + d822 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11370 pattern childGuard
    simpa only [d1901, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11374 pattern childGuard
    simpa only [d1901, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11376 (pattern : Twelve) (guard : d1901 pattern = 1) : d1452 pattern ≤ (1 : Int) + d1655 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1452, d1655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11375 pattern childGuard
    simpa only [d1452, d1655, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1452, d1655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11154 pattern childGuard
    simpa only [d1452, d1655, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11377 (pattern : Twelve) (guard : d1901 pattern = 1) : d1457 pattern ≤ (1 : Int) + d1819 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1457, d1819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11369 pattern childGuard
    simpa only [d1457, d1819, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1457, d1819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11376 pattern childGuard
    simpa only [d1457, d1819, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11378 (pattern : Twelve) (guard : d1901 pattern = 1) : d1460 pattern ≤ (1 : Int) + d1937 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1460, d1937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11356 pattern childGuard
    simpa only [d1460, d1937, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1460, d1937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11377 pattern childGuard
    simpa only [d1460, d1937, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11379 (pattern : Twelve) (guard : d1901 pattern = 1) : d1461 pattern ≤ (1 : Int) + d1938 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1461, d1938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11356 pattern childGuard
    simpa only [d1461, d1938, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1461, d1938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11154 pattern childGuard
    simpa only [d1461, d1938, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11380 (pattern : Twelve) (guard : d1901 pattern = 1) : d1464 pattern ≤ (1 : Int) + d1939 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1464, d1939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11378 pattern childGuard
    simpa only [d1464, d1939, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1464, d1939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11379 pattern childGuard
    simpa only [d1464, d1939, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11381 (pattern : Twelve) (guard : d1901 pattern = 1) : d1466 pattern ≤ (1 : Int) + d1940 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1466, d1940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11361 pattern childGuard
    simpa only [d1466, d1940, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1466, d1940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11380 pattern childGuard
    simpa only [d1466, d1940, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11382 (pattern : Twelve) (guard : d1901 pattern = 1) : d1467 pattern ≤ (1 : Int) + d1940 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1467, d1940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11360 pattern childGuard
    simpa only [d1467, d1940, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1467, d1940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11380 pattern childGuard
    simpa only [d1467, d1940, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11383 (pattern : Twelve) (guard : d1901 pattern = 1) : d1469 pattern ≤ (1 : Int) + d1940 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11381 pattern childGuard
    simpa only [d1469, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11382 pattern childGuard
    simpa only [d1469, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11384 (pattern : Twelve) (guard : d1901 pattern = 1) : d1470 pattern ≤ (1 : Int) + d1940 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11383 pattern childGuard
    simpa only [d1470, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11382 pattern childGuard
    simpa only [d1470, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11385 (pattern : Twelve) (guard : d1 pattern = 1) : d5 pattern ≤ (1 : Int) + d5 pattern := by
  omega
theorem c11386 (pattern : Twelve) (guard : d1 pattern = 1) : d15 pattern ≤ (1 : Int) + d12 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d15, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11184 pattern childGuard
    simpa only [d15, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d15, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11385 pattern childGuard
    simpa only [d15, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11387 (pattern : Twelve) (guard : d1 pattern = 1) : d14 pattern ≤ (1 : Int) + d13 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d14, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11195 pattern childGuard
    simpa only [d14, d13, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d14, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11282 pattern childGuard
    simpa only [d14, d13, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11388 (pattern : Twelve) (guard : d1 pattern = 1) : d1277 pattern ≤ (1 : Int) + d20 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1277, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11386 pattern childGuard
    simpa only [d1277, d20, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1277, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11387 pattern childGuard
    simpa only [d1277, d20, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11389 (pattern : Twelve) (guard : d1848 pattern = 1) : d1331 pattern ≤ (1 : Int) + d1646 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d1331, d1646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11388 pattern childGuard
    simpa only [d1848, d1331, d1646, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d1331, d1646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11366 pattern childGuard
    simpa only [d1848, d1331, d1646, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11390 (pattern : Twelve) (guard : d1901 pattern = 1) : d1337 pattern ≤ (1 : Int) + d1646 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1901, d1337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11362 pattern childGuard
    simpa only [d1901, d1337, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1901, d1337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11389 pattern childGuard
    simpa only [d1901, d1337, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11391 (pattern : Twelve) (guard : d1901 pattern = 1) : d1453 pattern ≤ (1 : Int) + d1816 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1453, d1816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11280 pattern childGuard
    simpa only [d1453, d1816, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1453, d1816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11390 pattern childGuard
    simpa only [d1453, d1816, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11392 (pattern : Twelve) (guard : d1 pattern = 1) : d12 pattern ≤ (1 : Int) + d13 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d12, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11267 pattern childGuard
    simpa only [d12, d13, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d12, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11234 pattern childGuard
    simpa only [d12, d13, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11393 (pattern : Twelve) (guard : d1 pattern = 1) : d13 pattern ≤ (1 : Int) + d14 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d13, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11316 pattern childGuard
    simpa only [d13, d14, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d13, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11282 pattern childGuard
    simpa only [d13, d14, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11394 (pattern : Twelve) (guard : d1 pattern = 1) : d20 pattern ≤ (1 : Int) + d21 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d20, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11392 pattern childGuard
    simpa only [d20, d21, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d20, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11393 pattern childGuard
    simpa only [d20, d21, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11395 (pattern : Twelve) (guard : d1848 pattern = 1) : d128 pattern ≤ (1 : Int) + d822 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d128, d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11394 pattern childGuard
    simpa only [d1848, d128, d822, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d128, d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11237 pattern childGuard
    simpa only [d1848, d128, d822, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11396 (pattern : Twelve) (guard : d1901 pattern = 1) : d1447 pattern ≤ (1 : Int) + d822 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1901, d1447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11370 pattern childGuard
    simpa only [d1901, d1447, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1901, d1447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11395 pattern childGuard
    simpa only [d1901, d1447, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11397 (pattern : Twelve) (guard : d1901 pattern = 1) : d1454 pattern ≤ (1 : Int) + d1655 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1454, d1655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11396 pattern childGuard
    simpa only [d1454, d1655, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1454, d1655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11154 pattern childGuard
    simpa only [d1454, d1655, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11398 (pattern : Twelve) (guard : d1901 pattern = 1) : d1458 pattern ≤ (1 : Int) + d1819 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1458, d1819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11391 pattern childGuard
    simpa only [d1458, d1819, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1458, d1819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11397 pattern childGuard
    simpa only [d1458, d1819, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11399 (pattern : Twelve) (guard : d1901 pattern = 1) : d1462 pattern ≤ (1 : Int) + d1937 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1462, d1937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11356 pattern childGuard
    simpa only [d1462, d1937, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1462, d1937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11398 pattern childGuard
    simpa only [d1462, d1937, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11400 (pattern : Twelve) (guard : d1901 pattern = 1) : d1465 pattern ≤ (1 : Int) + d1939 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1465, d1939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11399 pattern childGuard
    simpa only [d1465, d1939, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1465, d1939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11379 pattern childGuard
    simpa only [d1465, d1939, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11401 (pattern : Twelve) (guard : d1901 pattern = 1) : d1468 pattern ≤ (1 : Int) + d1940 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1468, d1940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11360 pattern childGuard
    simpa only [d1468, d1940, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1468, d1940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11400 pattern childGuard
    simpa only [d1468, d1940, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11402 (pattern : Twelve) (guard : d1901 pattern = 1) : d1471 pattern ≤ (1 : Int) + d1940 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11384 pattern childGuard
    simpa only [d1471, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11401 pattern childGuard
    simpa only [d1471, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11403 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (1 : Int) + d6 pattern := by
  change (0 : Int) ≤ (1 : Int) + 6
  decide
theorem c11404 (pattern : Twelve) (guard : d1 pattern = 1) : d10 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11403 pattern childGuard
    simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11230 pattern childGuard
    simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11405 (pattern : Twelve) (guard : d1 pattern = 1) : d1 pattern ≤ (1 : Int) + d6 pattern := by
  change (1 : Int) ≤ (1 : Int) + 6
  decide
theorem c11406 (pattern : Twelve) (guard : d1 pattern = 1) : d11 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11405 pattern childGuard
    simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11233 pattern childGuard
    simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11407 (pattern : Twelve) (guard : d1 pattern = 1) : d19 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11404 pattern childGuard
    simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11406 pattern childGuard
    simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11408 (pattern : Twelve) (guard : d1848 pattern = 1) : d29 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11407 pattern childGuard
    simpa only [d1848, d29, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11237 pattern childGuard
    simpa only [d1848, d29, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11409 (pattern : Twelve) (guard : d1901 pattern = 1) : d29 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11229 pattern childGuard
    simpa only [d1901, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11408 pattern childGuard
    simpa only [d1901, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11410 (pattern : Twelve) (guard : d0 pattern = 1) : d1645 pattern ≤ (1 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11411 (pattern : Twelve) (guard : d1 pattern = 1) : d1324 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11406 pattern childGuard
    simpa only [d1324, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11232 pattern childGuard
    simpa only [d1324, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11412 (pattern : Twelve) (guard : d1848 pattern = 1) : d1645 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d1645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11411 pattern childGuard
    simpa only [d1848, d1645, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d1645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11237 pattern childGuard
    simpa only [d1848, d1645, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11413 (pattern : Twelve) (guard : d1901 pattern = 1) : d1645 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11410 pattern childGuard
    simpa only [d1901, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11412 pattern childGuard
    simpa only [d1901, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11414 (pattern : Twelve) (guard : d1901 pattern = 1) : d1716 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11409 pattern childGuard
    simpa only [d1716, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11413 pattern childGuard
    simpa only [d1716, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11415 (pattern : Twelve) (guard : d1901 pattern = 1) : d42 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11281 pattern childGuard
    simpa only [d1901, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11238 pattern childGuard
    simpa only [d1901, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11416 (pattern : Twelve) (guard : d1901 pattern = 1) : d1452 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11415 pattern childGuard
    simpa only [d1452, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11154 pattern childGuard
    simpa only [d1452, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11417 (pattern : Twelve) (guard : d1901 pattern = 1) : d1719 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11414 pattern childGuard
    simpa only [d1719, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11416 pattern childGuard
    simpa only [d1719, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11418 (pattern : Twelve) (guard : d0 pattern = 1) : d128 pattern ≤ (1 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11419 (pattern : Twelve) (guard : d1 pattern = 1) : d20 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11235 pattern childGuard
    simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11283 pattern childGuard
    simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11420 (pattern : Twelve) (guard : d1848 pattern = 1) : d128 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11419 pattern childGuard
    simpa only [d1848, d128, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11237 pattern childGuard
    simpa only [d1848, d128, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11421 (pattern : Twelve) (guard : d1901 pattern = 1) : d128 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11418 pattern childGuard
    simpa only [d1901, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11420 pattern childGuard
    simpa only [d1901, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11422 (pattern : Twelve) (guard : d1901 pattern = 1) : d1717 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11415 pattern childGuard
    simpa only [d1717, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11421 pattern childGuard
    simpa only [d1717, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11423 (pattern : Twelve) (guard : d0 pattern = 1) : d822 pattern ≤ (1 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11424 (pattern : Twelve) (guard : d1901 pattern = 1) : d822 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11423 pattern childGuard
    simpa only [d1901, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11286 pattern childGuard
    simpa only [d1901, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11425 (pattern : Twelve) (guard : d1901 pattern = 1) : d1655 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11424 pattern childGuard
    simpa only [d1655, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11154 pattern childGuard
    simpa only [d1655, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11426 (pattern : Twelve) (guard : d1901 pattern = 1) : d1720 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11422 pattern childGuard
    simpa only [d1720, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11425 pattern childGuard
    simpa only [d1720, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11427 (pattern : Twelve) (guard : d1901 pattern = 1) : d1722 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11417 pattern childGuard
    simpa only [d1722, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11426 pattern childGuard
    simpa only [d1722, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11428 (pattern : Twelve) (guard : d1901 pattern = 1) : d1723 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11417 pattern childGuard
    simpa only [d1723, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11154 pattern childGuard
    simpa only [d1723, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11429 (pattern : Twelve) (guard : d1901 pattern = 1) : d1725 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11427 pattern childGuard
    simpa only [d1725, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11428 pattern childGuard
    simpa only [d1725, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11430 (pattern : Twelve) (guard : d1901 pattern = 1) : d1727 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11417 pattern childGuard
    simpa only [d1727, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11429 pattern childGuard
    simpa only [d1727, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11431 (pattern : Twelve) (guard : d1 pattern = 1) : d22 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11284 pattern childGuard
    simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11282 pattern childGuard
    simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11432 (pattern : Twelve) (guard : d1848 pattern = 1) : d183 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11431 pattern childGuard
    simpa only [d1848, d183, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11237 pattern childGuard
    simpa only [d1848, d183, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11433 (pattern : Twelve) (guard : d1901 pattern = 1) : d1667 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1901, d1667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11418 pattern childGuard
    simpa only [d1901, d1667, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1901, d1667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11432 pattern childGuard
    simpa only [d1901, d1667, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11434 (pattern : Twelve) (guard : d1901 pattern = 1) : d1718 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11415 pattern childGuard
    simpa only [d1718, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11433 pattern childGuard
    simpa only [d1718, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11435 (pattern : Twelve) (guard : d1901 pattern = 1) : d1252 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1901, d1252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11423 pattern childGuard
    simpa only [d1901, d1252, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1901, d1252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11321 pattern childGuard
    simpa only [d1901, d1252, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11436 (pattern : Twelve) (guard : d1901 pattern = 1) : d1626 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11435 pattern childGuard
    simpa only [d1626, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11154 pattern childGuard
    simpa only [d1626, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11437 (pattern : Twelve) (guard : d1901 pattern = 1) : d1721 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11434 pattern childGuard
    simpa only [d1721, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11436 pattern childGuard
    simpa only [d1721, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11438 (pattern : Twelve) (guard : d1901 pattern = 1) : d1724 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11417 pattern childGuard
    simpa only [d1724, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11437 pattern childGuard
    simpa only [d1724, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11439 (pattern : Twelve) (guard : d1901 pattern = 1) : d1726 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11438 pattern childGuard
    simpa only [d1726, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11428 pattern childGuard
    simpa only [d1726, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11440 (pattern : Twelve) (guard : d1901 pattern = 1) : d1728 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11417 pattern childGuard
    simpa only [d1728, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11439 pattern childGuard
    simpa only [d1728, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11441 (pattern : Twelve) (guard : d1901 pattern = 1) : d1729 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11430 pattern childGuard
    simpa only [d1729, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11440 pattern childGuard
    simpa only [d1729, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11442 (pattern : Twelve) (guard : d1901 pattern = 1) : d0 pattern ≤ (0 : Int) + d0 pattern := by
  omega
theorem c11443 (pattern : Twelve) (guard : d0 pattern = 1) : d26 pattern ≤ (0 : Int) + d1 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11444 (pattern : Twelve) (guard : d0 pattern = 1) : d1 pattern ≤ (0 : Int) + d1 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11445 (pattern : Twelve) (guard : d1848 pattern = 1) : d27 pattern ≤ (0 : Int) + d1 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10902 pattern childGuard
    simpa only [d1848, d27, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11444 pattern childGuard
    simpa only [d1848, d27, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11446 (pattern : Twelve) (guard : d1901 pattern = 1) : d50 pattern ≤ (0 : Int) + d1 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1901, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11443 pattern childGuard
    simpa only [d1901, d50, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1901, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11445 pattern childGuard
    simpa only [d1901, d50, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11447 (pattern : Twelve) (guard : d1901 pattern = 1) : d72 pattern ≤ (0 : Int) + d1859 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d72, d1859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11442 pattern childGuard
    simpa only [d72, d1859, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d72, d1859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11446 pattern childGuard
    simpa only [d72, d1859, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11448 (pattern : Twelve) (guard : d0 pattern = 1) : d28 pattern ≤ (0 : Int) + d18 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11449 (pattern : Twelve) (guard : d1 pattern = 1) : d10 pattern ≤ (0 : Int) + d8 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d10, d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10900 pattern childGuard
    simpa only [d10, d8, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d10, d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1333 pattern childGuard
    simpa only [d10, d8, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11450 (pattern : Twelve) (guard : d1 pattern = 1) : d19 pattern ≤ (0 : Int) + d18 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d19, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11449 pattern childGuard
    simpa only [d19, d18, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d19, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10908 pattern childGuard
    simpa only [d19, d18, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11451 (pattern : Twelve) (guard : d1848 pattern = 1) : d29 pattern ≤ (0 : Int) + d18 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11450 pattern childGuard
    simpa only [d1848, d29, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5062 pattern childGuard
    simpa only [d1848, d29, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11452 (pattern : Twelve) (guard : d1901 pattern = 1) : d51 pattern ≤ (0 : Int) + d18 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1901, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11448 pattern childGuard
    simpa only [d1901, d51, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1901, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11451 pattern childGuard
    simpa only [d1901, d51, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11453 (pattern : Twelve) (guard : d1901 pattern = 1) : d73 pattern ≤ (0 : Int) + d1941 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d73, d1941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11442 pattern childGuard
    simpa only [d73, d1941, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d73, d1941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11452 pattern childGuard
    simpa only [d73, d1941, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11454 (pattern : Twelve) (guard : d1901 pattern = 1) : d91 pattern ≤ (0 : Int) + d1942 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d91, d1942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11447 pattern childGuard
    simpa only [d91, d1942, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d91, d1942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11453 pattern childGuard
    simpa only [d91, d1942, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11455 (pattern : Twelve) (guard : d0 pattern = 1) : d30 pattern ≤ (0 : Int) + d2 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11456 (pattern : Twelve) (guard : d0 pattern = 1) : d20 pattern ≤ (0 : Int) + d2 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11457 (pattern : Twelve) (guard : d1848 pattern = 1) : d31 pattern ≤ (0 : Int) + d2 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10863 pattern childGuard
    simpa only [d1848, d31, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11456 pattern childGuard
    simpa only [d1848, d31, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11458 (pattern : Twelve) (guard : d1901 pattern = 1) : d52 pattern ≤ (0 : Int) + d2 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1901, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11455 pattern childGuard
    simpa only [d1901, d52, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1901, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11457 pattern childGuard
    simpa only [d1901, d52, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11459 (pattern : Twelve) (guard : d0 pattern = 1) : d21 pattern ≤ (0 : Int) + d2 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11460 (pattern : Twelve) (guard : d1848 pattern = 1) : d32 pattern ≤ (0 : Int) + d2 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10968 pattern childGuard
    simpa only [d1848, d32, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11459 pattern childGuard
    simpa only [d1848, d32, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11461 (pattern : Twelve) (guard : d1901 pattern = 1) : d53 pattern ≤ (0 : Int) + d2 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1901, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11455 pattern childGuard
    simpa only [d1901, d53, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1901, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11460 pattern childGuard
    simpa only [d1901, d53, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11462 (pattern : Twelve) (guard : d1901 pattern = 1) : d74 pattern ≤ (0 : Int) + d2 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11458 pattern childGuard
    simpa only [d74, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11461 pattern childGuard
    simpa only [d74, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11463 (pattern : Twelve) (guard : d1848 pattern = 1) : d33 pattern ≤ (0 : Int) + d2 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10863 pattern childGuard
    simpa only [d1848, d33, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5002 pattern childGuard
    simpa only [d1848, d33, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11464 (pattern : Twelve) (guard : d1901 pattern = 1) : d54 pattern ≤ (0 : Int) + d2 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1901, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11455 pattern childGuard
    simpa only [d1901, d54, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1901, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11463 pattern childGuard
    simpa only [d1901, d54, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11465 (pattern : Twelve) (guard : d0 pattern = 1) : d34 pattern ≤ (0 : Int) + d23 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11466 (pattern : Twelve) (guard : d1848 pattern = 1) : d29 pattern ≤ (0 : Int) + d23 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10909 pattern childGuard
    simpa only [d1848, d29, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4984 pattern childGuard
    simpa only [d1848, d29, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11467 (pattern : Twelve) (guard : d1901 pattern = 1) : d55 pattern ≤ (0 : Int) + d23 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1901, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11465 pattern childGuard
    simpa only [d1901, d55, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1901, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11466 pattern childGuard
    simpa only [d1901, d55, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11468 (pattern : Twelve) (guard : d1901 pattern = 1) : d75 pattern ≤ (0 : Int) + d1943 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d75, d1943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11464 pattern childGuard
    simpa only [d75, d1943, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d75, d1943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11467 pattern childGuard
    simpa only [d75, d1943, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11469 (pattern : Twelve) (guard : d1901 pattern = 1) : d92 pattern ≤ (0 : Int) + d1944 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d92, d1944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11462 pattern childGuard
    simpa only [d92, d1944, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d92, d1944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11468 pattern childGuard
    simpa only [d92, d1944, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11470 (pattern : Twelve) (guard : d1901 pattern = 1) : d102 pattern ≤ (0 : Int) + d1945 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d102, d1945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11454 pattern childGuard
    simpa only [d102, d1945, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d102, d1945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11469 pattern childGuard
    simpa only [d102, d1945, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11471 (pattern : Twelve) (guard : d1901 pattern = 1) : d76 pattern ≤ (0 : Int) + d1946 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d76, d1946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11442 pattern childGuard
    simpa only [d76, d1946, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d76, d1946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11467 pattern childGuard
    simpa only [d76, d1946, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11472 (pattern : Twelve) (guard : d1901 pattern = 1) : d93 pattern ≤ (0 : Int) + d1947 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d93, d1947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11447 pattern childGuard
    simpa only [d93, d1947, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d93, d1947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11471 pattern childGuard
    simpa only [d93, d1947, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11473 (pattern : Twelve) (guard : d1848 pattern = 1) : d35 pattern ≤ (0 : Int) + d2 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10863 pattern childGuard
    simpa only [d1848, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5005 pattern childGuard
    simpa only [d1848, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11474 (pattern : Twelve) (guard : d1901 pattern = 1) : d56 pattern ≤ (0 : Int) + d2 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1901, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11455 pattern childGuard
    simpa only [d1901, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1901, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11473 pattern childGuard
    simpa only [d1901, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11475 (pattern : Twelve) (guard : d1848 pattern = 1) : d36 pattern ≤ (0 : Int) + d2 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10968 pattern childGuard
    simpa only [d1848, d36, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5005 pattern childGuard
    simpa only [d1848, d36, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11476 (pattern : Twelve) (guard : d1901 pattern = 1) : d57 pattern ≤ (0 : Int) + d2 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1901, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11455 pattern childGuard
    simpa only [d1901, d57, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1901, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11475 pattern childGuard
    simpa only [d1901, d57, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11477 (pattern : Twelve) (guard : d1901 pattern = 1) : d77 pattern ≤ (0 : Int) + d2 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11474 pattern childGuard
    simpa only [d77, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11476 pattern childGuard
    simpa only [d77, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11478 (pattern : Twelve) (guard : d1901 pattern = 1) : d78 pattern ≤ (0 : Int) + d1943 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d78, d1943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11474 pattern childGuard
    simpa only [d78, d1943, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d78, d1943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11467 pattern childGuard
    simpa only [d78, d1943, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11479 (pattern : Twelve) (guard : d1901 pattern = 1) : d94 pattern ≤ (0 : Int) + d1944 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d94, d1944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11477 pattern childGuard
    simpa only [d94, d1944, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d94, d1944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11478 pattern childGuard
    simpa only [d94, d1944, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
