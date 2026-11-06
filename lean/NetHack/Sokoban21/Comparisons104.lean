/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons103
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c14560 (pattern : Twelve) (guard : d2356 pattern = 1) : d363 pattern ≤ (2 : Int) + d2372 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d2356 pattern = 1 := by simpa only [d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14556 pattern childGuard
    simpa only [d363, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2356 pattern = 1 := by simpa only [d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14559 pattern childGuard
    simpa only [d363, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14561 (pattern : Twelve) (guard : d2356 pattern = 1) : d365 pattern ≤ (2 : Int) + d2373 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d2356 pattern = 1 := by simpa only [d365, d2373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14552 pattern childGuard
    simpa only [d365, d2373, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2356 pattern = 1 := by simpa only [d365, d2373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14560 pattern childGuard
    simpa only [d365, d2373, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14562 (pattern : Twelve) (guard : d0 pattern = 1) : d0 pattern ≤ (2 : Int) + d814 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14563 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (2 : Int) + d814 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14502 pattern childGuard
    simpa only [d814, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13901 pattern childGuard
    simpa only [d814, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14564 (pattern : Twelve) (guard : d26 pattern = 1) : d0 pattern ≤ (2 : Int) + d814 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14562 pattern childGuard
    simpa only [d26, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14563 pattern childGuard
    simpa only [d26, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14565 (pattern : Twelve) (guard : d26 pattern = 1) : d0 pattern ≤ (2 : Int) + d2374 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14504 pattern childGuard
    simpa only [d2374, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d26 pattern = 1 := by simpa only [d2374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14564 pattern childGuard
    simpa only [d2374, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14566 (pattern : Twelve) (guard : d0 pattern = 1) : d824 pattern ≤ (2 : Int) + d2374 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14567 (pattern : Twelve) (guard : d2355 pattern = 1) : d838 pattern ≤ (2 : Int) + d2374 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2355, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14565 pattern childGuard
    simpa only [d2355, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2355, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14566 pattern childGuard
    simpa only [d2355, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14568 (pattern : Twelve) (guard : d1 pattern = 1) : d7 pattern ≤ (2 : Int) + d11 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13901 pattern childGuard
    simpa only [d7, d11, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13915 pattern childGuard
    simpa only [d7, d11, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14569 (pattern : Twelve) (guard : d1 pattern = 1) : d17 pattern ≤ (2 : Int) + d19 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14509 pattern childGuard
    simpa only [d17, d19, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14568 pattern childGuard
    simpa only [d17, d19, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14570 (pattern : Twelve) (guard : d26 pattern = 1) : d17 pattern ≤ (2 : Int) + d19 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14174 pattern childGuard
    simpa only [d26, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14569 pattern childGuard
    simpa only [d26, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14571 (pattern : Twelve) (guard : d0 pattern = 1) : d17 pattern ≤ (2 : Int) + d25 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14572 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (2 : Int) + d4 pattern := by
  change (0 : Int) ≤ (2 : Int) + 4
  decide
theorem c14573 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (2 : Int) + d16 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13913 pattern childGuard
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14572 pattern childGuard
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14574 (pattern : Twelve) (guard : d1 pattern = 1) : d1 pattern ≤ (2 : Int) + d5 pattern := by
  change (1 : Int) ≤ (2 : Int) + 5
  decide
theorem c14575 (pattern : Twelve) (guard : d1 pattern = 1) : d7 pattern ≤ (2 : Int) + d12 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14510 pattern childGuard
    simpa only [d7, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14574 pattern childGuard
    simpa only [d7, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14576 (pattern : Twelve) (guard : d1 pattern = 1) : d17 pattern ≤ (2 : Int) + d25 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14573 pattern childGuard
    simpa only [d17, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14575 pattern childGuard
    simpa only [d17, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14577 (pattern : Twelve) (guard : d26 pattern = 1) : d17 pattern ≤ (2 : Int) + d25 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14571 pattern childGuard
    simpa only [d26, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14576 pattern childGuard
    simpa only [d26, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14578 (pattern : Twelve) (guard : d26 pattern = 1) : d17 pattern ≤ (2 : Int) + d2375 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14570 pattern childGuard
    simpa only [d2375, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d26 pattern = 1 := by simpa only [d2375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14577 pattern childGuard
    simpa only [d2375, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14579 (pattern : Twelve) (guard : d0 pattern = 1) : d825 pattern ≤ (2 : Int) + d2375 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14580 (pattern : Twelve) (guard : d2355 pattern = 1) : d839 pattern ≤ (2 : Int) + d2375 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2355, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14578 pattern childGuard
    simpa only [d2355, d839, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2355, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14579 pattern childGuard
    simpa only [d2355, d839, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14581 (pattern : Twelve) (guard : d2355 pattern = 1) : d853 pattern ≤ (2 : Int) + d2376 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2355 pattern = 1 := by simpa only [d853, d2376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14567 pattern childGuard
    simpa only [d853, d2376, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2355 pattern = 1 := by simpa only [d853, d2376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14580 pattern childGuard
    simpa only [d853, d2376, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14582 (pattern : Twelve) (guard : d0 pattern = 1) : d913 pattern ≤ (2 : Int) + d2376 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14583 (pattern : Twelve) (guard : d2356 pattern = 1) : d1018 pattern ≤ (2 : Int) + d2376 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2355 pattern = 1 := by simpa only [d2356, d1018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14581 pattern childGuard
    simpa only [d2356, d1018, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2356, d1018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14582 pattern childGuard
    simpa only [d2356, d1018, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14584 (pattern : Twelve) (guard : d0 pattern = 1) : d914 pattern ≤ (2 : Int) + d2376 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14585 (pattern : Twelve) (guard : d2356 pattern = 1) : d1019 pattern ≤ (2 : Int) + d2376 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2355 pattern = 1 := by simpa only [d2356, d1019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14581 pattern childGuard
    simpa only [d2356, d1019, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2356, d1019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14584 pattern childGuard
    simpa only [d2356, d1019, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14586 (pattern : Twelve) (guard : d2356 pattern = 1) : d1023 pattern ≤ (2 : Int) + d2376 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d2356 pattern = 1 := by simpa only [d1023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14583 pattern childGuard
    simpa only [d1023, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2356 pattern = 1 := by simpa only [d1023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14585 pattern childGuard
    simpa only [d1023, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14587 (pattern : Twelve) (guard : d0 pattern = 1) : d916 pattern ≤ (2 : Int) + d2379 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14588 (pattern : Twelve) (guard : d2356 pattern = 1) : d1020 pattern ≤ (2 : Int) + d2380 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2355 pattern = 1 := by simpa only [d2356, d1020, d2380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14581 pattern childGuard
    simpa only [d2356, d1020, d2380, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2356, d1020, d2380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14587 pattern childGuard
    simpa only [d2356, d1020, d2380, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14589 (pattern : Twelve) (guard : d2356 pattern = 1) : d1021 pattern ≤ (2 : Int) + d2381 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2355 pattern = 1 := by simpa only [d2356, d1021, d2381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14581 pattern childGuard
    simpa only [d2356, d1021, d2381, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2356, d1021, d2381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13925 pattern childGuard
    simpa only [d2356, d1021, d2381, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14590 (pattern : Twelve) (guard : d2356 pattern = 1) : d1024 pattern ≤ (2 : Int) + d2382 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d2356 pattern = 1 := by simpa only [d1024, d2382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14588 pattern childGuard
    simpa only [d1024, d2382, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2356 pattern = 1 := by simpa only [d1024, d2382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14589 pattern childGuard
    simpa only [d1024, d2382, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14591 (pattern : Twelve) (guard : d2356 pattern = 1) : d1025 pattern ≤ (2 : Int) + d2383 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d2356 pattern = 1 := by simpa only [d1025, d2383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14586 pattern childGuard
    simpa only [d1025, d2383, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2356 pattern = 1 := by simpa only [d1025, d2383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14590 pattern childGuard
    simpa only [d1025, d2383, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14592 (pattern : Twelve) (guard : d26 pattern = 1) : d823 pattern ≤ (2 : Int) + d19 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d26, d823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14174 pattern childGuard
    simpa only [d26, d823, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d26, d823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14532 pattern childGuard
    simpa only [d26, d823, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14593 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (2 : Int) + d16 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13329 pattern childGuard
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13482 pattern childGuard
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14594 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (2 : Int) + d25 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14593 pattern childGuard
    simpa only [d25, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13481 pattern childGuard
    simpa only [d25, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14595 (pattern : Twelve) (guard : d26 pattern = 1) : d823 pattern ≤ (2 : Int) + d25 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d26, d823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14571 pattern childGuard
    simpa only [d26, d823, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d26, d823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14594 pattern childGuard
    simpa only [d26, d823, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14596 (pattern : Twelve) (guard : d26 pattern = 1) : d823 pattern ≤ (2 : Int) + d2375 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14592 pattern childGuard
    simpa only [d2375, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d26 pattern = 1 := by simpa only [d2375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14595 pattern childGuard
    simpa only [d2375, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14597 (pattern : Twelve) (guard : d2355 pattern = 1) : d846 pattern ≤ (2 : Int) + d2375 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2355, d846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14596 pattern childGuard
    simpa only [d2355, d846, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2355, d846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14579 pattern childGuard
    simpa only [d2355, d846, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14598 (pattern : Twelve) (guard : d2355 pattern = 1) : d857 pattern ≤ (2 : Int) + d2376 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2355 pattern = 1 := by simpa only [d857, d2376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14567 pattern childGuard
    simpa only [d857, d2376, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2355 pattern = 1 := by simpa only [d857, d2376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14597 pattern childGuard
    simpa only [d857, d2376, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14599 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (2 : Int) + d2376 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14600 (pattern : Twelve) (guard : d2356 pattern = 1) : d1022 pattern ≤ (2 : Int) + d2376 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2355 pattern = 1 := by simpa only [d2356, d1022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14598 pattern childGuard
    simpa only [d2356, d1022, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2356, d1022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14599 pattern childGuard
    simpa only [d2356, d1022, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14601 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (2 : Int) + d2379 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14602 (pattern : Twelve) (guard : d2356 pattern = 1) : d1022 pattern ≤ (2 : Int) + d2380 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2355 pattern = 1 := by simpa only [d2356, d1022, d2380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14598 pattern childGuard
    simpa only [d2356, d1022, d2380, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2356, d1022, d2380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14601 pattern childGuard
    simpa only [d2356, d1022, d2380, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14603 (pattern : Twelve) (guard : d2356 pattern = 1) : d1022 pattern ≤ (2 : Int) + d2381 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2355 pattern = 1 := by simpa only [d2356, d1022, d2381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14598 pattern childGuard
    simpa only [d2356, d1022, d2381, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2356, d1022, d2381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13925 pattern childGuard
    simpa only [d2356, d1022, d2381, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14604 (pattern : Twelve) (guard : d2356 pattern = 1) : d1022 pattern ≤ (2 : Int) + d2382 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d2356 pattern = 1 := by simpa only [d2382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14602 pattern childGuard
    simpa only [d2382, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2356 pattern = 1 := by simpa only [d2382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14603 pattern childGuard
    simpa only [d2382, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14605 (pattern : Twelve) (guard : d2356 pattern = 1) : d1022 pattern ≤ (2 : Int) + d2383 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d2356 pattern = 1 := by simpa only [d2383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14600 pattern childGuard
    simpa only [d2383, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2356 pattern = 1 := by simpa only [d2383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14604 pattern childGuard
    simpa only [d2383, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14606 (pattern : Twelve) (guard : d2356 pattern = 1) : d1026 pattern ≤ (2 : Int) + d2383 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d2356 pattern = 1 := by simpa only [d1026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14591 pattern childGuard
    simpa only [d1026, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2356 pattern = 1 := by simpa only [d1026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14605 pattern childGuard
    simpa only [d1026, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14607 (pattern : Twelve) (guard : d2356 pattern = 1) : d1021 pattern ≤ (2 : Int) + d2376 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2355 pattern = 1 := by simpa only [d2356, d1021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14581 pattern childGuard
    simpa only [d2356, d1021, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2356, d1021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14599 pattern childGuard
    simpa only [d2356, d1021, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14608 (pattern : Twelve) (guard : d2356 pattern = 1) : d1021 pattern ≤ (2 : Int) + d2380 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2355 pattern = 1 := by simpa only [d2356, d1021, d2380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14581 pattern childGuard
    simpa only [d2356, d1021, d2380, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2356, d1021, d2380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14601 pattern childGuard
    simpa only [d2356, d1021, d2380, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14609 (pattern : Twelve) (guard : d2356 pattern = 1) : d1021 pattern ≤ (2 : Int) + d2382 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d2356 pattern = 1 := by simpa only [d2382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14608 pattern childGuard
    simpa only [d2382, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2356 pattern = 1 := by simpa only [d2382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14589 pattern childGuard
    simpa only [d2382, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14610 (pattern : Twelve) (guard : d2356 pattern = 1) : d1021 pattern ≤ (2 : Int) + d2383 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d2356 pattern = 1 := by simpa only [d2383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14607 pattern childGuard
    simpa only [d2383, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2356 pattern = 1 := by simpa only [d2383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14609 pattern childGuard
    simpa only [d2383, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14611 (pattern : Twelve) (guard : d2356 pattern = 1) : d1027 pattern ≤ (2 : Int) + d2383 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d2356 pattern = 1 := by simpa only [d1027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14610 pattern childGuard
    simpa only [d1027, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2356 pattern = 1 := by simpa only [d1027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14605 pattern childGuard
    simpa only [d1027, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14612 (pattern : Twelve) (guard : d2356 pattern = 1) : d1028 pattern ≤ (2 : Int) + d2383 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d2356 pattern = 1 := by simpa only [d1028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14606 pattern childGuard
    simpa only [d1028, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2356 pattern = 1 := by simpa only [d1028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14611 pattern childGuard
    simpa only [d1028, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14613 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (2 : Int) + d2385 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14614 (pattern : Twelve) (guard : d2356 pattern = 1) : d1021 pattern ≤ (2 : Int) + d2386 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2355 pattern = 1 := by simpa only [d2356, d1021, d2386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14581 pattern childGuard
    simpa only [d2356, d1021, d2386, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2356, d1021, d2386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14613 pattern childGuard
    simpa only [d2356, d1021, d2386, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14615 (pattern : Twelve) (guard : d2356 pattern = 1) : d1021 pattern ≤ (2 : Int) + d2387 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d2356 pattern = 1 := by simpa only [d2387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14614 pattern childGuard
    simpa only [d2387, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2356 pattern = 1 := by simpa only [d2387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14589 pattern childGuard
    simpa only [d2387, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14616 (pattern : Twelve) (guard : d2356 pattern = 1) : d1021 pattern ≤ (2 : Int) + d2388 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d2356 pattern = 1 := by simpa only [d2388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14607 pattern childGuard
    simpa only [d2388, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2356 pattern = 1 := by simpa only [d2388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14615 pattern childGuard
    simpa only [d2388, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14617 (pattern : Twelve) (guard : d2356 pattern = 1) : d1022 pattern ≤ (2 : Int) + d2386 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2355 pattern = 1 := by simpa only [d2356, d1022, d2386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14598 pattern childGuard
    simpa only [d2356, d1022, d2386, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2356, d1022, d2386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14613 pattern childGuard
    simpa only [d2356, d1022, d2386, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14618 (pattern : Twelve) (guard : d2356 pattern = 1) : d1022 pattern ≤ (2 : Int) + d2387 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d2356 pattern = 1 := by simpa only [d2387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14617 pattern childGuard
    simpa only [d2387, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2356 pattern = 1 := by simpa only [d2387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14603 pattern childGuard
    simpa only [d2387, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14619 (pattern : Twelve) (guard : d2356 pattern = 1) : d1022 pattern ≤ (2 : Int) + d2388 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d2356 pattern = 1 := by simpa only [d2388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14600 pattern childGuard
    simpa only [d2388, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2356 pattern = 1 := by simpa only [d2388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14618 pattern childGuard
    simpa only [d2388, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14620 (pattern : Twelve) (guard : d2356 pattern = 1) : d1027 pattern ≤ (2 : Int) + d2388 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d2356 pattern = 1 := by simpa only [d1027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14616 pattern childGuard
    simpa only [d1027, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2356 pattern = 1 := by simpa only [d1027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14619 pattern childGuard
    simpa only [d1027, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14621 (pattern : Twelve) (guard : d2356 pattern = 1) : d1029 pattern ≤ (2 : Int) + d2389 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d2356 pattern = 1 := by simpa only [d1029, d2389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14612 pattern childGuard
    simpa only [d1029, d2389, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2356 pattern = 1 := by simpa only [d1029, d2389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14620 pattern childGuard
    simpa only [d1029, d2389, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14622 (pattern : Twelve) (guard : d0 pattern = 1) : d17 pattern ≤ (2 : Int) + d1275 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14623 (pattern : Twelve) (guard : d1 pattern = 1) : d7 pattern ≤ (2 : Int) + d8 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13901 pattern childGuard
    simpa only [d7, d8, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14008 pattern childGuard
    simpa only [d7, d8, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14624 (pattern : Twelve) (guard : d1 pattern = 1) : d17 pattern ≤ (2 : Int) + d1275 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, d1275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14502 pattern childGuard
    simpa only [d17, d1275, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, d1275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14623 pattern childGuard
    simpa only [d17, d1275, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14625 (pattern : Twelve) (guard : d26 pattern = 1) : d17 pattern ≤ (2 : Int) + d1275 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14622 pattern childGuard
    simpa only [d26, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14624 pattern childGuard
    simpa only [d26, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14626 (pattern : Twelve) (guard : d0 pattern = 1) : d17 pattern ≤ (2 : Int) + d872 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14627 (pattern : Twelve) (guard : d1 pattern = 1) : d17 pattern ≤ (2 : Int) + d872 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, d872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13901 pattern childGuard
    simpa only [d17, d872, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, d872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14623 pattern childGuard
    simpa only [d17, d872, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14628 (pattern : Twelve) (guard : d26 pattern = 1) : d17 pattern ≤ (2 : Int) + d872 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14626 pattern childGuard
    simpa only [d26, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14627 pattern childGuard
    simpa only [d26, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14629 (pattern : Twelve) (guard : d26 pattern = 1) : d17 pattern ≤ (2 : Int) + d2390 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14625 pattern childGuard
    simpa only [d2390, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d26 pattern = 1 := by simpa only [d2390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14628 pattern childGuard
    simpa only [d2390, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14630 (pattern : Twelve) (guard : d0 pattern = 1) : d1284 pattern ≤ (2 : Int) + d2390 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14631 (pattern : Twelve) (guard : d2355 pattern = 1) : d1293 pattern ≤ (2 : Int) + d2390 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2355, d1293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14629 pattern childGuard
    simpa only [d2355, d1293, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2355, d1293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14630 pattern childGuard
    simpa only [d2355, d1293, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14632 (pattern : Twelve) (guard : d0 pattern = 1) : d19 pattern ≤ (2 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14633 (pattern : Twelve) (guard : d26 pattern = 1) : d19 pattern ≤ (2 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14632 pattern childGuard
    simpa only [d26, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13924 pattern childGuard
    simpa only [d26, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14634 (pattern : Twelve) (guard : d2355 pattern = 1) : d1294 pattern ≤ (2 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2355, d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14633 pattern childGuard
    simpa only [d2355, d1294, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2355, d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13925 pattern childGuard
    simpa only [d2355, d1294, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14635 (pattern : Twelve) (guard : d2355 pattern = 1) : d1305 pattern ≤ (2 : Int) + d2391 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2355 pattern = 1 := by simpa only [d1305, d2391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14631 pattern childGuard
    simpa only [d1305, d2391, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2355 pattern = 1 := by simpa only [d1305, d2391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14634 pattern childGuard
    simpa only [d1305, d2391, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14636 (pattern : Twelve) (guard : d0 pattern = 1) : d1357 pattern ≤ (2 : Int) + d2391 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14637 (pattern : Twelve) (guard : d2356 pattern = 1) : d1435 pattern ≤ (2 : Int) + d2391 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2355 pattern = 1 := by simpa only [d2356, d1435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14635 pattern childGuard
    simpa only [d2356, d1435, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2356, d1435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14636 pattern childGuard
    simpa only [d2356, d1435, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14638 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (2 : Int) + d2391 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14639 (pattern : Twelve) (guard : d2356 pattern = 1) : d1436 pattern ≤ (2 : Int) + d2391 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2355 pattern = 1 := by simpa only [d2356, d1436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14635 pattern childGuard
    simpa only [d2356, d1436, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2356, d1436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14638 pattern childGuard
    simpa only [d2356, d1436, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14640 (pattern : Twelve) (guard : d2356 pattern = 1) : d1438 pattern ≤ (2 : Int) + d2391 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d2356 pattern = 1 := by simpa only [d1438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14637 pattern childGuard
    simpa only [d1438, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2356 pattern = 1 := by simpa only [d1438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14639 pattern childGuard
    simpa only [d1438, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14641 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (2 : Int) + d2393 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14642 (pattern : Twelve) (guard : d2356 pattern = 1) : d1436 pattern ≤ (2 : Int) + d2394 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2355 pattern = 1 := by simpa only [d2356, d1436, d2394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14635 pattern childGuard
    simpa only [d2356, d1436, d2394, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2356, d1436, d2394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14641 pattern childGuard
    simpa only [d2356, d1436, d2394, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14643 (pattern : Twelve) (guard : d2356 pattern = 1) : d1436 pattern ≤ (2 : Int) + d2395 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2355 pattern = 1 := by simpa only [d2356, d1436, d2395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14635 pattern childGuard
    simpa only [d2356, d1436, d2395, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2356, d1436, d2395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13925 pattern childGuard
    simpa only [d2356, d1436, d2395, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14644 (pattern : Twelve) (guard : d2356 pattern = 1) : d1436 pattern ≤ (2 : Int) + d2396 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d2356 pattern = 1 := by simpa only [d2396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14642 pattern childGuard
    simpa only [d2396, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2356 pattern = 1 := by simpa only [d2396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14643 pattern childGuard
    simpa only [d2396, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14645 (pattern : Twelve) (guard : d2356 pattern = 1) : d1439 pattern ≤ (2 : Int) + d2397 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d2356 pattern = 1 := by simpa only [d1439, d2397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14640 pattern childGuard
    simpa only [d1439, d2397, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2356 pattern = 1 := by simpa only [d1439, d2397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14644 pattern childGuard
    simpa only [d1439, d2397, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14646 (pattern : Twelve) (guard : d26 pattern = 1) : d1283 pattern ≤ (2 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d26, d1283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14632 pattern childGuard
    simpa only [d26, d1283, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d26, d1283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13538 pattern childGuard
    simpa only [d26, d1283, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14647 (pattern : Twelve) (guard : d2355 pattern = 1) : d1301 pattern ≤ (2 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2355, d1301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14646 pattern childGuard
    simpa only [d2355, d1301, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2355, d1301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13925 pattern childGuard
    simpa only [d2355, d1301, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14648 (pattern : Twelve) (guard : d2355 pattern = 1) : d1309 pattern ≤ (2 : Int) + d2391 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2355 pattern = 1 := by simpa only [d1309, d2391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14631 pattern childGuard
    simpa only [d1309, d2391, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2355 pattern = 1 := by simpa only [d1309, d2391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14647 pattern childGuard
    simpa only [d1309, d2391, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14649 (pattern : Twelve) (guard : d2356 pattern = 1) : d1437 pattern ≤ (2 : Int) + d2391 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2355 pattern = 1 := by simpa only [d2356, d1437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14648 pattern childGuard
    simpa only [d2356, d1437, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2356, d1437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14638 pattern childGuard
    simpa only [d2356, d1437, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14650 (pattern : Twelve) (guard : d2356 pattern = 1) : d1437 pattern ≤ (2 : Int) + d2394 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2355 pattern = 1 := by simpa only [d2356, d1437, d2394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14648 pattern childGuard
    simpa only [d2356, d1437, d2394, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2356, d1437, d2394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14641 pattern childGuard
    simpa only [d2356, d1437, d2394, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14651 (pattern : Twelve) (guard : d2356 pattern = 1) : d1437 pattern ≤ (2 : Int) + d2395 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2355 pattern = 1 := by simpa only [d2356, d1437, d2395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14648 pattern childGuard
    simpa only [d2356, d1437, d2395, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2356, d1437, d2395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13925 pattern childGuard
    simpa only [d2356, d1437, d2395, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14652 (pattern : Twelve) (guard : d2356 pattern = 1) : d1437 pattern ≤ (2 : Int) + d2396 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d2356 pattern = 1 := by simpa only [d2396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14650 pattern childGuard
    simpa only [d2396, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2356 pattern = 1 := by simpa only [d2396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14651 pattern childGuard
    simpa only [d2396, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14653 (pattern : Twelve) (guard : d2356 pattern = 1) : d1437 pattern ≤ (2 : Int) + d2397 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d2356 pattern = 1 := by simpa only [d2397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14649 pattern childGuard
    simpa only [d2397, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2356 pattern = 1 := by simpa only [d2397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14652 pattern childGuard
    simpa only [d2397, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14654 (pattern : Twelve) (guard : d2356 pattern = 1) : d1440 pattern ≤ (2 : Int) + d2397 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d2356 pattern = 1 := by simpa only [d1440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14645 pattern childGuard
    simpa only [d1440, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2356 pattern = 1 := by simpa only [d1440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14653 pattern childGuard
    simpa only [d1440, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14655 (pattern : Twelve) (guard : d2356 pattern = 1) : d1436 pattern ≤ (2 : Int) + d2397 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d2356 pattern = 1 := by simpa only [d2397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14639 pattern childGuard
    simpa only [d2397, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2356 pattern = 1 := by simpa only [d2397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14644 pattern childGuard
    simpa only [d2397, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14656 (pattern : Twelve) (guard : d2356 pattern = 1) : d1441 pattern ≤ (2 : Int) + d2397 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d2356 pattern = 1 := by simpa only [d1441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14655 pattern childGuard
    simpa only [d1441, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2356 pattern = 1 := by simpa only [d1441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14653 pattern childGuard
    simpa only [d1441, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14657 (pattern : Twelve) (guard : d2356 pattern = 1) : d1442 pattern ≤ (2 : Int) + d2397 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d2356 pattern = 1 := by simpa only [d1442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14654 pattern childGuard
    simpa only [d1442, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2356 pattern = 1 := by simpa only [d1442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14656 pattern childGuard
    simpa only [d1442, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14658 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (2 : Int) + d2399 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14659 (pattern : Twelve) (guard : d2356 pattern = 1) : d1436 pattern ≤ (2 : Int) + d2400 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2355 pattern = 1 := by simpa only [d2356, d1436, d2400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14635 pattern childGuard
    simpa only [d2356, d1436, d2400, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2356, d1436, d2400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14658 pattern childGuard
    simpa only [d2356, d1436, d2400, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14660 (pattern : Twelve) (guard : d2356 pattern = 1) : d1436 pattern ≤ (2 : Int) + d2401 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d2356 pattern = 1 := by simpa only [d2401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14659 pattern childGuard
    simpa only [d2401, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2356 pattern = 1 := by simpa only [d2401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14643 pattern childGuard
    simpa only [d2401, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14661 (pattern : Twelve) (guard : d2356 pattern = 1) : d1436 pattern ≤ (2 : Int) + d2402 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d2356 pattern = 1 := by simpa only [d2402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14639 pattern childGuard
    simpa only [d2402, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2356 pattern = 1 := by simpa only [d2402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14660 pattern childGuard
    simpa only [d2402, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14662 (pattern : Twelve) (guard : d2356 pattern = 1) : d1437 pattern ≤ (2 : Int) + d2400 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2355 pattern = 1 := by simpa only [d2356, d1437, d2400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14648 pattern childGuard
    simpa only [d2356, d1437, d2400, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2356, d1437, d2400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14658 pattern childGuard
    simpa only [d2356, d1437, d2400, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14663 (pattern : Twelve) (guard : d2356 pattern = 1) : d1437 pattern ≤ (2 : Int) + d2401 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d2356 pattern = 1 := by simpa only [d2401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14662 pattern childGuard
    simpa only [d2401, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2356 pattern = 1 := by simpa only [d2401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14651 pattern childGuard
    simpa only [d2401, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14664 (pattern : Twelve) (guard : d2356 pattern = 1) : d1437 pattern ≤ (2 : Int) + d2402 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d2356 pattern = 1 := by simpa only [d2402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14649 pattern childGuard
    simpa only [d2402, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2356 pattern = 1 := by simpa only [d2402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14663 pattern childGuard
    simpa only [d2402, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14665 (pattern : Twelve) (guard : d2356 pattern = 1) : d1441 pattern ≤ (2 : Int) + d2402 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d2356 pattern = 1 := by simpa only [d1441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14661 pattern childGuard
    simpa only [d1441, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2356 pattern = 1 := by simpa only [d1441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14664 pattern childGuard
    simpa only [d1441, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14666 (pattern : Twelve) (guard : d2356 pattern = 1) : d1443 pattern ≤ (2 : Int) + d2403 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d2356 pattern = 1 := by simpa only [d1443, d2403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14657 pattern childGuard
    simpa only [d1443, d2403, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2356 pattern = 1 := by simpa only [d1443, d2403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14665 pattern childGuard
    simpa only [d1443, d2403, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14667 (pattern : Twelve) (guard : d0 pattern = 1) : d19 pattern ≤ (2 : Int) + d1324 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14668 (pattern : Twelve) (guard : d1 pattern = 1) : d10 pattern ≤ (2 : Int) + d11 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d10, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13901 pattern childGuard
    simpa only [d10, d11, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d10, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13479 pattern childGuard
    simpa only [d10, d11, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14669 (pattern : Twelve) (guard : d1 pattern = 1) : d11 pattern ≤ (2 : Int) + d16 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14008 pattern childGuard
    simpa only [d11, d16, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13488 pattern childGuard
    simpa only [d11, d16, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14670 (pattern : Twelve) (guard : d1 pattern = 1) : d19 pattern ≤ (2 : Int) + d1324 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d19, d1324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14668 pattern childGuard
    simpa only [d19, d1324, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d19, d1324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14669 pattern childGuard
    simpa only [d19, d1324, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14671 (pattern : Twelve) (guard : d26 pattern = 1) : d19 pattern ≤ (2 : Int) + d1324 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14667 pattern childGuard
    simpa only [d26, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14670 pattern childGuard
    simpa only [d26, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14672 (pattern : Twelve) (guard : d2355 pattern = 1) : d1649 pattern ≤ (2 : Int) + d1324 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2355, d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14671 pattern childGuard
    simpa only [d2355, d1649, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2355, d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14450 pattern childGuard
    simpa only [d2355, d1649, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14673 (pattern : Twelve) (guard : d26 pattern = 1) : d25 pattern ≤ (2 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14366 pattern childGuard
    simpa only [d26, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13577 pattern childGuard
    simpa only [d26, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14674 (pattern : Twelve) (guard : d2355 pattern = 1) : d1650 pattern ≤ (2 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2355, d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14673 pattern childGuard
    simpa only [d2355, d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2355, d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13925 pattern childGuard
    simpa only [d2355, d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14675 (pattern : Twelve) (guard : d2355 pattern = 1) : d1656 pattern ≤ (2 : Int) + d2404 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2355 pattern = 1 := by simpa only [d1656, d2404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14672 pattern childGuard
    simpa only [d1656, d2404, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2355 pattern = 1 := by simpa only [d1656, d2404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14674 pattern childGuard
    simpa only [d1656, d2404, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14676 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (2 : Int) + d2404 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14677 (pattern : Twelve) (guard : d2356 pattern = 1) : d1715 pattern ≤ (2 : Int) + d2404 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2355 pattern = 1 := by simpa only [d2356, d1715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14675 pattern childGuard
    simpa only [d2356, d1715, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2356, d1715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14676 pattern childGuard
    simpa only [d2356, d1715, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14678 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (2 : Int) + d2405 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14679 (pattern : Twelve) (guard : d2356 pattern = 1) : d1715 pattern ≤ (2 : Int) + d2406 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2355 pattern = 1 := by simpa only [d2356, d1715, d2406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14675 pattern childGuard
    simpa only [d2356, d1715, d2406, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2356, d1715, d2406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14678 pattern childGuard
    simpa only [d2356, d1715, d2406, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14680 (pattern : Twelve) (guard : d2356 pattern = 1) : d1715 pattern ≤ (2 : Int) + d2407 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2355 pattern = 1 := by simpa only [d2356, d1715, d2407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14675 pattern childGuard
    simpa only [d2356, d1715, d2407, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2356, d1715, d2407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13925 pattern childGuard
    simpa only [d2356, d1715, d2407, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14681 (pattern : Twelve) (guard : d2356 pattern = 1) : d1715 pattern ≤ (2 : Int) + d2408 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d2356 pattern = 1 := by simpa only [d2408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14679 pattern childGuard
    simpa only [d2408, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2356 pattern = 1 := by simpa only [d2408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14680 pattern childGuard
    simpa only [d2408, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14682 (pattern : Twelve) (guard : d2356 pattern = 1) : d1715 pattern ≤ (2 : Int) + d2409 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d2356 pattern = 1 := by simpa only [d2409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14677 pattern childGuard
    simpa only [d2409, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2356 pattern = 1 := by simpa only [d2409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14681 pattern childGuard
    simpa only [d2409, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14683 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (2 : Int) + d2411 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14684 (pattern : Twelve) (guard : d2356 pattern = 1) : d1715 pattern ≤ (2 : Int) + d2412 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2355 pattern = 1 := by simpa only [d2356, d1715, d2412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14675 pattern childGuard
    simpa only [d2356, d1715, d2412, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2356, d1715, d2412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14683 pattern childGuard
    simpa only [d2356, d1715, d2412, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14685 (pattern : Twelve) (guard : d2356 pattern = 1) : d1715 pattern ≤ (2 : Int) + d2413 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d2356 pattern = 1 := by simpa only [d2413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14684 pattern childGuard
    simpa only [d2413, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2356 pattern = 1 := by simpa only [d2413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14680 pattern childGuard
    simpa only [d2413, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14686 (pattern : Twelve) (guard : d2356 pattern = 1) : d1715 pattern ≤ (2 : Int) + d2414 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d2356 pattern = 1 := by simpa only [d2414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14677 pattern childGuard
    simpa only [d2414, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2356 pattern = 1 := by simpa only [d2414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14685 pattern childGuard
    simpa only [d2414, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14687 (pattern : Twelve) (guard : d2356 pattern = 1) : d1715 pattern ≤ (2 : Int) + d2415 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d2356 pattern = 1 := by simpa only [d2415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14682 pattern childGuard
    simpa only [d2415, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2356 pattern = 1 := by simpa only [d2415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14686 pattern childGuard
    simpa only [d2415, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14688 (pattern : Twelve) (guard : d0 pattern = 1) : d171 pattern ≤ (2 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14689 (pattern : Twelve) (guard : d2301 pattern = 1) : d235 pattern ≤ (2 : Int) + d0 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2301, d235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14501 pattern childGuard
    simpa only [d2301, d235, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2301, d235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14688 pattern childGuard
    simpa only [d2301, d235, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14690 (pattern : Twelve) (guard : d26 pattern = 1) : d26 pattern ≤ (2 : Int) + d0 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14182 pattern childGuard
    simpa only [d26, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13319 pattern childGuard
    simpa only [d26, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14691 (pattern : Twelve) (guard : d0 pattern = 1) : d172 pattern ≤ (2 : Int) + d17 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14692 (pattern : Twelve) (guard : d2301 pattern = 1) : d236 pattern ≤ (2 : Int) + d2357 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2301, d236, d2357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14690 pattern childGuard
    simpa only [d2301, d236, d2357, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2301, d236, d2357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14691 pattern childGuard
    simpa only [d2301, d236, d2357, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14693 (pattern : Twelve) (guard : d2301 pattern = 1) : d256 pattern ≤ (2 : Int) + d2416 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d256, d2416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14689 pattern childGuard
    simpa only [d256, d2416, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d256, d2416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14692 pattern childGuard
    simpa only [d256, d2416, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14694 (pattern : Twelve) (guard : d0 pattern = 1) : d172 pattern ≤ (2 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14695 (pattern : Twelve) (guard : d2301 pattern = 1) : d237 pattern ≤ (2 : Int) + d0 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2301, d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14501 pattern childGuard
    simpa only [d2301, d237, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2301, d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14694 pattern childGuard
    simpa only [d2301, d237, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14696 (pattern : Twelve) (guard : d1 pattern = 1) : d8 pattern ≤ (2 : Int) + d0 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13319 pattern childGuard
    simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13281 pattern childGuard
    simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14697 (pattern : Twelve) (guard : d1 pattern = 1) : d18 pattern ≤ (2 : Int) + d17 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d18, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14696 pattern childGuard
    simpa only [d18, d17, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d18, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13298 pattern childGuard
    simpa only [d18, d17, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14698 (pattern : Twelve) (guard : d26 pattern = 1) : d28 pattern ≤ (2 : Int) + d17 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d26, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14300 pattern childGuard
    simpa only [d26, d28, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d26, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14697 pattern childGuard
    simpa only [d26, d28, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14699 (pattern : Twelve) (guard : d0 pattern = 1) : d173 pattern ≤ (2 : Int) + d19 pattern := by
  change (0 : Int) = 1 at guard
  omega
end NetHack.Sokoban21.Diagram
