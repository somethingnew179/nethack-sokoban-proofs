/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons138
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c19460 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (16 : Int) + d4 pattern := by
  change (2 : Int) ≤ (16 : Int) + 4
  decide
theorem c19461 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (16 : Int) + d16 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19459 pattern childGuard
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19460 pattern childGuard
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19462 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (16 : Int) + d3 pattern := by
  change (2 : Int) ≤ (16 : Int) + 3
  decide
theorem c19463 (pattern : Twelve) (guard : d1 pattern = 1) : d3 pattern ≤ (16 : Int) + d5 pattern := by
  change (3 : Int) ≤ (16 : Int) + 5
  decide
theorem c19464 (pattern : Twelve) (guard : d1 pattern = 1) : d9 pattern ≤ (16 : Int) + d12 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19462 pattern childGuard
    simpa only [d9, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19463 pattern childGuard
    simpa only [d9, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19465 (pattern : Twelve) (guard : d1 pattern = 1) : d23 pattern ≤ (16 : Int) + d25 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19461 pattern childGuard
    simpa only [d23, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19464 pattern childGuard
    simpa only [d23, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19466 (pattern : Twelve) (guard : d1 pattern = 1) : d34 pattern ≤ (16 : Int) + d817 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d34, d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19458 pattern childGuard
    simpa only [d34, d817, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d34, d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19465 pattern childGuard
    simpa only [d34, d817, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19467 (pattern : Twelve) (guard : d1 pattern = 1) : d10 pattern ≤ (16 : Int) + d16 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d10, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19454 pattern childGuard
    simpa only [d10, d16, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d10, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19460 pattern childGuard
    simpa only [d10, d16, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19468 (pattern : Twelve) (guard : d1 pattern = 1) : d11 pattern ≤ (16 : Int) + d12 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19456 pattern childGuard
    simpa only [d11, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19463 pattern childGuard
    simpa only [d11, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19469 (pattern : Twelve) (guard : d1 pattern = 1) : d19 pattern ≤ (16 : Int) + d25 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d19, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19467 pattern childGuard
    simpa only [d19, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d19, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19468 pattern childGuard
    simpa only [d19, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19470 (pattern : Twelve) (guard : d1 pattern = 1) : d6 pattern ≤ (16 : Int) + d6 pattern := by
  omega
theorem c19471 (pattern : Twelve) (guard : d1 pattern = 1) : d29 pattern ≤ (16 : Int) + d42 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d29, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19469 pattern childGuard
    simpa only [d29, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d29, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19470 pattern childGuard
    simpa only [d29, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19472 (pattern : Twelve) (guard : d1 pattern = 1) : d55 pattern ≤ (16 : Int) + d825 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d55, d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19466 pattern childGuard
    simpa only [d55, d825, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d55, d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19471 pattern childGuard
    simpa only [d55, d825, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19473 (pattern : Twelve) (guard : d1 pattern = 1) : d80 pattern ≤ (16 : Int) + d839 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d80, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19453 pattern childGuard
    simpa only [d80, d839, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d80, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19472 pattern childGuard
    simpa only [d80, d839, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19474 (pattern : Twelve) (guard : d1 pattern = 1) : d97 pattern ≤ (16 : Int) + d853 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d97, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19448 pattern childGuard
    simpa only [d97, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d97, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19473 pattern childGuard
    simpa only [d97, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19475 (pattern : Twelve) (guard : d1 pattern = 1) : d30 pattern ≤ (16 : Int) + d30 pattern := by
  omega
theorem c19476 (pattern : Twelve) (guard : d1 pattern = 1) : d3 pattern ≤ (16 : Int) + d6 pattern := by
  change (3 : Int) ≤ (16 : Int) + 6
  decide
theorem c19477 (pattern : Twelve) (guard : d1 pattern = 1) : d5 pattern ≤ (16 : Int) + d6 pattern := by
  change (5 : Int) ≤ (16 : Int) + 6
  decide
theorem c19478 (pattern : Twelve) (guard : d1 pattern = 1) : d12 pattern ≤ (16 : Int) + d6 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19476 pattern childGuard
    simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19477 pattern childGuard
    simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19479 (pattern : Twelve) (guard : d1 pattern = 1) : d4 pattern ≤ (16 : Int) + d6 pattern := by
  change (4 : Int) ≤ (16 : Int) + 6
  decide
theorem c19480 (pattern : Twelve) (guard : d1 pattern = 1) : d13 pattern ≤ (16 : Int) + d6 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19479 pattern childGuard
    simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19470 pattern childGuard
    simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19481 (pattern : Twelve) (guard : d1 pattern = 1) : d20 pattern ≤ (16 : Int) + d6 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19478 pattern childGuard
    simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19480 pattern childGuard
    simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19482 (pattern : Twelve) (guard : d1 pattern = 1) : d31 pattern ≤ (16 : Int) + d35 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d31, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19438 pattern childGuard
    simpa only [d31, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d31, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19481 pattern childGuard
    simpa only [d31, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19483 (pattern : Twelve) (guard : d1 pattern = 1) : d52 pattern ≤ (16 : Int) + d56 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d52, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19475 pattern childGuard
    simpa only [d52, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d52, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19482 pattern childGuard
    simpa only [d52, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19484 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (16 : Int) + d9 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19459 pattern childGuard
    simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19462 pattern childGuard
    simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19485 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (16 : Int) + d23 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19459 pattern childGuard
    simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19484 pattern childGuard
    simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19486 (pattern : Twelve) (guard : d1 pattern = 1) : d30 pattern ≤ (16 : Int) + d34 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d30, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19441 pattern childGuard
    simpa only [d30, d34, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d30, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19485 pattern childGuard
    simpa only [d30, d34, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19487 (pattern : Twelve) (guard : d1 pattern = 1) : d1 pattern ≤ (16 : Int) + d0 pattern := by
  change (1 : Int) ≤ (16 : Int) + 0
  decide
theorem c19488 (pattern : Twelve) (guard : d1 pattern = 1) : d1 pattern ≤ (16 : Int) + d7 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19487 pattern childGuard
    simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19442 pattern childGuard
    simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19489 (pattern : Twelve) (guard : d1 pattern = 1) : d1 pattern ≤ (16 : Int) + d814 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19488 pattern childGuard
    simpa only [d814, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19442 pattern childGuard
    simpa only [d814, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19490 (pattern : Twelve) (guard : d1 pattern = 1) : d14 pattern ≤ (16 : Int) + d6 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19477 pattern childGuard
    simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19470 pattern childGuard
    simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19491 (pattern : Twelve) (guard : d1 pattern = 1) : d21 pattern ≤ (16 : Int) + d6 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19480 pattern childGuard
    simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19490 pattern childGuard
    simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19492 (pattern : Twelve) (guard : d1 pattern = 1) : d43 pattern ≤ (16 : Int) + d818 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d43, d818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19489 pattern childGuard
    simpa only [d43, d818, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d43, d818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19491 pattern childGuard
    simpa only [d43, d818, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19493 (pattern : Twelve) (guard : d1 pattern = 1) : d62 pattern ≤ (16 : Int) + d826 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d62, d826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19486 pattern childGuard
    simpa only [d62, d826, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d62, d826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19492 pattern childGuard
    simpa only [d62, d826, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19494 (pattern : Twelve) (guard : d1 pattern = 1) : d83 pattern ≤ (16 : Int) + d840 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d83, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19483 pattern childGuard
    simpa only [d83, d840, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d83, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19493 pattern childGuard
    simpa only [d83, d840, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19495 (pattern : Twelve) (guard : d1 pattern = 1) : d22 pattern ≤ (16 : Int) + d6 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19490 pattern childGuard
    simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19470 pattern childGuard
    simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19496 (pattern : Twelve) (guard : d1 pattern = 1) : d44 pattern ≤ (16 : Int) + d36 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d44, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19452 pattern childGuard
    simpa only [d44, d36, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d44, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19495 pattern childGuard
    simpa only [d44, d36, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19497 (pattern : Twelve) (guard : d1 pattern = 1) : d63 pattern ≤ (16 : Int) + d827 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d63, d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19486 pattern childGuard
    simpa only [d63, d827, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d63, d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19496 pattern childGuard
    simpa only [d63, d827, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19498 (pattern : Twelve) (guard : d1 pattern = 1) : d40 pattern ≤ (16 : Int) + d42 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d40, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19465 pattern childGuard
    simpa only [d40, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d40, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19470 pattern childGuard
    simpa only [d40, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19499 (pattern : Twelve) (guard : d1 pattern = 1) : d64 pattern ≤ (16 : Int) + d825 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d64, d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19466 pattern childGuard
    simpa only [d64, d825, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d64, d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19498 pattern childGuard
    simpa only [d64, d825, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19500 (pattern : Twelve) (guard : d1 pattern = 1) : d84 pattern ≤ (16 : Int) + d841 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d84, d841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19497 pattern childGuard
    simpa only [d84, d841, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d84, d841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19499 pattern childGuard
    simpa only [d84, d841, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19501 (pattern : Twelve) (guard : d1 pattern = 1) : d98 pattern ≤ (16 : Int) + d854 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d98, d854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19494 pattern childGuard
    simpa only [d98, d854, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d98, d854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19500 pattern childGuard
    simpa only [d98, d854, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19502 (pattern : Twelve) (guard : d1 pattern = 1) : d106 pattern ≤ (16 : Int) + d861 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d106, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19474 pattern childGuard
    simpa only [d106, d861, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d106, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19501 pattern childGuard
    simpa only [d106, d861, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19503 (pattern : Twelve) (guard : d1 pattern = 1) : d56 pattern ≤ (16 : Int) + d56 pattern := by
  omega
theorem c19504 (pattern : Twelve) (guard : d1 pattern = 1) : d45 pattern ≤ (16 : Int) + d818 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d45, d818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19489 pattern childGuard
    simpa only [d45, d818, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d45, d818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19470 pattern childGuard
    simpa only [d45, d818, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19505 (pattern : Twelve) (guard : d1 pattern = 1) : d65 pattern ≤ (16 : Int) + d826 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d65, d826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19486 pattern childGuard
    simpa only [d65, d826, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d65, d826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19504 pattern childGuard
    simpa only [d65, d826, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19506 (pattern : Twelve) (guard : d1 pattern = 1) : d85 pattern ≤ (16 : Int) + d840 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d85, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19503 pattern childGuard
    simpa only [d85, d840, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d85, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19505 pattern childGuard
    simpa only [d85, d840, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19507 (pattern : Twelve) (guard : d1 pattern = 1) : d39 pattern ≤ (16 : Int) + d36 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d39, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19452 pattern childGuard
    simpa only [d39, d36, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d39, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19470 pattern childGuard
    simpa only [d39, d36, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19508 (pattern : Twelve) (guard : d1 pattern = 1) : d66 pattern ≤ (16 : Int) + d827 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d66, d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19486 pattern childGuard
    simpa only [d66, d827, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d66, d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19507 pattern childGuard
    simpa only [d66, d827, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19509 (pattern : Twelve) (guard : d1 pattern = 1) : d86 pattern ≤ (16 : Int) + d841 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d86, d841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19508 pattern childGuard
    simpa only [d86, d841, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d86, d841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19499 pattern childGuard
    simpa only [d86, d841, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19510 (pattern : Twelve) (guard : d1 pattern = 1) : d99 pattern ≤ (16 : Int) + d854 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d99, d854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19506 pattern childGuard
    simpa only [d99, d854, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d99, d854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19509 pattern childGuard
    simpa only [d99, d854, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19511 (pattern : Twelve) (guard : d1 pattern = 1) : d107 pattern ≤ (16 : Int) + d861 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d107, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19474 pattern childGuard
    simpa only [d107, d861, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d107, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19510 pattern childGuard
    simpa only [d107, d861, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19512 (pattern : Twelve) (guard : d1 pattern = 1) : d112 pattern ≤ (16 : Int) + d861 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19502 pattern childGuard
    simpa only [d112, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19511 pattern childGuard
    simpa only [d112, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19513 (pattern : Twelve) (guard : d1 pattern = 1) : d3 pattern ≤ (16 : Int) + d3 pattern := by
  omega
theorem c19514 (pattern : Twelve) (guard : d1 pattern = 1) : d46 pattern ≤ (16 : Int) + d819 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d46, d819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19489 pattern childGuard
    simpa only [d46, d819, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d46, d819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19513 pattern childGuard
    simpa only [d46, d819, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19515 (pattern : Twelve) (guard : d1 pattern = 1) : d67 pattern ≤ (16 : Int) + d828 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d67, d828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19486 pattern childGuard
    simpa only [d67, d828, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d67, d828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19514 pattern childGuard
    simpa only [d67, d828, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19516 (pattern : Twelve) (guard : d1 pattern = 1) : d87 pattern ≤ (16 : Int) + d842 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d87, d842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19475 pattern childGuard
    simpa only [d87, d842, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d87, d842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19515 pattern childGuard
    simpa only [d87, d842, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19517 (pattern : Twelve) (guard : d1 pattern = 1) : d4 pattern ≤ (16 : Int) + d2 pattern := by
  change (4 : Int) ≤ (16 : Int) + 2
  decide
theorem c19518 (pattern : Twelve) (guard : d1 pattern = 1) : d4 pattern ≤ (16 : Int) + d3 pattern := by
  change (4 : Int) ≤ (16 : Int) + 3
  decide
theorem c19519 (pattern : Twelve) (guard : d1 pattern = 1) : d4 pattern ≤ (16 : Int) + d9 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19517 pattern childGuard
    simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19518 pattern childGuard
    simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19520 (pattern : Twelve) (guard : d1 pattern = 1) : d4 pattern ≤ (16 : Int) + d23 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19517 pattern childGuard
    simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19519 pattern childGuard
    simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19521 (pattern : Twelve) (guard : d1 pattern = 1) : d38 pattern ≤ (16 : Int) + d34 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d38, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19452 pattern childGuard
    simpa only [d38, d34, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d38, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19520 pattern childGuard
    simpa only [d38, d34, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19522 (pattern : Twelve) (guard : d1 pattern = 1) : d68 pattern ≤ (16 : Int) + d34 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19486 pattern childGuard
    simpa only [d68, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19521 pattern childGuard
    simpa only [d68, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19523 (pattern : Twelve) (guard : d1 pattern = 1) : d88 pattern ≤ (16 : Int) + d843 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d88, d843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19522 pattern childGuard
    simpa only [d88, d843, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d88, d843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19499 pattern childGuard
    simpa only [d88, d843, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19524 (pattern : Twelve) (guard : d1 pattern = 1) : d100 pattern ≤ (16 : Int) + d855 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d100, d855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19516 pattern childGuard
    simpa only [d100, d855, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d100, d855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19523 pattern childGuard
    simpa only [d100, d855, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19525 (pattern : Twelve) (guard : d1 pattern = 1) : d59 pattern ≤ (16 : Int) + d59 pattern := by
  omega
theorem c19526 (pattern : Twelve) (guard : d1 pattern = 1) : d4 pattern ≤ (16 : Int) + d4 pattern := by
  omega
theorem c19527 (pattern : Twelve) (guard : d1 pattern = 1) : d4 pattern ≤ (16 : Int) + d5 pattern := by
  change (4 : Int) ≤ (16 : Int) + 5
  decide
theorem c19528 (pattern : Twelve) (guard : d1 pattern = 1) : d4 pattern ≤ (16 : Int) + d15 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19526 pattern childGuard
    simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19527 pattern childGuard
    simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19529 (pattern : Twelve) (guard : d1 pattern = 1) : d4 pattern ≤ (16 : Int) + d24 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19526 pattern childGuard
    simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19528 pattern childGuard
    simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19530 (pattern : Twelve) (guard : d1 pattern = 1) : d38 pattern ≤ (16 : Int) + d41 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d38, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19485 pattern childGuard
    simpa only [d38, d41, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d38, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19529 pattern childGuard
    simpa only [d38, d41, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19531 (pattern : Twelve) (guard : d1 pattern = 1) : d3 pattern ≤ (16 : Int) + d2 pattern := by
  change (3 : Int) ≤ (16 : Int) + 2
  decide
theorem c19532 (pattern : Twelve) (guard : d1 pattern = 1) : d3 pattern ≤ (16 : Int) + d9 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19531 pattern childGuard
    simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19513 pattern childGuard
    simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19533 (pattern : Twelve) (guard : d1 pattern = 1) : d3 pattern ≤ (16 : Int) + d815 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19532 pattern childGuard
    simpa only [d815, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19513 pattern childGuard
    simpa only [d815, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19534 (pattern : Twelve) (guard : d1 pattern = 1) : d47 pattern ≤ (16 : Int) + d820 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d47, d820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19533 pattern childGuard
    simpa only [d47, d820, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d47, d820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19470 pattern childGuard
    simpa only [d47, d820, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19535 (pattern : Twelve) (guard : d1 pattern = 1) : d69 pattern ≤ (16 : Int) + d829 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d69, d829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19530 pattern childGuard
    simpa only [d69, d829, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d69, d829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19534 pattern childGuard
    simpa only [d69, d829, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19536 (pattern : Twelve) (guard : d1 pattern = 1) : d89 pattern ≤ (16 : Int) + d844 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d89, d844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19525 pattern childGuard
    simpa only [d89, d844, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d89, d844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19535 pattern childGuard
    simpa only [d89, d844, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19537 (pattern : Twelve) (guard : d1 pattern = 1) : d48 pattern ≤ (16 : Int) + d40 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d48, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19520 pattern childGuard
    simpa only [d48, d40, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d48, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19470 pattern childGuard
    simpa only [d48, d40, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19538 (pattern : Twelve) (guard : d1 pattern = 1) : d70 pattern ≤ (16 : Int) + d830 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d70, d830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19530 pattern childGuard
    simpa only [d70, d830, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d70, d830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19537 pattern childGuard
    simpa only [d70, d830, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19539 (pattern : Twelve) (guard : d1 pattern = 1) : d4 pattern ≤ (16 : Int) + d13 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19526 pattern childGuard
    simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19479 pattern childGuard
    simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19540 (pattern : Twelve) (guard : d1 pattern = 1) : d15 pattern ≤ (16 : Int) + d14 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d15, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19527 pattern childGuard
    simpa only [d15, d14, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d15, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19477 pattern childGuard
    simpa only [d15, d14, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19541 (pattern : Twelve) (guard : d1 pattern = 1) : d24 pattern ≤ (16 : Int) + d21 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d24, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19539 pattern childGuard
    simpa only [d24, d21, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d24, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19540 pattern childGuard
    simpa only [d24, d21, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19542 (pattern : Twelve) (guard : d1 pattern = 1) : d41 pattern ≤ (16 : Int) + d821 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d41, d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19465 pattern childGuard
    simpa only [d41, d821, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d41, d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19541 pattern childGuard
    simpa only [d41, d821, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19543 (pattern : Twelve) (guard : d1 pattern = 1) : d49 pattern ≤ (16 : Int) + d822 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d49, d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19541 pattern childGuard
    simpa only [d49, d822, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d49, d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19470 pattern childGuard
    simpa only [d49, d822, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19544 (pattern : Twelve) (guard : d1 pattern = 1) : d71 pattern ≤ (16 : Int) + d831 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d71, d831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19542 pattern childGuard
    simpa only [d71, d831, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d71, d831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19543 pattern childGuard
    simpa only [d71, d831, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19545 (pattern : Twelve) (guard : d1 pattern = 1) : d90 pattern ≤ (16 : Int) + d845 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d90, d845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19538 pattern childGuard
    simpa only [d90, d845, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d90, d845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19544 pattern childGuard
    simpa only [d90, d845, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19546 (pattern : Twelve) (guard : d1 pattern = 1) : d101 pattern ≤ (16 : Int) + d856 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d101, d856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19536 pattern childGuard
    simpa only [d101, d856, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d101, d856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19545 pattern childGuard
    simpa only [d101, d856, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19547 (pattern : Twelve) (guard : d1 pattern = 1) : d108 pattern ≤ (16 : Int) + d862 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d108, d862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19524 pattern childGuard
    simpa only [d108, d862, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d108, d862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19546 pattern childGuard
    simpa only [d108, d862, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19548 (pattern : Twelve) (guard : d1 pattern = 1) : d109 pattern ≤ (16 : Int) + d863 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d109, d863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19510 pattern childGuard
    simpa only [d109, d863, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d109, d863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19470 pattern childGuard
    simpa only [d109, d863, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19549 (pattern : Twelve) (guard : d1 pattern = 1) : d113 pattern ≤ (16 : Int) + d867 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d113, d867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19547 pattern childGuard
    simpa only [d113, d867, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d113, d867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19548 pattern childGuard
    simpa only [d113, d867, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19550 (pattern : Twelve) (guard : d1 pattern = 1) : d115 pattern ≤ (16 : Int) + d869 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d115, d869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19512 pattern childGuard
    simpa only [d115, d869, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d115, d869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19549 pattern childGuard
    simpa only [d115, d869, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19551 (pattern : Twelve) (guard : d1872 pattern = 1) : d116 pattern ≤ (16 : Int) + d869 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1872, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19437 pattern childGuard
    simpa only [d1872, d116, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1872, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19550 pattern childGuard
    simpa only [d1872, d116, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19552 (pattern : Twelve) (guard : d0 pattern = 1) : d155 pattern ≤ (16 : Int) + d906 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c19553 (pattern : Twelve) (guard : d1 pattern = 1) : d3 pattern ≤ (16 : Int) + d1 pattern := by
  change (3 : Int) ≤ (16 : Int) + 1
  decide
theorem c19554 (pattern : Twelve) (guard : d1 pattern = 1) : d3 pattern ≤ (16 : Int) + d8 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19553 pattern childGuard
    simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19531 pattern childGuard
    simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19555 (pattern : Twelve) (guard : d1 pattern = 1) : d3 pattern ≤ (16 : Int) + d872 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19553 pattern childGuard
    simpa only [d872, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19554 pattern childGuard
    simpa only [d872, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19556 (pattern : Twelve) (guard : d1 pattern = 1) : d778 pattern ≤ (16 : Int) + d874 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d778, d874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19452 pattern childGuard
    simpa only [d778, d874, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d778, d874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19555 pattern childGuard
    simpa only [d778, d874, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19557 (pattern : Twelve) (guard : d1 pattern = 1) : d9 pattern ≤ (16 : Int) + d1 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19450 pattern childGuard
    simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19553 pattern childGuard
    simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19558 (pattern : Twelve) (guard : d1 pattern = 1) : d23 pattern ≤ (16 : Int) + d814 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19451 pattern childGuard
    simpa only [d23, d814, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19557 pattern childGuard
    simpa only [d23, d814, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19559 (pattern : Twelve) (guard : d1 pattern = 1) : d779 pattern ≤ (16 : Int) + d875 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d779, d875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19558 pattern childGuard
    simpa only [d779, d875, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d779, d875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19555 pattern childGuard
    simpa only [d779, d875, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19560 (pattern : Twelve) (guard : d1 pattern = 1) : d782 pattern ≤ (16 : Int) + d882 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d782, d882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19556 pattern childGuard
    simpa only [d782, d882, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d782, d882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19559 pattern childGuard
    simpa only [d782, d882, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19561 (pattern : Twelve) (guard : d1 pattern = 1) : d788 pattern ≤ (16 : Int) + d890 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d788, d890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19449 pattern childGuard
    simpa only [d788, d890, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d788, d890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19560 pattern childGuard
    simpa only [d788, d890, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19562 (pattern : Twelve) (guard : d1 pattern = 1) : d4 pattern ≤ (16 : Int) + d0 pattern := by
  change (4 : Int) ≤ (16 : Int) + 0
  decide
theorem c19563 (pattern : Twelve) (guard : d1 pattern = 1) : d4 pattern ≤ (16 : Int) + d1 pattern := by
  change (4 : Int) ≤ (16 : Int) + 1
  decide
theorem c19564 (pattern : Twelve) (guard : d1 pattern = 1) : d4 pattern ≤ (16 : Int) + d7 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19562 pattern childGuard
    simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19563 pattern childGuard
    simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19565 (pattern : Twelve) (guard : d1 pattern = 1) : d4 pattern ≤ (16 : Int) + d17 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19562 pattern childGuard
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19564 pattern childGuard
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19566 (pattern : Twelve) (guard : d1 pattern = 1) : d38 pattern ≤ (16 : Int) + d17 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19452 pattern childGuard
    simpa only [d38, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19565 pattern childGuard
    simpa only [d38, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19567 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (16 : Int) + d10 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19449 pattern childGuard
    simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19459 pattern childGuard
    simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19568 (pattern : Twelve) (guard : d1 pattern = 1) : d9 pattern ≤ (16 : Int) + d11 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19450 pattern childGuard
    simpa only [d9, d11, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19513 pattern childGuard
    simpa only [d9, d11, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19569 (pattern : Twelve) (guard : d1 pattern = 1) : d23 pattern ≤ (16 : Int) + d19 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19567 pattern childGuard
    simpa only [d23, d19, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19568 pattern childGuard
    simpa only [d23, d19, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19570 (pattern : Twelve) (guard : d1 pattern = 1) : d41 pattern ≤ (16 : Int) + d876 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d41, d876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19569 pattern childGuard
    simpa only [d41, d876, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d41, d876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19541 pattern childGuard
    simpa only [d41, d876, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19571 (pattern : Twelve) (guard : d1 pattern = 1) : d42 pattern ≤ (16 : Int) + d42 pattern := by
  omega
theorem c19572 (pattern : Twelve) (guard : d1 pattern = 1) : d61 pattern ≤ (16 : Int) + d883 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d61, d883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19570 pattern childGuard
    simpa only [d61, d883, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d61, d883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19571 pattern childGuard
    simpa only [d61, d883, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19573 (pattern : Twelve) (guard : d1 pattern = 1) : d789 pattern ≤ (16 : Int) + d891 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d789, d891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19566 pattern childGuard
    simpa only [d789, d891, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d789, d891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19572 pattern childGuard
    simpa only [d789, d891, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19574 (pattern : Twelve) (guard : d1 pattern = 1) : d794 pattern ≤ (16 : Int) + d898 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d794, d898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19561 pattern childGuard
    simpa only [d794, d898, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d794, d898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19573 pattern childGuard
    simpa only [d794, d898, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19575 (pattern : Twelve) (guard : d1 pattern = 1) : d38 pattern ≤ (16 : Int) + d30 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d38, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19449 pattern childGuard
    simpa only [d38, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d38, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19517 pattern childGuard
    simpa only [d38, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19576 (pattern : Twelve) (guard : d1 pattern = 1) : d44 pattern ≤ (16 : Int) + d35 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d44, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19449 pattern childGuard
    simpa only [d44, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d44, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19495 pattern childGuard
    simpa only [d44, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19577 (pattern : Twelve) (guard : d1 pattern = 1) : d783 pattern ≤ (16 : Int) + d56 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d783, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19575 pattern childGuard
    simpa only [d783, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d783, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19576 pattern childGuard
    simpa only [d783, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19578 (pattern : Twelve) (guard : d1 pattern = 1) : d4 pattern ≤ (16 : Int) + d815 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19519 pattern childGuard
    simpa only [d815, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19518 pattern childGuard
    simpa only [d815, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19579 (pattern : Twelve) (guard : d1 pattern = 1) : d38 pattern ≤ (16 : Int) + d877 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d38, d877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19452 pattern childGuard
    simpa only [d38, d877, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d38, d877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19578 pattern childGuard
    simpa only [d38, d877, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19580 (pattern : Twelve) (guard : d1 pattern = 1) : d3 pattern ≤ (16 : Int) + d0 pattern := by
  change (3 : Int) ≤ (16 : Int) + 0
  decide
theorem c19581 (pattern : Twelve) (guard : d1 pattern = 1) : d3 pattern ≤ (16 : Int) + d7 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19580 pattern childGuard
    simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19553 pattern childGuard
    simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19582 (pattern : Twelve) (guard : d1 pattern = 1) : d3 pattern ≤ (16 : Int) + d814 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19581 pattern childGuard
    simpa only [d814, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19553 pattern childGuard
    simpa only [d814, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19583 (pattern : Twelve) (guard : d1 pattern = 1) : d47 pattern ≤ (16 : Int) + d818 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d47, d818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19582 pattern childGuard
    simpa only [d47, d818, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d47, d818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19470 pattern childGuard
    simpa only [d47, d818, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19584 (pattern : Twelve) (guard : d1 pattern = 1) : d69 pattern ≤ (16 : Int) + d884 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d69, d884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19579 pattern childGuard
    simpa only [d69, d884, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d69, d884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19583 pattern childGuard
    simpa only [d69, d884, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19585 (pattern : Twelve) (guard : d1 pattern = 1) : d790 pattern ≤ (16 : Int) + d892 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d790, d892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19577 pattern childGuard
    simpa only [d790, d892, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d790, d892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19584 pattern childGuard
    simpa only [d790, d892, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19586 (pattern : Twelve) (guard : d1 pattern = 1) : d48 pattern ≤ (16 : Int) + d36 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d48, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19565 pattern childGuard
    simpa only [d48, d36, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d48, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19470 pattern childGuard
    simpa only [d48, d36, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19587 (pattern : Twelve) (guard : d1 pattern = 1) : d70 pattern ≤ (16 : Int) + d827 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d70, d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19521 pattern childGuard
    simpa only [d70, d827, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d70, d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19586 pattern childGuard
    simpa only [d70, d827, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19588 (pattern : Twelve) (guard : d1 pattern = 1) : d4 pattern ≤ (16 : Int) + d16 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19517 pattern childGuard
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19526 pattern childGuard
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19589 (pattern : Twelve) (guard : d1 pattern = 1) : d5 pattern ≤ (16 : Int) + d5 pattern := by
  omega
theorem c19590 (pattern : Twelve) (guard : d1 pattern = 1) : d15 pattern ≤ (16 : Int) + d12 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d15, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19518 pattern childGuard
    simpa only [d15, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d15, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19589 pattern childGuard
    simpa only [d15, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19591 (pattern : Twelve) (guard : d1 pattern = 1) : d24 pattern ≤ (16 : Int) + d25 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d24, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19588 pattern childGuard
    simpa only [d24, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d24, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19590 pattern childGuard
    simpa only [d24, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19592 (pattern : Twelve) (guard : d1 pattern = 1) : d49 pattern ≤ (16 : Int) + d42 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d49, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19591 pattern childGuard
    simpa only [d49, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d49, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19470 pattern childGuard
    simpa only [d49, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19593 (pattern : Twelve) (guard : d1 pattern = 1) : d71 pattern ≤ (16 : Int) + d883 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d71, d883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19570 pattern childGuard
    simpa only [d71, d883, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d71, d883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19592 pattern childGuard
    simpa only [d71, d883, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19594 (pattern : Twelve) (guard : d1 pattern = 1) : d90 pattern ≤ (16 : Int) + d893 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d90, d893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19587 pattern childGuard
    simpa only [d90, d893, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d90, d893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19593 pattern childGuard
    simpa only [d90, d893, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19595 (pattern : Twelve) (guard : d1 pattern = 1) : d795 pattern ≤ (16 : Int) + d899 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d795, d899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19585 pattern childGuard
    simpa only [d795, d899, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d795, d899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19594 pattern childGuard
    simpa only [d795, d899, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19596 (pattern : Twelve) (guard : d1 pattern = 1) : d798 pattern ≤ (16 : Int) + d902 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d798, d902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19574 pattern childGuard
    simpa only [d798, d902, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d798, d902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19595 pattern childGuard
    simpa only [d798, d902, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19597 (pattern : Twelve) (guard : d1 pattern = 1) : d39 pattern ≤ (16 : Int) + d35 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d39, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19449 pattern childGuard
    simpa only [d39, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d39, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19470 pattern childGuard
    simpa only [d39, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19598 (pattern : Twelve) (guard : d1 pattern = 1) : d59 pattern ≤ (16 : Int) + d56 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d59, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19575 pattern childGuard
    simpa only [d59, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d59, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19597 pattern childGuard
    simpa only [d59, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19599 (pattern : Twelve) (guard : d1 pattern = 1) : d89 pattern ≤ (16 : Int) + d892 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d89, d892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19598 pattern childGuard
    simpa only [d89, d892, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d89, d892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19584 pattern childGuard
    simpa only [d89, d892, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
