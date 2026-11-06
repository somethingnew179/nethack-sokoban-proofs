/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons074
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c10500 (pattern : Twelve) (guard : d1 pattern = 1) : d80 pattern ≤ (4 : Int) + d78 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d80, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10496 pattern childGuard
    simpa only [d80, d78, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d80, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10488 pattern childGuard
    simpa only [d80, d78, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10501 (pattern : Twelve) (guard : d1 pattern = 1) : d95 pattern ≤ (4 : Int) + d94 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d95, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10499 pattern childGuard
    simpa only [d95, d94, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d95, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10500 pattern childGuard
    simpa only [d95, d94, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10502 (pattern : Twelve) (guard : d1 pattern = 1) : d38 pattern ≤ (4 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10494 pattern childGuard
    simpa only [d38, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10474 pattern childGuard
    simpa only [d38, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10503 (pattern : Twelve) (guard : d1 pattern = 1) : d39 pattern ≤ (4 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10494 pattern childGuard
    simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10475 pattern childGuard
    simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10504 (pattern : Twelve) (guard : d1 pattern = 1) : d59 pattern ≤ (4 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10502 pattern childGuard
    simpa only [d59, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10503 pattern childGuard
    simpa only [d59, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10505 (pattern : Twelve) (guard : d1 pattern = 1) : d9 pattern ≤ (4 : Int) + d6 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10494 pattern childGuard
    simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10471 pattern childGuard
    simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10506 (pattern : Twelve) (guard : d1 pattern = 1) : d23 pattern ≤ (4 : Int) + d6 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10494 pattern childGuard
    simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10505 pattern childGuard
    simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10507 (pattern : Twelve) (guard : d1 pattern = 1) : d40 pattern ≤ (4 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10506 pattern childGuard
    simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10475 pattern childGuard
    simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10508 (pattern : Twelve) (guard : d1 pattern = 1) : d60 pattern ≤ (4 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10502 pattern childGuard
    simpa only [d60, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10507 pattern childGuard
    simpa only [d60, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10509 (pattern : Twelve) (guard : d1 pattern = 1) : d81 pattern ≤ (4 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10504 pattern childGuard
    simpa only [d81, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10508 pattern childGuard
    simpa only [d81, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10510 (pattern : Twelve) (guard : d1 pattern = 1) : d15 pattern ≤ (4 : Int) + d6 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10474 pattern childGuard
    simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10472 pattern childGuard
    simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10511 (pattern : Twelve) (guard : d1 pattern = 1) : d24 pattern ≤ (4 : Int) + d6 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10474 pattern childGuard
    simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10510 pattern childGuard
    simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10512 (pattern : Twelve) (guard : d1 pattern = 1) : d41 pattern ≤ (4 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10506 pattern childGuard
    simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10511 pattern childGuard
    simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10513 (pattern : Twelve) (guard : d1 pattern = 1) : d16 pattern ≤ (4 : Int) + d6 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10494 pattern childGuard
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10474 pattern childGuard
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10514 (pattern : Twelve) (guard : d1 pattern = 1) : d25 pattern ≤ (4 : Int) + d6 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10513 pattern childGuard
    simpa only [d25, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10473 pattern childGuard
    simpa only [d25, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10515 (pattern : Twelve) (guard : d1 pattern = 1) : d42 pattern ≤ (4 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10514 pattern childGuard
    simpa only [d42, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10475 pattern childGuard
    simpa only [d42, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10516 (pattern : Twelve) (guard : d1 pattern = 1) : d61 pattern ≤ (4 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10512 pattern childGuard
    simpa only [d61, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10515 pattern childGuard
    simpa only [d61, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10517 (pattern : Twelve) (guard : d1 pattern = 1) : d82 pattern ≤ (4 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10504 pattern childGuard
    simpa only [d82, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10516 pattern childGuard
    simpa only [d82, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10518 (pattern : Twelve) (guard : d1 pattern = 1) : d96 pattern ≤ (4 : Int) + d6 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10509 pattern childGuard
    simpa only [d96, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10517 pattern childGuard
    simpa only [d96, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10519 (pattern : Twelve) (guard : d1 pattern = 1) : d104 pattern ≤ (4 : Int) + d105 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d104, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10501 pattern childGuard
    simpa only [d104, d105, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d104, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10518 pattern childGuard
    simpa only [d104, d105, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10520 (pattern : Twelve) (guard : d0 pattern = 1) : d105 pattern ≤ (4 : Int) + d105 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c10521 (pattern : Twelve) (guard : d1835 pattern = 1) : d111 pattern ≤ (4 : Int) + d105 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1835, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10519 pattern childGuard
    simpa only [d1835, d111, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1835, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10520 pattern childGuard
    simpa only [d1835, d111, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10522 (pattern : Twelve) (guard : d1835 pattern = 1) : d114 pattern ≤ (4 : Int) + d1880 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1835 pattern = 1 := by simpa only [d114, d1880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10493 pattern childGuard
    simpa only [d114, d1880, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1835 pattern = 1 := by simpa only [d114, d1880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10521 pattern childGuard
    simpa only [d114, d1880, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10523 (pattern : Twelve) (guard : d1 pattern = 1) : d97 pattern ≤ (4 : Int) + d97 pattern := by
  omega
theorem c10524 (pattern : Twelve) (guard : d1 pattern = 1) : d1 pattern ≤ (4 : Int) + d1 pattern := by
  omega
theorem c10525 (pattern : Twelve) (guard : d1 pattern = 1) : d43 pattern ≤ (4 : Int) + d45 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d43, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10524 pattern childGuard
    simpa only [d43, d45, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d43, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10481 pattern childGuard
    simpa only [d43, d45, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10526 (pattern : Twelve) (guard : d1 pattern = 1) : d62 pattern ≤ (4 : Int) + d65 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d62, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10470 pattern childGuard
    simpa only [d62, d65, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d62, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10525 pattern childGuard
    simpa only [d62, d65, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10527 (pattern : Twelve) (guard : d1 pattern = 1) : d83 pattern ≤ (4 : Int) + d85 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d83, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10479 pattern childGuard
    simpa only [d83, d85, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d83, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10526 pattern childGuard
    simpa only [d83, d85, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10528 (pattern : Twelve) (guard : d1 pattern = 1) : d44 pattern ≤ (4 : Int) + d39 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d44, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10461 pattern childGuard
    simpa only [d44, d39, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d44, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10485 pattern childGuard
    simpa only [d44, d39, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10529 (pattern : Twelve) (guard : d1 pattern = 1) : d63 pattern ≤ (4 : Int) + d66 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d63, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10470 pattern childGuard
    simpa only [d63, d66, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d63, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10528 pattern childGuard
    simpa only [d63, d66, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10530 (pattern : Twelve) (guard : d1 pattern = 1) : d64 pattern ≤ (4 : Int) + d64 pattern := by
  omega
theorem c10531 (pattern : Twelve) (guard : d1 pattern = 1) : d84 pattern ≤ (4 : Int) + d86 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d84, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10529 pattern childGuard
    simpa only [d84, d86, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d84, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10530 pattern childGuard
    simpa only [d84, d86, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10532 (pattern : Twelve) (guard : d1 pattern = 1) : d98 pattern ≤ (4 : Int) + d99 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d98, d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10527 pattern childGuard
    simpa only [d98, d99, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d98, d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10531 pattern childGuard
    simpa only [d98, d99, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10533 (pattern : Twelve) (guard : d1 pattern = 1) : d106 pattern ≤ (4 : Int) + d107 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d106, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10523 pattern childGuard
    simpa only [d106, d107, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d106, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10532 pattern childGuard
    simpa only [d106, d107, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10534 (pattern : Twelve) (guard : d0 pattern = 1) : d107 pattern ≤ (4 : Int) + d107 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c10535 (pattern : Twelve) (guard : d1835 pattern = 1) : d112 pattern ≤ (4 : Int) + d107 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1835, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10533 pattern childGuard
    simpa only [d1835, d112, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1835, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10534 pattern childGuard
    simpa only [d1835, d112, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10536 (pattern : Twelve) (guard : d1 pattern = 1) : d46 pattern ≤ (4 : Int) + d45 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d46, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10524 pattern childGuard
    simpa only [d46, d45, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d46, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10471 pattern childGuard
    simpa only [d46, d45, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10537 (pattern : Twelve) (guard : d1 pattern = 1) : d67 pattern ≤ (4 : Int) + d65 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d67, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10470 pattern childGuard
    simpa only [d67, d65, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d67, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10536 pattern childGuard
    simpa only [d67, d65, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10538 (pattern : Twelve) (guard : d1 pattern = 1) : d87 pattern ≤ (4 : Int) + d85 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d87, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10496 pattern childGuard
    simpa only [d87, d85, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d87, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10537 pattern childGuard
    simpa only [d87, d85, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10539 (pattern : Twelve) (guard : d1 pattern = 1) : d38 pattern ≤ (4 : Int) + d39 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d38, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10461 pattern childGuard
    simpa only [d38, d39, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d38, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10474 pattern childGuard
    simpa only [d38, d39, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10540 (pattern : Twelve) (guard : d1 pattern = 1) : d68 pattern ≤ (4 : Int) + d66 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d68, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10470 pattern childGuard
    simpa only [d68, d66, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d68, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10539 pattern childGuard
    simpa only [d68, d66, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10541 (pattern : Twelve) (guard : d1 pattern = 1) : d88 pattern ≤ (4 : Int) + d86 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d88, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10540 pattern childGuard
    simpa only [d88, d86, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d88, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10530 pattern childGuard
    simpa only [d88, d86, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10542 (pattern : Twelve) (guard : d1 pattern = 1) : d100 pattern ≤ (4 : Int) + d99 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d100, d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10538 pattern childGuard
    simpa only [d100, d99, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d100, d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10541 pattern childGuard
    simpa only [d100, d99, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10543 (pattern : Twelve) (guard : d1 pattern = 1) : d47 pattern ≤ (4 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10471 pattern childGuard
    simpa only [d47, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10475 pattern childGuard
    simpa only [d47, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10544 (pattern : Twelve) (guard : d1 pattern = 1) : d69 pattern ≤ (4 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10502 pattern childGuard
    simpa only [d69, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10543 pattern childGuard
    simpa only [d69, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10545 (pattern : Twelve) (guard : d1 pattern = 1) : d89 pattern ≤ (4 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10504 pattern childGuard
    simpa only [d89, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10544 pattern childGuard
    simpa only [d89, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10546 (pattern : Twelve) (guard : d1 pattern = 1) : d48 pattern ≤ (4 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10474 pattern childGuard
    simpa only [d48, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10475 pattern childGuard
    simpa only [d48, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10547 (pattern : Twelve) (guard : d1 pattern = 1) : d70 pattern ≤ (4 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10502 pattern childGuard
    simpa only [d70, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10546 pattern childGuard
    simpa only [d70, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10548 (pattern : Twelve) (guard : d1 pattern = 1) : d49 pattern ≤ (4 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10511 pattern childGuard
    simpa only [d49, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10475 pattern childGuard
    simpa only [d49, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10549 (pattern : Twelve) (guard : d1 pattern = 1) : d71 pattern ≤ (4 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10512 pattern childGuard
    simpa only [d71, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10548 pattern childGuard
    simpa only [d71, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10550 (pattern : Twelve) (guard : d1 pattern = 1) : d90 pattern ≤ (4 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d90, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10547 pattern childGuard
    simpa only [d90, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d90, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10549 pattern childGuard
    simpa only [d90, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10551 (pattern : Twelve) (guard : d1 pattern = 1) : d101 pattern ≤ (4 : Int) + d6 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10545 pattern childGuard
    simpa only [d101, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10550 pattern childGuard
    simpa only [d101, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10552 (pattern : Twelve) (guard : d1 pattern = 1) : d108 pattern ≤ (4 : Int) + d109 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d108, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10542 pattern childGuard
    simpa only [d108, d109, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d108, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10551 pattern childGuard
    simpa only [d108, d109, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10553 (pattern : Twelve) (guard : d0 pattern = 1) : d109 pattern ≤ (4 : Int) + d109 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c10554 (pattern : Twelve) (guard : d1835 pattern = 1) : d113 pattern ≤ (4 : Int) + d109 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1835, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10552 pattern childGuard
    simpa only [d1835, d113, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1835, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10553 pattern childGuard
    simpa only [d1835, d113, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10555 (pattern : Twelve) (guard : d1835 pattern = 1) : d115 pattern ≤ (4 : Int) + d1881 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1835 pattern = 1 := by simpa only [d115, d1881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10535 pattern childGuard
    simpa only [d115, d1881, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1835 pattern = 1 := by simpa only [d115, d1881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10554 pattern childGuard
    simpa only [d115, d1881, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10556 (pattern : Twelve) (guard : d1835 pattern = 1) : d116 pattern ≤ (4 : Int) + d1882 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1835 pattern = 1 := by simpa only [d116, d1882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10522 pattern childGuard
    simpa only [d116, d1882, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1835 pattern = 1 := by simpa only [d116, d1882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10555 pattern childGuard
    simpa only [d116, d1882, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10557 (pattern : Twelve) (guard : d1835 pattern = 1) : d861 pattern ≤ (4 : Int) + d861 pattern := by
  omega
theorem c10558 (pattern : Twelve) (guard : d1 pattern = 1) : d34 pattern ≤ (4 : Int) + d34 pattern := by
  omega
theorem c10559 (pattern : Twelve) (guard : d1 pattern = 1) : d814 pattern ≤ (4 : Int) + d814 pattern := by
  omega
theorem c10560 (pattern : Twelve) (guard : d1 pattern = 1) : d819 pattern ≤ (4 : Int) + d818 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d819, d818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10559 pattern childGuard
    simpa only [d819, d818, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d819, d818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10471 pattern childGuard
    simpa only [d819, d818, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10561 (pattern : Twelve) (guard : d1 pattern = 1) : d828 pattern ≤ (4 : Int) + d826 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d828, d826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10558 pattern childGuard
    simpa only [d828, d826, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d828, d826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10560 pattern childGuard
    simpa only [d828, d826, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10562 (pattern : Twelve) (guard : d1 pattern = 1) : d842 pattern ≤ (4 : Int) + d840 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d842, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10496 pattern childGuard
    simpa only [d842, d840, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d842, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10561 pattern childGuard
    simpa only [d842, d840, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10563 (pattern : Twelve) (guard : d1 pattern = 1) : d34 pattern ≤ (4 : Int) + d36 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d34, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10459 pattern childGuard
    simpa only [d34, d36, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d34, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10506 pattern childGuard
    simpa only [d34, d36, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10564 (pattern : Twelve) (guard : d1 pattern = 1) : d34 pattern ≤ (4 : Int) + d827 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10558 pattern childGuard
    simpa only [d827, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10563 pattern childGuard
    simpa only [d827, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10565 (pattern : Twelve) (guard : d1 pattern = 1) : d825 pattern ≤ (4 : Int) + d825 pattern := by
  omega
theorem c10566 (pattern : Twelve) (guard : d1 pattern = 1) : d843 pattern ≤ (4 : Int) + d841 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d843, d841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10564 pattern childGuard
    simpa only [d843, d841, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d843, d841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10565 pattern childGuard
    simpa only [d843, d841, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10567 (pattern : Twelve) (guard : d1 pattern = 1) : d855 pattern ≤ (4 : Int) + d854 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d855, d854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10562 pattern childGuard
    simpa only [d855, d854, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d855, d854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10566 pattern childGuard
    simpa only [d855, d854, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10568 (pattern : Twelve) (guard : d1 pattern = 1) : d815 pattern ≤ (4 : Int) + d6 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10505 pattern childGuard
    simpa only [d815, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10471 pattern childGuard
    simpa only [d815, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10569 (pattern : Twelve) (guard : d1 pattern = 1) : d820 pattern ≤ (4 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10568 pattern childGuard
    simpa only [d820, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10475 pattern childGuard
    simpa only [d820, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10570 (pattern : Twelve) (guard : d1 pattern = 1) : d829 pattern ≤ (4 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10512 pattern childGuard
    simpa only [d829, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10569 pattern childGuard
    simpa only [d829, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10571 (pattern : Twelve) (guard : d1 pattern = 1) : d844 pattern ≤ (4 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10504 pattern childGuard
    simpa only [d844, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10570 pattern childGuard
    simpa only [d844, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10572 (pattern : Twelve) (guard : d1 pattern = 1) : d830 pattern ≤ (4 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10512 pattern childGuard
    simpa only [d830, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10507 pattern childGuard
    simpa only [d830, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10573 (pattern : Twelve) (guard : d1 pattern = 1) : d821 pattern ≤ (4 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10514 pattern childGuard
    simpa only [d821, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10481 pattern childGuard
    simpa only [d821, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10574 (pattern : Twelve) (guard : d1 pattern = 1) : d822 pattern ≤ (4 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10481 pattern childGuard
    simpa only [d822, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10475 pattern childGuard
    simpa only [d822, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10575 (pattern : Twelve) (guard : d1 pattern = 1) : d831 pattern ≤ (4 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10573 pattern childGuard
    simpa only [d831, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10574 pattern childGuard
    simpa only [d831, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10576 (pattern : Twelve) (guard : d1 pattern = 1) : d845 pattern ≤ (4 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10572 pattern childGuard
    simpa only [d845, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10575 pattern childGuard
    simpa only [d845, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10577 (pattern : Twelve) (guard : d1 pattern = 1) : d856 pattern ≤ (4 : Int) + d6 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10571 pattern childGuard
    simpa only [d856, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10576 pattern childGuard
    simpa only [d856, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10578 (pattern : Twelve) (guard : d1 pattern = 1) : d862 pattern ≤ (4 : Int) + d863 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d862, d863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10567 pattern childGuard
    simpa only [d862, d863, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d862, d863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10577 pattern childGuard
    simpa only [d862, d863, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10579 (pattern : Twelve) (guard : d0 pattern = 1) : d863 pattern ≤ (4 : Int) + d863 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c10580 (pattern : Twelve) (guard : d1835 pattern = 1) : d867 pattern ≤ (4 : Int) + d863 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1835, d867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10578 pattern childGuard
    simpa only [d1835, d867, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1835, d867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10579 pattern childGuard
    simpa only [d1835, d867, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10581 (pattern : Twelve) (guard : d1835 pattern = 1) : d869 pattern ≤ (4 : Int) + d1883 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1835 pattern = 1 := by simpa only [d869, d1883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10557 pattern childGuard
    simpa only [d869, d1883, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1835 pattern = 1 := by simpa only [d869, d1883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10580 pattern childGuard
    simpa only [d869, d1883, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10582 (pattern : Twelve) (guard : d1835 pattern = 1) : d864 pattern ≤ (4 : Int) + d864 pattern := by
  omega
theorem c10583 (pattern : Twelve) (guard : d1 pattern = 1) : d834 pattern ≤ (4 : Int) + d832 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d834, d832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10558 pattern childGuard
    simpa only [d834, d832, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d834, d832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10536 pattern childGuard
    simpa only [d834, d832, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10584 (pattern : Twelve) (guard : d1 pattern = 1) : d849 pattern ≤ (4 : Int) + d847 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d849, d847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10496 pattern childGuard
    simpa only [d849, d847, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d849, d847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10583 pattern childGuard
    simpa only [d849, d847, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10585 (pattern : Twelve) (guard : d1 pattern = 1) : d835 pattern ≤ (4 : Int) + d833 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d835, d833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10558 pattern childGuard
    simpa only [d835, d833, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d835, d833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10539 pattern childGuard
    simpa only [d835, d833, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10586 (pattern : Twelve) (guard : d1 pattern = 1) : d850 pattern ≤ (4 : Int) + d848 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d850, d848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10585 pattern childGuard
    simpa only [d850, d848, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d850, d848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10565 pattern childGuard
    simpa only [d850, d848, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10587 (pattern : Twelve) (guard : d1 pattern = 1) : d859 pattern ≤ (4 : Int) + d858 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d859, d858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10584 pattern childGuard
    simpa only [d859, d858, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d859, d858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10586 pattern childGuard
    simpa only [d859, d858, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10588 (pattern : Twelve) (guard : d1 pattern = 1) : d836 pattern ≤ (4 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10512 pattern childGuard
    simpa only [d836, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10543 pattern childGuard
    simpa only [d836, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10589 (pattern : Twelve) (guard : d1 pattern = 1) : d851 pattern ≤ (4 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10504 pattern childGuard
    simpa only [d851, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10588 pattern childGuard
    simpa only [d851, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10590 (pattern : Twelve) (guard : d1 pattern = 1) : d837 pattern ≤ (4 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10512 pattern childGuard
    simpa only [d837, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10546 pattern childGuard
    simpa only [d837, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10591 (pattern : Twelve) (guard : d1 pattern = 1) : d852 pattern ≤ (4 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10590 pattern childGuard
    simpa only [d852, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10575 pattern childGuard
    simpa only [d852, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10592 (pattern : Twelve) (guard : d1 pattern = 1) : d860 pattern ≤ (4 : Int) + d6 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10589 pattern childGuard
    simpa only [d860, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10591 pattern childGuard
    simpa only [d860, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10593 (pattern : Twelve) (guard : d1 pattern = 1) : d865 pattern ≤ (4 : Int) + d866 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d865, d866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10587 pattern childGuard
    simpa only [d865, d866, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d865, d866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10592 pattern childGuard
    simpa only [d865, d866, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10594 (pattern : Twelve) (guard : d0 pattern = 1) : d866 pattern ≤ (4 : Int) + d866 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c10595 (pattern : Twelve) (guard : d1835 pattern = 1) : d868 pattern ≤ (4 : Int) + d866 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1835, d868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10593 pattern childGuard
    simpa only [d1835, d868, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1835, d868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10594 pattern childGuard
    simpa only [d1835, d868, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10596 (pattern : Twelve) (guard : d1835 pattern = 1) : d870 pattern ≤ (4 : Int) + d1884 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1835 pattern = 1 := by simpa only [d870, d1884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10582 pattern childGuard
    simpa only [d870, d1884, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1835 pattern = 1 := by simpa only [d870, d1884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10595 pattern childGuard
    simpa only [d870, d1884, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10597 (pattern : Twelve) (guard : d1835 pattern = 1) : d871 pattern ≤ (4 : Int) + d1885 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1835 pattern = 1 := by simpa only [d871, d1885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10581 pattern childGuard
    simpa only [d871, d1885, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1835 pattern = 1 := by simpa only [d871, d1885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10596 pattern childGuard
    simpa only [d871, d1885, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10598 (pattern : Twelve) (guard : d1835 pattern = 1) : d1313 pattern ≤ (4 : Int) + d1313 pattern := by
  omega
theorem c10599 (pattern : Twelve) (guard : d1 pattern = 1) : d1279 pattern ≤ (4 : Int) + d1279 pattern := by
  omega
theorem c10600 (pattern : Twelve) (guard : d1 pattern = 1) : d872 pattern ≤ (4 : Int) + d872 pattern := by
  omega
theorem c10601 (pattern : Twelve) (guard : d1 pattern = 1) : d117 pattern ≤ (4 : Int) + d6 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10471 pattern childGuard
    simpa only [d117, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10474 pattern childGuard
    simpa only [d117, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10602 (pattern : Twelve) (guard : d1 pattern = 1) : d119 pattern ≤ (4 : Int) + d6 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10471 pattern childGuard
    simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10601 pattern childGuard
    simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10603 (pattern : Twelve) (guard : d1 pattern = 1) : d1281 pattern ≤ (4 : Int) + d1280 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1281, d1280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10600 pattern childGuard
    simpa only [d1281, d1280, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1281, d1280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10602 pattern childGuard
    simpa only [d1281, d1280, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10604 (pattern : Twelve) (guard : d1 pattern = 1) : d1287 pattern ≤ (4 : Int) + d1285 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1287, d1285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10599 pattern childGuard
    simpa only [d1287, d1285, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1287, d1285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10603 pattern childGuard
    simpa only [d1287, d1285, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10605 (pattern : Twelve) (guard : d1 pattern = 1) : d1297 pattern ≤ (4 : Int) + d1295 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1297, d1295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10564 pattern childGuard
    simpa only [d1297, d1295, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1297, d1295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10604 pattern childGuard
    simpa only [d1297, d1295, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10606 (pattern : Twelve) (guard : d1 pattern = 1) : d817 pattern ≤ (4 : Int) + d817 pattern := by
  omega
theorem c10607 (pattern : Twelve) (guard : d1 pattern = 1) : d19 pattern ≤ (4 : Int) + d19 pattern := by
  omega
theorem c10608 (pattern : Twelve) (guard : d1 pattern = 1) : d817 pattern ≤ (4 : Int) + d29 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d817, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10607 pattern childGuard
    simpa only [d817, d29, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d817, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10514 pattern childGuard
    simpa only [d817, d29, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10609 (pattern : Twelve) (guard : d1 pattern = 1) : d817 pattern ≤ (4 : Int) + d1286 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10606 pattern childGuard
    simpa only [d1286, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10608 pattern childGuard
    simpa only [d1286, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10610 (pattern : Twelve) (guard : d1 pattern = 1) : d1298 pattern ≤ (4 : Int) + d1296 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1298, d1296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10609 pattern childGuard
    simpa only [d1298, d1296, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1298, d1296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10475 pattern childGuard
    simpa only [d1298, d1296, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10611 (pattern : Twelve) (guard : d1 pattern = 1) : d1307 pattern ≤ (4 : Int) + d1306 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1307, d1306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10605 pattern childGuard
    simpa only [d1307, d1306, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1307, d1306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10610 pattern childGuard
    simpa only [d1307, d1306, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10612 (pattern : Twelve) (guard : d1 pattern = 1) : d1276 pattern ≤ (4 : Int) + d6 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10505 pattern childGuard
    simpa only [d1276, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10601 pattern childGuard
    simpa only [d1276, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10613 (pattern : Twelve) (guard : d1 pattern = 1) : d1277 pattern ≤ (4 : Int) + d6 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10510 pattern childGuard
    simpa only [d1277, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10480 pattern childGuard
    simpa only [d1277, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10614 (pattern : Twelve) (guard : d1 pattern = 1) : d1282 pattern ≤ (4 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10612 pattern childGuard
    simpa only [d1282, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10613 pattern childGuard
    simpa only [d1282, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10615 (pattern : Twelve) (guard : d1 pattern = 1) : d125 pattern ≤ (4 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10602 pattern childGuard
    simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10475 pattern childGuard
    simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10616 (pattern : Twelve) (guard : d1 pattern = 1) : d1288 pattern ≤ (4 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10614 pattern childGuard
    simpa only [d1288, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10615 pattern childGuard
    simpa only [d1288, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10617 (pattern : Twelve) (guard : d1 pattern = 1) : d1299 pattern ≤ (4 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10572 pattern childGuard
    simpa only [d1299, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10616 pattern childGuard
    simpa only [d1299, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10618 (pattern : Twelve) (guard : d1 pattern = 1) : d1289 pattern ≤ (4 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10573 pattern childGuard
    simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10515 pattern childGuard
    simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10619 (pattern : Twelve) (guard : d1 pattern = 1) : d1300 pattern ≤ (4 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10618 pattern childGuard
    simpa only [d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10475 pattern childGuard
    simpa only [d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10620 (pattern : Twelve) (guard : d1 pattern = 1) : d1308 pattern ≤ (4 : Int) + d6 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10617 pattern childGuard
    simpa only [d1308, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10619 pattern childGuard
    simpa only [d1308, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10621 (pattern : Twelve) (guard : d1 pattern = 1) : d1314 pattern ≤ (4 : Int) + d1315 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1314, d1315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10611 pattern childGuard
    simpa only [d1314, d1315, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1314, d1315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10620 pattern childGuard
    simpa only [d1314, d1315, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10622 (pattern : Twelve) (guard : d0 pattern = 1) : d1315 pattern ≤ (4 : Int) + d1315 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c10623 (pattern : Twelve) (guard : d1835 pattern = 1) : d1319 pattern ≤ (4 : Int) + d1315 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1835, d1319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10621 pattern childGuard
    simpa only [d1835, d1319, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1835, d1319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10622 pattern childGuard
    simpa only [d1835, d1319, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10624 (pattern : Twelve) (guard : d1835 pattern = 1) : d1321 pattern ≤ (4 : Int) + d1886 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1835 pattern = 1 := by simpa only [d1321, d1886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10598 pattern childGuard
    simpa only [d1321, d1886, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1835 pattern = 1 := by simpa only [d1321, d1886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10623 pattern childGuard
    simpa only [d1321, d1886, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10625 (pattern : Twelve) (guard : d1835 pattern = 1) : d1316 pattern ≤ (4 : Int) + d1316 pattern := by
  omega
theorem c10626 (pattern : Twelve) (guard : d1 pattern = 1) : d23 pattern ≤ (4 : Int) + d23 pattern := by
  omega
theorem c10627 (pattern : Twelve) (guard : d1 pattern = 1) : d41 pattern ≤ (4 : Int) + d40 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d41, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10626 pattern childGuard
    simpa only [d41, d40, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d41, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10511 pattern childGuard
    simpa only [d41, d40, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10628 (pattern : Twelve) (guard : d1 pattern = 1) : d1291 pattern ≤ (4 : Int) + d1290 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1291, d1290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10606 pattern childGuard
    simpa only [d1291, d1290, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1291, d1290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10627 pattern childGuard
    simpa only [d1291, d1290, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10629 (pattern : Twelve) (guard : d1 pattern = 1) : d1303 pattern ≤ (4 : Int) + d1302 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1303, d1302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10628 pattern childGuard
    simpa only [d1303, d1302, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1303, d1302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10475 pattern childGuard
    simpa only [d1303, d1302, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10630 (pattern : Twelve) (guard : d1 pattern = 1) : d1311 pattern ≤ (4 : Int) + d1310 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1311, d1310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10605 pattern childGuard
    simpa only [d1311, d1310, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1311, d1310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10629 pattern childGuard
    simpa only [d1311, d1310, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10631 (pattern : Twelve) (guard : d1 pattern = 1) : d1292 pattern ≤ (4 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10573 pattern childGuard
    simpa only [d1292, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10548 pattern childGuard
    simpa only [d1292, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10632 (pattern : Twelve) (guard : d1 pattern = 1) : d1304 pattern ≤ (4 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10631 pattern childGuard
    simpa only [d1304, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10475 pattern childGuard
    simpa only [d1304, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10633 (pattern : Twelve) (guard : d1 pattern = 1) : d1312 pattern ≤ (4 : Int) + d6 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10617 pattern childGuard
    simpa only [d1312, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10632 pattern childGuard
    simpa only [d1312, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10634 (pattern : Twelve) (guard : d1 pattern = 1) : d1317 pattern ≤ (4 : Int) + d1318 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1317, d1318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10630 pattern childGuard
    simpa only [d1317, d1318, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1317, d1318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10633 pattern childGuard
    simpa only [d1317, d1318, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10635 (pattern : Twelve) (guard : d0 pattern = 1) : d1318 pattern ≤ (4 : Int) + d1318 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c10636 (pattern : Twelve) (guard : d1835 pattern = 1) : d1320 pattern ≤ (4 : Int) + d1318 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1835, d1320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10634 pattern childGuard
    simpa only [d1835, d1320, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1835, d1320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10635 pattern childGuard
    simpa only [d1835, d1320, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10637 (pattern : Twelve) (guard : d1835 pattern = 1) : d1322 pattern ≤ (4 : Int) + d1887 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1835 pattern = 1 := by simpa only [d1322, d1887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10625 pattern childGuard
    simpa only [d1322, d1887, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1835 pattern = 1 := by simpa only [d1322, d1887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10636 pattern childGuard
    simpa only [d1322, d1887, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10638 (pattern : Twelve) (guard : d1835 pattern = 1) : d1323 pattern ≤ (4 : Int) + d1888 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1835 pattern = 1 := by simpa only [d1323, d1888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10624 pattern childGuard
    simpa only [d1323, d1888, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1835 pattern = 1 := by simpa only [d1323, d1888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10637 pattern childGuard
    simpa only [d1323, d1888, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10639 (pattern : Twelve) (guard : d1835 pattern = 1) : d1660 pattern ≤ (4 : Int) + d1660 pattern := by
  omega
end NetHack.Sokoban21.Diagram
