/- Staged soko4-1 certificate. No result until all kernel checks pass. -/
import NetHack.Sokoban41.Comparisons21
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban41.Diagram
theorem c3520 (pattern : Ten) (guard : d350 pattern = 1) : d0 pattern ≤ (2 : Int) + d10 pattern := by
  change (0 : Int) ≤ (2 : Int) + 10
  decide
theorem c3521 (pattern : Ten) (guard : d350 pattern = 1) : d15 pattern ≤ (2 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3520 pattern childGuard
    simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3293 pattern childGuard
    simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3522 (pattern : Ten) (guard : d350 pattern = 1) : d48 pattern ≤ (2 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3521 pattern childGuard
    simpa only [d48, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3296 pattern childGuard
    simpa only [d48, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3523 (pattern : Ten) (guard : d350 pattern = 1) : d54 pattern ≤ (2 : Int) + d10 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3522 pattern childGuard
    simpa only [d54, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3300 pattern childGuard
    simpa only [d54, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3524 (pattern : Ten) (guard : d0 pattern = 1) : d10 pattern ≤ (2 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3525 (pattern : Ten) (guard : d395 pattern = 1) : d162 pattern ≤ (2 : Int) + d10 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d395, d162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3523 pattern childGuard
    simpa only [d395, d162, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d395, d162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3524 pattern childGuard
    simpa only [d395, d162, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3526 (pattern : Ten) (guard : d350 pattern = 1) : d44 pattern ≤ (2 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3293 pattern childGuard
    simpa only [d44, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3295 pattern childGuard
    simpa only [d44, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3527 (pattern : Ten) (guard : d350 pattern = 1) : d50 pattern ≤ (2 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3526 pattern childGuard
    simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3299 pattern childGuard
    simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3528 (pattern : Ten) (guard : d350 pattern = 1) : d55 pattern ≤ (2 : Int) + d10 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3527 pattern childGuard
    simpa only [d55, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3320 pattern childGuard
    simpa only [d55, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3529 (pattern : Ten) (guard : d395 pattern = 1) : d163 pattern ≤ (2 : Int) + d10 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d395, d163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3528 pattern childGuard
    simpa only [d395, d163, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d395, d163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3524 pattern childGuard
    simpa only [d395, d163, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3530 (pattern : Ten) (guard : d395 pattern = 1) : d166 pattern ≤ (2 : Int) + d10 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d395 pattern = 1 := by simpa only [d166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3525 pattern childGuard
    simpa only [d166, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d395 pattern = 1 := by simpa only [d166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3529 pattern childGuard
    simpa only [d166, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3531 (pattern : Ten) (guard : d395 pattern = 1) : d168 pattern ≤ (2 : Int) + d577 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d395 pattern = 1 := by simpa only [d168, d577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3519 pattern childGuard
    simpa only [d168, d577, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d395 pattern = 1 := by simpa only [d168, d577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3530 pattern childGuard
    simpa only [d168, d577, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3532 (pattern : Ten) (guard : d1 pattern = 1) : d7 pattern ≤ (2 : Int) + d9 pattern := by
  change (7 : Int) ≤ (2 : Int) + 9
  decide
theorem c3533 (pattern : Ten) (guard : d1 pattern = 1) : d38 pattern ≤ (2 : Int) + d39 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d38, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3532 pattern childGuard
    simpa only [d38, d39, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d38, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3361 pattern childGuard
    simpa only [d38, d39, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3534 (pattern : Ten) (guard : d1 pattern = 1) : d40 pattern ≤ (2 : Int) + d41 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d40, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3533 pattern childGuard
    simpa only [d40, d41, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d40, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3361 pattern childGuard
    simpa only [d40, d41, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3535 (pattern : Ten) (guard : d0 pattern = 1) : d40 pattern ≤ (2 : Int) + d41 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3536 (pattern : Ten) (guard : d350 pattern = 1) : d40 pattern ≤ (2 : Int) + d41 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3534 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3535 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3537 (pattern : Ten) (guard : d350 pattern = 1) : d46 pattern ≤ (2 : Int) + d47 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d46, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3536 pattern childGuard
    simpa only [d46, d47, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d46, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1965 pattern childGuard
    simpa only [d46, d47, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3538 (pattern : Ten) (guard : d350 pattern = 1) : d52 pattern ≤ (2 : Int) + d53 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d52, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3537 pattern childGuard
    simpa only [d52, d53, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d52, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1965 pattern childGuard
    simpa only [d52, d53, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3539 (pattern : Ten) (guard : d350 pattern = 1) : d56 pattern ≤ (2 : Int) + d57 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d56, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3538 pattern childGuard
    simpa only [d56, d57, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d56, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1965 pattern childGuard
    simpa only [d56, d57, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3540 (pattern : Ten) (guard : d0 pattern = 1) : d57 pattern ≤ (2 : Int) + d57 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3541 (pattern : Ten) (guard : d395 pattern = 1) : d164 pattern ≤ (2 : Int) + d57 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d395, d164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3539 pattern childGuard
    simpa only [d395, d164, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d395, d164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3540 pattern childGuard
    simpa only [d395, d164, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3542 (pattern : Ten) (guard : d1 pattern = 1) : d38 pattern ≤ (2 : Int) + d10 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3342 pattern childGuard
    simpa only [d38, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3361 pattern childGuard
    simpa only [d38, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3543 (pattern : Ten) (guard : d1 pattern = 1) : d40 pattern ≤ (2 : Int) + d10 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3542 pattern childGuard
    simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3361 pattern childGuard
    simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3544 (pattern : Ten) (guard : d0 pattern = 1) : d40 pattern ≤ (2 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3545 (pattern : Ten) (guard : d350 pattern = 1) : d40 pattern ≤ (2 : Int) + d10 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3543 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3544 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3546 (pattern : Ten) (guard : d350 pattern = 1) : d46 pattern ≤ (2 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3545 pattern childGuard
    simpa only [d46, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1965 pattern childGuard
    simpa only [d46, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3547 (pattern : Ten) (guard : d350 pattern = 1) : d52 pattern ≤ (2 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3546 pattern childGuard
    simpa only [d52, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1965 pattern childGuard
    simpa only [d52, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3548 (pattern : Ten) (guard : d350 pattern = 1) : d56 pattern ≤ (2 : Int) + d10 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3547 pattern childGuard
    simpa only [d56, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1965 pattern childGuard
    simpa only [d56, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3549 (pattern : Ten) (guard : d395 pattern = 1) : d60 pattern ≤ (2 : Int) + d10 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d395, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3548 pattern childGuard
    simpa only [d395, d60, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d395, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3524 pattern childGuard
    simpa only [d395, d60, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3550 (pattern : Ten) (guard : d395 pattern = 1) : d167 pattern ≤ (2 : Int) + d578 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d395 pattern = 1 := by simpa only [d167, d578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3541 pattern childGuard
    simpa only [d167, d578, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d395 pattern = 1 := by simpa only [d167, d578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3549 pattern childGuard
    simpa only [d167, d578, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3551 (pattern : Ten) (guard : d1 pattern = 1) : d39 pattern ≤ (2 : Int) + d10 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1970 pattern childGuard
    simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1971 pattern childGuard
    simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3552 (pattern : Ten) (guard : d1 pattern = 1) : d41 pattern ≤ (2 : Int) + d10 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3551 pattern childGuard
    simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1971 pattern childGuard
    simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3553 (pattern : Ten) (guard : d0 pattern = 1) : d41 pattern ≤ (2 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3554 (pattern : Ten) (guard : d350 pattern = 1) : d41 pattern ≤ (2 : Int) + d10 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3552 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3553 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3555 (pattern : Ten) (guard : d350 pattern = 1) : d47 pattern ≤ (2 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3554 pattern childGuard
    simpa only [d47, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1965 pattern childGuard
    simpa only [d47, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3556 (pattern : Ten) (guard : d350 pattern = 1) : d53 pattern ≤ (2 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3555 pattern childGuard
    simpa only [d53, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1965 pattern childGuard
    simpa only [d53, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3557 (pattern : Ten) (guard : d350 pattern = 1) : d57 pattern ≤ (2 : Int) + d10 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3556 pattern childGuard
    simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1965 pattern childGuard
    simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3558 (pattern : Ten) (guard : d395 pattern = 1) : d61 pattern ≤ (2 : Int) + d10 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d395, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3557 pattern childGuard
    simpa only [d395, d61, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d395, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3524 pattern childGuard
    simpa only [d395, d61, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3559 (pattern : Ten) (guard : d395 pattern = 1) : d63 pattern ≤ (2 : Int) + d10 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d395 pattern = 1 := by simpa only [d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3549 pattern childGuard
    simpa only [d63, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d395 pattern = 1 := by simpa only [d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3558 pattern childGuard
    simpa only [d63, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3560 (pattern : Ten) (guard : d395 pattern = 1) : d169 pattern ≤ (2 : Int) + d579 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d395 pattern = 1 := by simpa only [d169, d579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3550 pattern childGuard
    simpa only [d169, d579, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d395 pattern = 1 := by simpa only [d169, d579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3559 pattern childGuard
    simpa only [d169, d579, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3561 (pattern : Ten) (guard : d395 pattern = 1) : d170 pattern ≤ (2 : Int) + d580 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d395 pattern = 1 := by simpa only [d170, d580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3531 pattern childGuard
    simpa only [d170, d580, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d395 pattern = 1 := by simpa only [d170, d580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3560 pattern childGuard
    simpa only [d170, d580, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3562 (pattern : Ten) (guard : d1 pattern = 1) : d0 pattern ≤ (2 : Int) + d2 pattern := by
  change (0 : Int) ≤ (2 : Int) + 2
  decide
theorem c3563 (pattern : Ten) (guard : d1 pattern = 1) : d1 pattern ≤ (2 : Int) + d3 pattern := by
  change (1 : Int) ≤ (2 : Int) + 3
  decide
theorem c3564 (pattern : Ten) (guard : d1 pattern = 1) : d171 pattern ≤ (2 : Int) + d172 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d171, d172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3562 pattern childGuard
    simpa only [d171, d172, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d171, d172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3563 pattern childGuard
    simpa only [d171, d172, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3565 (pattern : Ten) (guard : d1 pattern = 1) : d0 pattern ≤ (2 : Int) + d3 pattern := by
  change (0 : Int) ≤ (2 : Int) + 3
  decide
theorem c3566 (pattern : Ten) (guard : d1 pattern = 1) : d1 pattern ≤ (2 : Int) + d4 pattern := by
  change (1 : Int) ≤ (2 : Int) + 4
  decide
theorem c3567 (pattern : Ten) (guard : d1 pattern = 1) : d171 pattern ≤ (2 : Int) + d310 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d171, d310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3565 pattern childGuard
    simpa only [d171, d310, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d171, d310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3566 pattern childGuard
    simpa only [d171, d310, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3568 (pattern : Ten) (guard : d1 pattern = 1) : d171 pattern ≤ (2 : Int) + d314 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3564 pattern childGuard
    simpa only [d314, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3567 pattern childGuard
    simpa only [d314, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3569 (pattern : Ten) (guard : d1 pattern = 1) : d2 pattern ≤ (2 : Int) + d4 pattern := by
  change (2 : Int) ≤ (2 : Int) + 4
  decide
theorem c3570 (pattern : Ten) (guard : d1 pattern = 1) : d3 pattern ≤ (2 : Int) + d5 pattern := by
  change (3 : Int) ≤ (2 : Int) + 5
  decide
theorem c3571 (pattern : Ten) (guard : d1 pattern = 1) : d172 pattern ≤ (2 : Int) + d193 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d172, d193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3569 pattern childGuard
    simpa only [d172, d193, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d172, d193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3570 pattern childGuard
    simpa only [d172, d193, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3572 (pattern : Ten) (guard : d1 pattern = 1) : d2 pattern ≤ (2 : Int) + d5 pattern := by
  change (2 : Int) ≤ (2 : Int) + 5
  decide
theorem c3573 (pattern : Ten) (guard : d1 pattern = 1) : d3 pattern ≤ (2 : Int) + d6 pattern := by
  change (3 : Int) ≤ (2 : Int) + 6
  decide
theorem c3574 (pattern : Ten) (guard : d1 pattern = 1) : d172 pattern ≤ (2 : Int) + d311 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d172, d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3572 pattern childGuard
    simpa only [d172, d311, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d172, d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3573 pattern childGuard
    simpa only [d172, d311, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3575 (pattern : Ten) (guard : d1 pattern = 1) : d172 pattern ≤ (2 : Int) + d315 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3571 pattern childGuard
    simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3574 pattern childGuard
    simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3576 (pattern : Ten) (guard : d1 pattern = 1) : d174 pattern ≤ (2 : Int) + d320 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d174, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3568 pattern childGuard
    simpa only [d174, d320, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d174, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3575 pattern childGuard
    simpa only [d174, d320, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3577 (pattern : Ten) (guard : d1 pattern = 1) : d4 pattern ≤ (2 : Int) + d6 pattern := by
  change (4 : Int) ≤ (2 : Int) + 6
  decide
theorem c3578 (pattern : Ten) (guard : d1 pattern = 1) : d5 pattern ≤ (2 : Int) + d7 pattern := by
  change (5 : Int) ≤ (2 : Int) + 7
  decide
theorem c3579 (pattern : Ten) (guard : d1 pattern = 1) : d193 pattern ≤ (2 : Int) + d194 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d193, d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3577 pattern childGuard
    simpa only [d193, d194, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d193, d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3578 pattern childGuard
    simpa only [d193, d194, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3580 (pattern : Ten) (guard : d1 pattern = 1) : d4 pattern ≤ (2 : Int) + d7 pattern := by
  change (4 : Int) ≤ (2 : Int) + 7
  decide
theorem c3581 (pattern : Ten) (guard : d1 pattern = 1) : d5 pattern ≤ (2 : Int) + d8 pattern := by
  change (5 : Int) ≤ (2 : Int) + 8
  decide
theorem c3582 (pattern : Ten) (guard : d1 pattern = 1) : d193 pattern ≤ (2 : Int) + d312 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d193, d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3580 pattern childGuard
    simpa only [d193, d312, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d193, d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3581 pattern childGuard
    simpa only [d193, d312, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3583 (pattern : Ten) (guard : d1 pattern = 1) : d193 pattern ≤ (2 : Int) + d316 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3579 pattern childGuard
    simpa only [d316, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3582 pattern childGuard
    simpa only [d316, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3584 (pattern : Ten) (guard : d1 pattern = 1) : d197 pattern ≤ (2 : Int) + d319 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d197, d319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3583 pattern childGuard
    simpa only [d197, d319, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d197, d319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1971 pattern childGuard
    simpa only [d197, d319, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3585 (pattern : Ten) (guard : d1 pattern = 1) : d202 pattern ≤ (2 : Int) + d323 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d202, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3576 pattern childGuard
    simpa only [d202, d323, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d202, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3584 pattern childGuard
    simpa only [d202, d323, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3586 (pattern : Ten) (guard : d1 pattern = 1) : d6 pattern ≤ (2 : Int) + d8 pattern := by
  change (6 : Int) ≤ (2 : Int) + 8
  decide
theorem c3587 (pattern : Ten) (guard : d1 pattern = 1) : d194 pattern ≤ (2 : Int) + d195 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d194, d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3586 pattern childGuard
    simpa only [d194, d195, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d194, d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3532 pattern childGuard
    simpa only [d194, d195, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3588 (pattern : Ten) (guard : d1 pattern = 1) : d6 pattern ≤ (2 : Int) + d9 pattern := by
  change (6 : Int) ≤ (2 : Int) + 9
  decide
theorem c3589 (pattern : Ten) (guard : d1 pattern = 1) : d194 pattern ≤ (2 : Int) + d11 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d194, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3588 pattern childGuard
    simpa only [d194, d11, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d194, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3342 pattern childGuard
    simpa only [d194, d11, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3590 (pattern : Ten) (guard : d1 pattern = 1) : d194 pattern ≤ (2 : Int) + d196 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3587 pattern childGuard
    simpa only [d196, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3589 pattern childGuard
    simpa only [d196, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3591 (pattern : Ten) (guard : d1 pattern = 1) : d198 pattern ≤ (2 : Int) + d201 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d198, d201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3590 pattern childGuard
    simpa only [d198, d201, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d198, d201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1971 pattern childGuard
    simpa only [d198, d201, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3592 (pattern : Ten) (guard : d1 pattern = 1) : d203 pattern ≤ (2 : Int) + d206 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d203, d206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3591 pattern childGuard
    simpa only [d203, d206, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d203, d206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1971 pattern childGuard
    simpa only [d203, d206, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3593 (pattern : Ten) (guard : d1 pattern = 1) : d207 pattern ≤ (2 : Int) + d325 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d207, d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3585 pattern childGuard
    simpa only [d207, d325, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d207, d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3592 pattern childGuard
    simpa only [d207, d325, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3594 (pattern : Ten) (guard : d0 pattern = 1) : d325 pattern ≤ (2 : Int) + d325 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3595 (pattern : Ten) (guard : d394 pattern = 1) : d344 pattern ≤ (2 : Int) + d325 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d394, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3593 pattern childGuard
    simpa only [d394, d344, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d394, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3594 pattern childGuard
    simpa only [d394, d344, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3596 (pattern : Ten) (guard : d1 pattern = 1) : d0 pattern ≤ (2 : Int) + d4 pattern := by
  change (0 : Int) ≤ (2 : Int) + 4
  decide
theorem c3597 (pattern : Ten) (guard : d1 pattern = 1) : d1 pattern ≤ (2 : Int) + d5 pattern := by
  change (1 : Int) ≤ (2 : Int) + 5
  decide
theorem c3598 (pattern : Ten) (guard : d1 pattern = 1) : d171 pattern ≤ (2 : Int) + d193 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d171, d193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3596 pattern childGuard
    simpa only [d171, d193, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d171, d193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3597 pattern childGuard
    simpa only [d171, d193, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3599 (pattern : Ten) (guard : d1 pattern = 1) : d0 pattern ≤ (2 : Int) + d5 pattern := by
  change (0 : Int) ≤ (2 : Int) + 5
  decide
theorem c3600 (pattern : Ten) (guard : d1 pattern = 1) : d1 pattern ≤ (2 : Int) + d6 pattern := by
  change (1 : Int) ≤ (2 : Int) + 6
  decide
theorem c3601 (pattern : Ten) (guard : d1 pattern = 1) : d171 pattern ≤ (2 : Int) + d311 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d171, d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3599 pattern childGuard
    simpa only [d171, d311, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d171, d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3600 pattern childGuard
    simpa only [d171, d311, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3602 (pattern : Ten) (guard : d1 pattern = 1) : d171 pattern ≤ (2 : Int) + d315 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3598 pattern childGuard
    simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3601 pattern childGuard
    simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3603 (pattern : Ten) (guard : d1 pattern = 1) : d2 pattern ≤ (2 : Int) + d6 pattern := by
  change (2 : Int) ≤ (2 : Int) + 6
  decide
theorem c3604 (pattern : Ten) (guard : d1 pattern = 1) : d3 pattern ≤ (2 : Int) + d7 pattern := by
  change (3 : Int) ≤ (2 : Int) + 7
  decide
theorem c3605 (pattern : Ten) (guard : d1 pattern = 1) : d172 pattern ≤ (2 : Int) + d194 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d172, d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3603 pattern childGuard
    simpa only [d172, d194, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d172, d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3604 pattern childGuard
    simpa only [d172, d194, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3606 (pattern : Ten) (guard : d1 pattern = 1) : d3 pattern ≤ (2 : Int) + d8 pattern := by
  change (3 : Int) ≤ (2 : Int) + 8
  decide
theorem c3607 (pattern : Ten) (guard : d1 pattern = 1) : d172 pattern ≤ (2 : Int) + d312 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d172, d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3310 pattern childGuard
    simpa only [d172, d312, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d172, d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3606 pattern childGuard
    simpa only [d172, d312, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3608 (pattern : Ten) (guard : d1 pattern = 1) : d172 pattern ≤ (2 : Int) + d316 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3605 pattern childGuard
    simpa only [d316, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3607 pattern childGuard
    simpa only [d316, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3609 (pattern : Ten) (guard : d1 pattern = 1) : d174 pattern ≤ (2 : Int) + d341 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d174, d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3602 pattern childGuard
    simpa only [d174, d341, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d174, d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3608 pattern childGuard
    simpa only [d174, d341, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3610 (pattern : Ten) (guard : d1 pattern = 1) : d4 pattern ≤ (2 : Int) + d8 pattern := by
  change (4 : Int) ≤ (2 : Int) + 8
  decide
theorem c3611 (pattern : Ten) (guard : d1 pattern = 1) : d5 pattern ≤ (2 : Int) + d9 pattern := by
  change (5 : Int) ≤ (2 : Int) + 9
  decide
theorem c3612 (pattern : Ten) (guard : d1 pattern = 1) : d193 pattern ≤ (2 : Int) + d195 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d193, d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3610 pattern childGuard
    simpa only [d193, d195, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d193, d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3611 pattern childGuard
    simpa only [d193, d195, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3613 (pattern : Ten) (guard : d1 pattern = 1) : d4 pattern ≤ (2 : Int) + d9 pattern := by
  change (4 : Int) ≤ (2 : Int) + 9
  decide
theorem c3614 (pattern : Ten) (guard : d1 pattern = 1) : d193 pattern ≤ (2 : Int) + d11 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d193, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3613 pattern childGuard
    simpa only [d193, d11, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d193, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3335 pattern childGuard
    simpa only [d193, d11, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3615 (pattern : Ten) (guard : d1 pattern = 1) : d193 pattern ≤ (2 : Int) + d196 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3612 pattern childGuard
    simpa only [d196, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3614 pattern childGuard
    simpa only [d196, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3616 (pattern : Ten) (guard : d1 pattern = 1) : d197 pattern ≤ (2 : Int) + d201 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d197, d201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3615 pattern childGuard
    simpa only [d197, d201, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d197, d201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1971 pattern childGuard
    simpa only [d197, d201, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3617 (pattern : Ten) (guard : d1 pattern = 1) : d202 pattern ≤ (2 : Int) + d342 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d202, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3609 pattern childGuard
    simpa only [d202, d342, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d202, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3616 pattern childGuard
    simpa only [d202, d342, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3618 (pattern : Ten) (guard : d1 pattern = 1) : d198 pattern ≤ (2 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3343 pattern childGuard
    simpa only [d198, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1971 pattern childGuard
    simpa only [d198, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3619 (pattern : Ten) (guard : d1 pattern = 1) : d203 pattern ≤ (2 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3618 pattern childGuard
    simpa only [d203, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1971 pattern childGuard
    simpa only [d203, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3620 (pattern : Ten) (guard : d1 pattern = 1) : d207 pattern ≤ (2 : Int) + d343 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d207, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3617 pattern childGuard
    simpa only [d207, d343, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d207, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3619 pattern childGuard
    simpa only [d207, d343, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3621 (pattern : Ten) (guard : d0 pattern = 1) : d343 pattern ≤ (2 : Int) + d343 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3622 (pattern : Ten) (guard : d394 pattern = 1) : d345 pattern ≤ (2 : Int) + d343 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d394, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3620 pattern childGuard
    simpa only [d394, d345, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d394, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3621 pattern childGuard
    simpa only [d394, d345, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3623 (pattern : Ten) (guard : d394 pattern = 1) : d346 pattern ≤ (2 : Int) + d581 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d394 pattern = 1 := by simpa only [d346, d581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3595 pattern childGuard
    simpa only [d346, d581, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d394 pattern = 1 := by simpa only [d346, d581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3622 pattern childGuard
    simpa only [d346, d581, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3624 (pattern : Ten) (guard : d1 pattern = 1) : d309 pattern ≤ (2 : Int) + d10 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2003 pattern childGuard
    simpa only [d309, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2011 pattern childGuard
    simpa only [d309, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3625 (pattern : Ten) (guard : d1 pattern = 1) : d313 pattern ≤ (2 : Int) + d10 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2004 pattern childGuard
    simpa only [d313, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3624 pattern childGuard
    simpa only [d313, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3626 (pattern : Ten) (guard : d1 pattern = 1) : d310 pattern ≤ (2 : Int) + d10 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2012 pattern childGuard
    simpa only [d310, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3334 pattern childGuard
    simpa only [d310, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3627 (pattern : Ten) (guard : d1 pattern = 1) : d314 pattern ≤ (2 : Int) + d10 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2013 pattern childGuard
    simpa only [d314, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3626 pattern childGuard
    simpa only [d314, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3628 (pattern : Ten) (guard : d1 pattern = 1) : d317 pattern ≤ (2 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3625 pattern childGuard
    simpa only [d317, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3627 pattern childGuard
    simpa only [d317, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3629 (pattern : Ten) (guard : d1 pattern = 1) : d311 pattern ≤ (2 : Int) + d10 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3335 pattern childGuard
    simpa only [d311, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3341 pattern childGuard
    simpa only [d311, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3630 (pattern : Ten) (guard : d1 pattern = 1) : d315 pattern ≤ (2 : Int) + d10 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3336 pattern childGuard
    simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3629 pattern childGuard
    simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3631 (pattern : Ten) (guard : d1 pattern = 1) : d318 pattern ≤ (2 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3630 pattern childGuard
    simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1971 pattern childGuard
    simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3632 (pattern : Ten) (guard : d1 pattern = 1) : d321 pattern ≤ (2 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3628 pattern childGuard
    simpa only [d321, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3631 pattern childGuard
    simpa only [d321, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3633 (pattern : Ten) (guard : d1 pattern = 1) : d312 pattern ≤ (2 : Int) + d10 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3342 pattern childGuard
    simpa only [d312, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3361 pattern childGuard
    simpa only [d312, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3634 (pattern : Ten) (guard : d1 pattern = 1) : d316 pattern ≤ (2 : Int) + d10 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3343 pattern childGuard
    simpa only [d316, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3633 pattern childGuard
    simpa only [d316, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3635 (pattern : Ten) (guard : d1 pattern = 1) : d319 pattern ≤ (2 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3634 pattern childGuard
    simpa only [d319, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1971 pattern childGuard
    simpa only [d319, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3636 (pattern : Ten) (guard : d1 pattern = 1) : d322 pattern ≤ (2 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3635 pattern childGuard
    simpa only [d322, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1971 pattern childGuard
    simpa only [d322, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3637 (pattern : Ten) (guard : d1 pattern = 1) : d324 pattern ≤ (2 : Int) + d10 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3632 pattern childGuard
    simpa only [d324, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3636 pattern childGuard
    simpa only [d324, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3638 (pattern : Ten) (guard : d394 pattern = 1) : d333 pattern ≤ (2 : Int) + d10 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d394, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3637 pattern childGuard
    simpa only [d394, d333, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d394, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3524 pattern childGuard
    simpa only [d394, d333, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3639 (pattern : Ten) (guard : d1 pattern = 1) : d320 pattern ≤ (2 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3627 pattern childGuard
    simpa only [d320, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3630 pattern childGuard
    simpa only [d320, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3640 (pattern : Ten) (guard : d1 pattern = 1) : d323 pattern ≤ (2 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3639 pattern childGuard
    simpa only [d323, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3635 pattern childGuard
    simpa only [d323, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3641 (pattern : Ten) (guard : d1 pattern = 1) : d196 pattern ≤ (2 : Int) + d10 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3362 pattern childGuard
    simpa only [d196, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1972 pattern childGuard
    simpa only [d196, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3642 (pattern : Ten) (guard : d1 pattern = 1) : d201 pattern ≤ (2 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3641 pattern childGuard
    simpa only [d201, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1971 pattern childGuard
    simpa only [d201, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3643 (pattern : Ten) (guard : d1 pattern = 1) : d206 pattern ≤ (2 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3642 pattern childGuard
    simpa only [d206, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1971 pattern childGuard
    simpa only [d206, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3644 (pattern : Ten) (guard : d1 pattern = 1) : d325 pattern ≤ (2 : Int) + d10 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3640 pattern childGuard
    simpa only [d325, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3643 pattern childGuard
    simpa only [d325, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3645 (pattern : Ten) (guard : d394 pattern = 1) : d334 pattern ≤ (2 : Int) + d10 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d394, d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3644 pattern childGuard
    simpa only [d394, d334, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d394, d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3524 pattern childGuard
    simpa only [d394, d334, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3646 (pattern : Ten) (guard : d394 pattern = 1) : d336 pattern ≤ (2 : Int) + d10 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d394 pattern = 1 := by simpa only [d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3638 pattern childGuard
    simpa only [d336, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d394 pattern = 1 := by simpa only [d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3645 pattern childGuard
    simpa only [d336, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3647 (pattern : Ten) (guard : d394 pattern = 1) : d347 pattern ≤ (2 : Int) + d582 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d394 pattern = 1 := by simpa only [d347, d582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3623 pattern childGuard
    simpa only [d347, d582, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d394 pattern = 1 := by simpa only [d347, d582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3646 pattern childGuard
    simpa only [d347, d582, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3648 (pattern : Ten) (guard : d1 pattern = 1) : d200 pattern ≤ (2 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3362 pattern childGuard
    simpa only [d200, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1971 pattern childGuard
    simpa only [d200, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3649 (pattern : Ten) (guard : d1 pattern = 1) : d205 pattern ≤ (2 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3648 pattern childGuard
    simpa only [d205, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1971 pattern childGuard
    simpa only [d205, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3650 (pattern : Ten) (guard : d1 pattern = 1) : d209 pattern ≤ (2 : Int) + d10 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3649 pattern childGuard
    simpa only [d209, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1971 pattern childGuard
    simpa only [d209, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3651 (pattern : Ten) (guard : d394 pattern = 1) : d214 pattern ≤ (2 : Int) + d10 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d394, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3650 pattern childGuard
    simpa only [d394, d214, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d394, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3524 pattern childGuard
    simpa only [d394, d214, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3652 (pattern : Ten) (guard : d1 pattern = 1) : d210 pattern ≤ (2 : Int) + d10 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3643 pattern childGuard
    simpa only [d210, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1971 pattern childGuard
    simpa only [d210, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3653 (pattern : Ten) (guard : d394 pattern = 1) : d335 pattern ≤ (2 : Int) + d10 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d394, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3652 pattern childGuard
    simpa only [d394, d335, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d394, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3524 pattern childGuard
    simpa only [d394, d335, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3654 (pattern : Ten) (guard : d394 pattern = 1) : d10 pattern ≤ (2 : Int) + d10 pattern := by
  omega
theorem c3655 (pattern : Ten) (guard : d394 pattern = 1) : d337 pattern ≤ (2 : Int) + d10 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d394 pattern = 1 := by simpa only [d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3653 pattern childGuard
    simpa only [d337, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d394 pattern = 1 := by simpa only [d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3654 pattern childGuard
    simpa only [d337, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3656 (pattern : Ten) (guard : d394 pattern = 1) : d348 pattern ≤ (2 : Int) + d10 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d394 pattern = 1 := by simpa only [d348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3651 pattern childGuard
    simpa only [d348, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d394 pattern = 1 := by simpa only [d348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3655 pattern childGuard
    simpa only [d348, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3657 (pattern : Ten) (guard : d394 pattern = 1) : d349 pattern ≤ (2 : Int) + d583 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d394 pattern = 1 := by simpa only [d349, d583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3647 pattern childGuard
    simpa only [d349, d583, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d394 pattern = 1 := by simpa only [d349, d583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3656 pattern childGuard
    simpa only [d349, d583, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3658 (pattern : Ten) (guard : d1 pattern = 1) : d0 pattern ≤ (20 : Int) + d0 pattern := by
  omega
theorem c3659 (pattern : Ten) (guard : d1 pattern = 1) : d0 pattern ≤ (20 : Int) + d1 pattern := by
  change (0 : Int) ≤ (20 : Int) + 1
  decide
theorem c3660 (pattern : Ten) (guard : d1 pattern = 1) : d0 pattern ≤ (20 : Int) + d171 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3658 pattern childGuard
    simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3659 pattern childGuard
    simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3661 (pattern : Ten) (guard : d0 pattern = 1) : d0 pattern ≤ (20 : Int) + d171 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3662 (pattern : Ten) (guard : d350 pattern = 1) : d0 pattern ≤ (20 : Int) + d171 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3660 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3661 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3663 (pattern : Ten) (guard : d1 pattern = 1) : d2 pattern ≤ (20 : Int) + d2 pattern := by
  omega
theorem c3664 (pattern : Ten) (guard : d1 pattern = 1) : d2 pattern ≤ (20 : Int) + d3 pattern := by
  change (2 : Int) ≤ (20 : Int) + 3
  decide
theorem c3665 (pattern : Ten) (guard : d1 pattern = 1) : d2 pattern ≤ (20 : Int) + d172 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3663 pattern childGuard
    simpa only [d172, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3664 pattern childGuard
    simpa only [d172, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3666 (pattern : Ten) (guard : d0 pattern = 1) : d2 pattern ≤ (20 : Int) + d172 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3667 (pattern : Ten) (guard : d350 pattern = 1) : d2 pattern ≤ (20 : Int) + d172 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3665 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3666 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3668 (pattern : Ten) (guard : d350 pattern = 1) : d15 pattern ≤ (20 : Int) + d174 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d15, d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3662 pattern childGuard
    simpa only [d15, d174, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d15, d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3667 pattern childGuard
    simpa only [d15, d174, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3669 (pattern : Ten) (guard : d1 pattern = 1) : d4 pattern ≤ (20 : Int) + d4 pattern := by
  omega
theorem c3670 (pattern : Ten) (guard : d1 pattern = 1) : d4 pattern ≤ (20 : Int) + d5 pattern := by
  change (4 : Int) ≤ (20 : Int) + 5
  decide
theorem c3671 (pattern : Ten) (guard : d1 pattern = 1) : d4 pattern ≤ (20 : Int) + d193 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3669 pattern childGuard
    simpa only [d193, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3670 pattern childGuard
    simpa only [d193, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3672 (pattern : Ten) (guard : d0 pattern = 1) : d4 pattern ≤ (20 : Int) + d193 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3673 (pattern : Ten) (guard : d350 pattern = 1) : d4 pattern ≤ (20 : Int) + d193 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3671 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3672 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3674 (pattern : Ten) (guard : d350 pattern = 1) : d10 pattern ≤ (20 : Int) + d10 pattern := by
  omega
theorem c3675 (pattern : Ten) (guard : d350 pattern = 1) : d42 pattern ≤ (20 : Int) + d197 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d42, d197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3673 pattern childGuard
    simpa only [d42, d197, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d42, d197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3674 pattern childGuard
    simpa only [d42, d197, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3676 (pattern : Ten) (guard : d350 pattern = 1) : d48 pattern ≤ (20 : Int) + d202 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d48, d202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3668 pattern childGuard
    simpa only [d48, d202, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d48, d202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3675 pattern childGuard
    simpa only [d48, d202, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3677 (pattern : Ten) (guard : d1 pattern = 1) : d6 pattern ≤ (20 : Int) + d6 pattern := by
  omega
theorem c3678 (pattern : Ten) (guard : d1 pattern = 1) : d6 pattern ≤ (20 : Int) + d7 pattern := by
  change (6 : Int) ≤ (20 : Int) + 7
  decide
theorem c3679 (pattern : Ten) (guard : d1 pattern = 1) : d6 pattern ≤ (20 : Int) + d194 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3677 pattern childGuard
    simpa only [d194, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3678 pattern childGuard
    simpa only [d194, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban41.Diagram
