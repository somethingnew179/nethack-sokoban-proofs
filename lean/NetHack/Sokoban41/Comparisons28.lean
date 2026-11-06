/- Staged soko4-1 certificate. No result until all kernel checks pass. -/
import NetHack.Sokoban41.Comparisons27
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban41.Diagram
theorem c4480 (pattern : Ten) (guard : d350 pattern = 1) : d52 pattern ≤ (13 : Int) + d205 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d52, d205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4479 pattern childGuard
    simpa only [d52, d205, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d52, d205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4429 pattern childGuard
    simpa only [d52, d205, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4481 (pattern : Ten) (guard : d350 pattern = 1) : d56 pattern ≤ (13 : Int) + d209 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d56, d209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4480 pattern childGuard
    simpa only [d56, d209, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d56, d209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4429 pattern childGuard
    simpa only [d56, d209, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4482 (pattern : Ten) (guard : d1 pattern = 1) : d9 pattern ≤ (13 : Int) + d10 pattern := by
  change (9 : Int) ≤ (13 : Int) + 10
  decide
theorem c4483 (pattern : Ten) (guard : d1 pattern = 1) : d10 pattern ≤ (13 : Int) + d10 pattern := by
  omega
theorem c4484 (pattern : Ten) (guard : d1 pattern = 1) : d39 pattern ≤ (13 : Int) + d10 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4482 pattern childGuard
    simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4483 pattern childGuard
    simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4485 (pattern : Ten) (guard : d1 pattern = 1) : d41 pattern ≤ (13 : Int) + d10 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4484 pattern childGuard
    simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4483 pattern childGuard
    simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4486 (pattern : Ten) (guard : d0 pattern = 1) : d41 pattern ≤ (13 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4487 (pattern : Ten) (guard : d350 pattern = 1) : d41 pattern ≤ (13 : Int) + d10 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4485 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4486 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4488 (pattern : Ten) (guard : d350 pattern = 1) : d47 pattern ≤ (13 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4487 pattern childGuard
    simpa only [d47, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4429 pattern childGuard
    simpa only [d47, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4489 (pattern : Ten) (guard : d350 pattern = 1) : d53 pattern ≤ (13 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4488 pattern childGuard
    simpa only [d53, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4429 pattern childGuard
    simpa only [d53, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4490 (pattern : Ten) (guard : d350 pattern = 1) : d57 pattern ≤ (13 : Int) + d10 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4489 pattern childGuard
    simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4429 pattern childGuard
    simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4491 (pattern : Ten) (guard : d350 pattern = 1) : d164 pattern ≤ (13 : Int) + d214 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d164, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4481 pattern childGuard
    simpa only [d164, d214, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d164, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4490 pattern childGuard
    simpa only [d164, d214, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4492 (pattern : Ten) (guard : d350 pattern = 1) : d60 pattern ≤ (13 : Int) + d214 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d60, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4481 pattern childGuard
    simpa only [d60, d214, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d60, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4429 pattern childGuard
    simpa only [d60, d214, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4493 (pattern : Ten) (guard : d350 pattern = 1) : d167 pattern ≤ (13 : Int) + d214 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4491 pattern childGuard
    simpa only [d167, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4492 pattern childGuard
    simpa only [d167, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4494 (pattern : Ten) (guard : d0 pattern = 1) : d40 pattern ≤ (13 : Int) + d11 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4495 (pattern : Ten) (guard : d350 pattern = 1) : d40 pattern ≤ (13 : Int) + d196 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, d196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4476 pattern childGuard
    simpa only [d350, d196, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, d196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4494 pattern childGuard
    simpa only [d350, d196, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4496 (pattern : Ten) (guard : d350 pattern = 1) : d46 pattern ≤ (13 : Int) + d201 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d46, d201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4495 pattern childGuard
    simpa only [d46, d201, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d46, d201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4429 pattern childGuard
    simpa only [d46, d201, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4497 (pattern : Ten) (guard : d350 pattern = 1) : d52 pattern ≤ (13 : Int) + d206 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d52, d206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4496 pattern childGuard
    simpa only [d52, d206, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d52, d206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4429 pattern childGuard
    simpa only [d52, d206, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4498 (pattern : Ten) (guard : d350 pattern = 1) : d56 pattern ≤ (13 : Int) + d210 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d56, d210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4497 pattern childGuard
    simpa only [d56, d210, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d56, d210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4429 pattern childGuard
    simpa only [d56, d210, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4499 (pattern : Ten) (guard : d350 pattern = 1) : d60 pattern ≤ (13 : Int) + d335 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d60, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4498 pattern childGuard
    simpa only [d60, d335, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d60, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4429 pattern childGuard
    simpa only [d60, d335, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4500 (pattern : Ten) (guard : d350 pattern = 1) : d61 pattern ≤ (13 : Int) + d10 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4490 pattern childGuard
    simpa only [d61, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4429 pattern childGuard
    simpa only [d61, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4501 (pattern : Ten) (guard : d350 pattern = 1) : d63 pattern ≤ (13 : Int) + d337 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d63, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4499 pattern childGuard
    simpa only [d63, d337, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d63, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4500 pattern childGuard
    simpa only [d63, d337, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4502 (pattern : Ten) (guard : d350 pattern = 1) : d169 pattern ≤ (13 : Int) + d348 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d169, d348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4493 pattern childGuard
    simpa only [d169, d348, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d169, d348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4501 pattern childGuard
    simpa only [d169, d348, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4503 (pattern : Ten) (guard : d350 pattern = 1) : d170 pattern ≤ (13 : Int) + d349 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d170, d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4473 pattern childGuard
    simpa only [d170, d349, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d170, d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4502 pattern childGuard
    simpa only [d170, d349, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4504 (pattern : Ten) (guard : d1 pattern = 1) : d0 pattern ≤ (13 : Int) + d10 pattern := by
  change (0 : Int) ≤ (13 : Int) + 10
  decide
theorem c4505 (pattern : Ten) (guard : d1 pattern = 1) : d1 pattern ≤ (13 : Int) + d10 pattern := by
  change (1 : Int) ≤ (13 : Int) + 10
  decide
theorem c4506 (pattern : Ten) (guard : d1 pattern = 1) : d171 pattern ≤ (13 : Int) + d10 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4504 pattern childGuard
    simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4505 pattern childGuard
    simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4507 (pattern : Ten) (guard : d1 pattern = 1) : d2 pattern ≤ (13 : Int) + d10 pattern := by
  change (2 : Int) ≤ (13 : Int) + 10
  decide
theorem c4508 (pattern : Ten) (guard : d1 pattern = 1) : d3 pattern ≤ (13 : Int) + d10 pattern := by
  change (3 : Int) ≤ (13 : Int) + 10
  decide
theorem c4509 (pattern : Ten) (guard : d1 pattern = 1) : d172 pattern ≤ (13 : Int) + d10 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4507 pattern childGuard
    simpa only [d172, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4508 pattern childGuard
    simpa only [d172, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4510 (pattern : Ten) (guard : d1 pattern = 1) : d174 pattern ≤ (13 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4506 pattern childGuard
    simpa only [d174, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4509 pattern childGuard
    simpa only [d174, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4511 (pattern : Ten) (guard : d1 pattern = 1) : d4 pattern ≤ (13 : Int) + d10 pattern := by
  change (4 : Int) ≤ (13 : Int) + 10
  decide
theorem c4512 (pattern : Ten) (guard : d1 pattern = 1) : d5 pattern ≤ (13 : Int) + d10 pattern := by
  change (5 : Int) ≤ (13 : Int) + 10
  decide
theorem c4513 (pattern : Ten) (guard : d1 pattern = 1) : d193 pattern ≤ (13 : Int) + d10 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4511 pattern childGuard
    simpa only [d193, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4512 pattern childGuard
    simpa only [d193, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4514 (pattern : Ten) (guard : d1 pattern = 1) : d197 pattern ≤ (13 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4513 pattern childGuard
    simpa only [d197, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4483 pattern childGuard
    simpa only [d197, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4515 (pattern : Ten) (guard : d1 pattern = 1) : d202 pattern ≤ (13 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4510 pattern childGuard
    simpa only [d202, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4514 pattern childGuard
    simpa only [d202, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4516 (pattern : Ten) (guard : d1 pattern = 1) : d6 pattern ≤ (13 : Int) + d10 pattern := by
  change (6 : Int) ≤ (13 : Int) + 10
  decide
theorem c4517 (pattern : Ten) (guard : d1 pattern = 1) : d7 pattern ≤ (13 : Int) + d10 pattern := by
  change (7 : Int) ≤ (13 : Int) + 10
  decide
theorem c4518 (pattern : Ten) (guard : d1 pattern = 1) : d194 pattern ≤ (13 : Int) + d10 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4516 pattern childGuard
    simpa only [d194, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4517 pattern childGuard
    simpa only [d194, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4519 (pattern : Ten) (guard : d1 pattern = 1) : d198 pattern ≤ (13 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4518 pattern childGuard
    simpa only [d198, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4483 pattern childGuard
    simpa only [d198, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4520 (pattern : Ten) (guard : d1 pattern = 1) : d203 pattern ≤ (13 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4519 pattern childGuard
    simpa only [d203, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4483 pattern childGuard
    simpa only [d203, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4521 (pattern : Ten) (guard : d1 pattern = 1) : d207 pattern ≤ (13 : Int) + d10 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4515 pattern childGuard
    simpa only [d207, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4520 pattern childGuard
    simpa only [d207, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4522 (pattern : Ten) (guard : d1 pattern = 1) : d310 pattern ≤ (13 : Int) + d10 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4508 pattern childGuard
    simpa only [d310, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4511 pattern childGuard
    simpa only [d310, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4523 (pattern : Ten) (guard : d1 pattern = 1) : d314 pattern ≤ (13 : Int) + d10 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4509 pattern childGuard
    simpa only [d314, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4522 pattern childGuard
    simpa only [d314, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4524 (pattern : Ten) (guard : d1 pattern = 1) : d311 pattern ≤ (13 : Int) + d10 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4512 pattern childGuard
    simpa only [d311, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4516 pattern childGuard
    simpa only [d311, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4525 (pattern : Ten) (guard : d1 pattern = 1) : d315 pattern ≤ (13 : Int) + d10 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4513 pattern childGuard
    simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4524 pattern childGuard
    simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4526 (pattern : Ten) (guard : d1 pattern = 1) : d320 pattern ≤ (13 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4523 pattern childGuard
    simpa only [d320, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4525 pattern childGuard
    simpa only [d320, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4527 (pattern : Ten) (guard : d1 pattern = 1) : d8 pattern ≤ (13 : Int) + d10 pattern := by
  change (8 : Int) ≤ (13 : Int) + 10
  decide
theorem c4528 (pattern : Ten) (guard : d1 pattern = 1) : d312 pattern ≤ (13 : Int) + d10 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4517 pattern childGuard
    simpa only [d312, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4527 pattern childGuard
    simpa only [d312, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4529 (pattern : Ten) (guard : d1 pattern = 1) : d316 pattern ≤ (13 : Int) + d10 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4518 pattern childGuard
    simpa only [d316, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4528 pattern childGuard
    simpa only [d316, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4530 (pattern : Ten) (guard : d1 pattern = 1) : d319 pattern ≤ (13 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4529 pattern childGuard
    simpa only [d319, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4483 pattern childGuard
    simpa only [d319, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4531 (pattern : Ten) (guard : d1 pattern = 1) : d323 pattern ≤ (13 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4526 pattern childGuard
    simpa only [d323, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4530 pattern childGuard
    simpa only [d323, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4532 (pattern : Ten) (guard : d1 pattern = 1) : d195 pattern ≤ (13 : Int) + d10 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4527 pattern childGuard
    simpa only [d195, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4482 pattern childGuard
    simpa only [d195, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4533 (pattern : Ten) (guard : d1 pattern = 1) : d11 pattern ≤ (13 : Int) + d10 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4482 pattern childGuard
    simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4483 pattern childGuard
    simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4534 (pattern : Ten) (guard : d1 pattern = 1) : d196 pattern ≤ (13 : Int) + d10 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4532 pattern childGuard
    simpa only [d196, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4533 pattern childGuard
    simpa only [d196, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4535 (pattern : Ten) (guard : d1 pattern = 1) : d201 pattern ≤ (13 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4534 pattern childGuard
    simpa only [d201, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4483 pattern childGuard
    simpa only [d201, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4536 (pattern : Ten) (guard : d1 pattern = 1) : d206 pattern ≤ (13 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4535 pattern childGuard
    simpa only [d206, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4483 pattern childGuard
    simpa only [d206, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4537 (pattern : Ten) (guard : d1 pattern = 1) : d325 pattern ≤ (13 : Int) + d10 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4531 pattern childGuard
    simpa only [d325, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4536 pattern childGuard
    simpa only [d325, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4538 (pattern : Ten) (guard : d1 pattern = 1) : d344 pattern ≤ (13 : Int) + d10 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4521 pattern childGuard
    simpa only [d344, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4537 pattern childGuard
    simpa only [d344, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4539 (pattern : Ten) (guard : d1 pattern = 1) : d341 pattern ≤ (13 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4525 pattern childGuard
    simpa only [d341, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4529 pattern childGuard
    simpa only [d341, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4540 (pattern : Ten) (guard : d1 pattern = 1) : d342 pattern ≤ (13 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4539 pattern childGuard
    simpa only [d342, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4535 pattern childGuard
    simpa only [d342, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4541 (pattern : Ten) (guard : d1 pattern = 1) : d343 pattern ≤ (13 : Int) + d10 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4540 pattern childGuard
    simpa only [d343, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4483 pattern childGuard
    simpa only [d343, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4542 (pattern : Ten) (guard : d1 pattern = 1) : d345 pattern ≤ (13 : Int) + d10 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4521 pattern childGuard
    simpa only [d345, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4541 pattern childGuard
    simpa only [d345, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4543 (pattern : Ten) (guard : d1 pattern = 1) : d346 pattern ≤ (13 : Int) + d10 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4538 pattern childGuard
    simpa only [d346, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4542 pattern childGuard
    simpa only [d346, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4544 (pattern : Ten) (guard : d1 pattern = 1) : d309 pattern ≤ (13 : Int) + d10 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4505 pattern childGuard
    simpa only [d309, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4507 pattern childGuard
    simpa only [d309, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4545 (pattern : Ten) (guard : d1 pattern = 1) : d313 pattern ≤ (13 : Int) + d10 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4506 pattern childGuard
    simpa only [d313, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4544 pattern childGuard
    simpa only [d313, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4546 (pattern : Ten) (guard : d1 pattern = 1) : d317 pattern ≤ (13 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4545 pattern childGuard
    simpa only [d317, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4523 pattern childGuard
    simpa only [d317, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4547 (pattern : Ten) (guard : d1 pattern = 1) : d318 pattern ≤ (13 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4525 pattern childGuard
    simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4483 pattern childGuard
    simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4548 (pattern : Ten) (guard : d1 pattern = 1) : d321 pattern ≤ (13 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4546 pattern childGuard
    simpa only [d321, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4547 pattern childGuard
    simpa only [d321, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4549 (pattern : Ten) (guard : d1 pattern = 1) : d322 pattern ≤ (13 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4530 pattern childGuard
    simpa only [d322, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4483 pattern childGuard
    simpa only [d322, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4550 (pattern : Ten) (guard : d1 pattern = 1) : d324 pattern ≤ (13 : Int) + d10 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4548 pattern childGuard
    simpa only [d324, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4549 pattern childGuard
    simpa only [d324, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4551 (pattern : Ten) (guard : d1 pattern = 1) : d333 pattern ≤ (13 : Int) + d10 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4550 pattern childGuard
    simpa only [d333, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4483 pattern childGuard
    simpa only [d333, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4552 (pattern : Ten) (guard : d1 pattern = 1) : d334 pattern ≤ (13 : Int) + d10 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4537 pattern childGuard
    simpa only [d334, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4483 pattern childGuard
    simpa only [d334, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4553 (pattern : Ten) (guard : d1 pattern = 1) : d336 pattern ≤ (13 : Int) + d10 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4551 pattern childGuard
    simpa only [d336, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4552 pattern childGuard
    simpa only [d336, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4554 (pattern : Ten) (guard : d1 pattern = 1) : d347 pattern ≤ (13 : Int) + d10 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4543 pattern childGuard
    simpa only [d347, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4553 pattern childGuard
    simpa only [d347, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4555 (pattern : Ten) (guard : d1 pattern = 1) : d200 pattern ≤ (13 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4532 pattern childGuard
    simpa only [d200, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4483 pattern childGuard
    simpa only [d200, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4556 (pattern : Ten) (guard : d1 pattern = 1) : d205 pattern ≤ (13 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4555 pattern childGuard
    simpa only [d205, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4483 pattern childGuard
    simpa only [d205, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4557 (pattern : Ten) (guard : d1 pattern = 1) : d209 pattern ≤ (13 : Int) + d10 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4556 pattern childGuard
    simpa only [d209, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4483 pattern childGuard
    simpa only [d209, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4558 (pattern : Ten) (guard : d1 pattern = 1) : d214 pattern ≤ (13 : Int) + d10 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4557 pattern childGuard
    simpa only [d214, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4483 pattern childGuard
    simpa only [d214, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4559 (pattern : Ten) (guard : d1 pattern = 1) : d210 pattern ≤ (13 : Int) + d10 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4536 pattern childGuard
    simpa only [d210, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4483 pattern childGuard
    simpa only [d210, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4560 (pattern : Ten) (guard : d1 pattern = 1) : d335 pattern ≤ (13 : Int) + d10 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4559 pattern childGuard
    simpa only [d335, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4483 pattern childGuard
    simpa only [d335, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4561 (pattern : Ten) (guard : d1 pattern = 1) : d337 pattern ≤ (13 : Int) + d10 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4560 pattern childGuard
    simpa only [d337, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4483 pattern childGuard
    simpa only [d337, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4562 (pattern : Ten) (guard : d1 pattern = 1) : d348 pattern ≤ (13 : Int) + d10 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4558 pattern childGuard
    simpa only [d348, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4561 pattern childGuard
    simpa only [d348, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4563 (pattern : Ten) (guard : d1 pattern = 1) : d349 pattern ≤ (13 : Int) + d10 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4554 pattern childGuard
    simpa only [d349, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4562 pattern childGuard
    simpa only [d349, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4564 (pattern : Ten) (guard : d606 pattern = 1) : d0 pattern ≤ (0 : Int) + d0 pattern := by
  omega
theorem c4565 (pattern : Ten) (guard : d607 pattern = 1) : d17 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d606 pattern = 1 := by simpa only [d607, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4564 pattern childGuard
    simpa only [d607, d17, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d607, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2784 pattern childGuard
    simpa only [d607, d17, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4566 (pattern : Ten) (guard : d0 pattern = 1) : d18 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4567 (pattern : Ten) (guard : d608 pattern = 1) : d23 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d607 pattern = 1 := by simpa only [d608, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4565 pattern childGuard
    simpa only [d608, d23, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d608, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4566 pattern childGuard
    simpa only [d608, d23, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4568 (pattern : Ten) (guard : d0 pattern = 1) : d24 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4569 (pattern : Ten) (guard : d609 pattern = 1) : d29 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d608 pattern = 1 := by simpa only [d609, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4567 pattern childGuard
    simpa only [d609, d29, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d609, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4568 pattern childGuard
    simpa only [d609, d29, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4570 (pattern : Ten) (guard : d0 pattern = 1) : d30 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4571 (pattern : Ten) (guard : d610 pattern = 1) : d33 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d609 pattern = 1 := by simpa only [d610, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4569 pattern childGuard
    simpa only [d610, d33, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d610, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4570 pattern childGuard
    simpa only [d610, d33, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4572 (pattern : Ten) (guard : d0 pattern = 1) : d34 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4573 (pattern : Ten) (guard : d611 pattern = 1) : d35 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d610 pattern = 1 := by simpa only [d611, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4571 pattern childGuard
    simpa only [d611, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d611, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4572 pattern childGuard
    simpa only [d611, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4574 (pattern : Ten) (guard : d0 pattern = 1) : d36 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4575 (pattern : Ten) (guard : d612 pattern = 1) : d37 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d611 pattern = 1 := by simpa only [d612, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4573 pattern childGuard
    simpa only [d612, d37, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d612, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4574 pattern childGuard
    simpa only [d612, d37, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4576 (pattern : Ten) (guard : d606 pattern = 1) : d15 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d359 pattern = 1 := by simpa only [d606, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c157 pattern childGuard
    simpa only [d606, d15, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d606, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c410 pattern childGuard
    simpa only [d606, d15, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4577 (pattern : Ten) (guard : d0 pattern = 1) : d42 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4578 (pattern : Ten) (guard : d607 pattern = 1) : d48 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d606 pattern = 1 := by simpa only [d607, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4576 pattern childGuard
    simpa only [d607, d48, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d607, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4577 pattern childGuard
    simpa only [d607, d48, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4579 (pattern : Ten) (guard : d0 pattern = 1) : d49 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4580 (pattern : Ten) (guard : d608 pattern = 1) : d54 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d607 pattern = 1 := by simpa only [d608, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4578 pattern childGuard
    simpa only [d608, d54, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d608, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4579 pattern childGuard
    simpa only [d608, d54, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4581 (pattern : Ten) (guard : d0 pattern = 1) : d54 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4582 (pattern : Ten) (guard : d609 pattern = 1) : d54 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d608 pattern = 1 := by simpa only [d609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4580 pattern childGuard
    simpa only [d609, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4581 pattern childGuard
    simpa only [d609, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4583 (pattern : Ten) (guard : d610 pattern = 1) : d54 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d609 pattern = 1 := by simpa only [d610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4582 pattern childGuard
    simpa only [d610, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4581 pattern childGuard
    simpa only [d610, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4584 (pattern : Ten) (guard : d0 pattern = 1) : d62 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4585 (pattern : Ten) (guard : d611 pattern = 1) : d64 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d610 pattern = 1 := by simpa only [d611, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4583 pattern childGuard
    simpa only [d611, d64, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d611, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4584 pattern childGuard
    simpa only [d611, d64, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4586 (pattern : Ten) (guard : d0 pattern = 1) : d65 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4587 (pattern : Ten) (guard : d612 pattern = 1) : d66 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d611 pattern = 1 := by simpa only [d612, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4585 pattern childGuard
    simpa only [d612, d66, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d612, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4586 pattern childGuard
    simpa only [d612, d66, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4588 (pattern : Ten) (guard : d0 pattern = 1) : d71 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4589 (pattern : Ten) (guard : d609 pattern = 1) : d73 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d608 pattern = 1 := by simpa only [d609, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4567 pattern childGuard
    simpa only [d609, d73, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d609, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4588 pattern childGuard
    simpa only [d609, d73, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4590 (pattern : Ten) (guard : d0 pattern = 1) : d74 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4591 (pattern : Ten) (guard : d610 pattern = 1) : d77 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d609 pattern = 1 := by simpa only [d610, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4589 pattern childGuard
    simpa only [d610, d77, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d610, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4590 pattern childGuard
    simpa only [d610, d77, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4592 (pattern : Ten) (guard : d0 pattern = 1) : d78 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4593 (pattern : Ten) (guard : d611 pattern = 1) : d79 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d610 pattern = 1 := by simpa only [d611, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4591 pattern childGuard
    simpa only [d611, d79, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d611, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4592 pattern childGuard
    simpa only [d611, d79, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4594 (pattern : Ten) (guard : d0 pattern = 1) : d80 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4595 (pattern : Ten) (guard : d612 pattern = 1) : d81 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d611 pattern = 1 := by simpa only [d612, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4593 pattern childGuard
    simpa only [d612, d81, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d612, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4594 pattern childGuard
    simpa only [d612, d81, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4596 (pattern : Ten) (guard : d0 pattern = 1) : d7 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4597 (pattern : Ten) (guard : d610 pattern = 1) : d82 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d609 pattern = 1 := by simpa only [d610, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4582 pattern childGuard
    simpa only [d610, d82, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d610, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4596 pattern childGuard
    simpa only [d610, d82, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4598 (pattern : Ten) (guard : d0 pattern = 1) : d58 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4599 (pattern : Ten) (guard : d611 pattern = 1) : d83 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d610 pattern = 1 := by simpa only [d611, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4597 pattern childGuard
    simpa only [d611, d83, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d611, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4598 pattern childGuard
    simpa only [d611, d83, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4600 (pattern : Ten) (guard : d0 pattern = 1) : d84 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4601 (pattern : Ten) (guard : d612 pattern = 1) : d85 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d611 pattern = 1 := by simpa only [d612, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4599 pattern childGuard
    simpa only [d612, d85, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d612, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4600 pattern childGuard
    simpa only [d612, d85, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4602 (pattern : Ten) (guard : d606 pattern = 1) : d86 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d359 pattern = 1 := by simpa only [d606, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c157 pattern childGuard
    simpa only [d606, d86, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d606, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c603 pattern childGuard
    simpa only [d606, d86, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4603 (pattern : Ten) (guard : d0 pattern = 1) : d0 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4604 (pattern : Ten) (guard : d607 pattern = 1) : d87 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d606 pattern = 1 := by simpa only [d607, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4602 pattern childGuard
    simpa only [d607, d87, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d607, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4603 pattern childGuard
    simpa only [d607, d87, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4605 (pattern : Ten) (guard : d0 pattern = 1) : d88 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4606 (pattern : Ten) (guard : d608 pattern = 1) : d93 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d607 pattern = 1 := by simpa only [d608, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4604 pattern childGuard
    simpa only [d608, d93, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d608, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4605 pattern childGuard
    simpa only [d608, d93, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4607 (pattern : Ten) (guard : d0 pattern = 1) : d94 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4608 (pattern : Ten) (guard : d609 pattern = 1) : d99 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d608 pattern = 1 := by simpa only [d609, d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4606 pattern childGuard
    simpa only [d609, d99, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d609, d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4607 pattern childGuard
    simpa only [d609, d99, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4609 (pattern : Ten) (guard : d0 pattern = 1) : d100 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4610 (pattern : Ten) (guard : d610 pattern = 1) : d103 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d609 pattern = 1 := by simpa only [d610, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4608 pattern childGuard
    simpa only [d610, d103, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d610, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4609 pattern childGuard
    simpa only [d610, d103, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4611 (pattern : Ten) (guard : d0 pattern = 1) : d104 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4612 (pattern : Ten) (guard : d611 pattern = 1) : d105 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d610 pattern = 1 := by simpa only [d611, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4610 pattern childGuard
    simpa only [d611, d105, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d611, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4611 pattern childGuard
    simpa only [d611, d105, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4613 (pattern : Ten) (guard : d0 pattern = 1) : d106 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4614 (pattern : Ten) (guard : d612 pattern = 1) : d107 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d611 pattern = 1 := by simpa only [d612, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4612 pattern childGuard
    simpa only [d612, d107, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d612, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4613 pattern childGuard
    simpa only [d612, d107, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4615 (pattern : Ten) (guard : d607 pattern = 1) : d108 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d606 pattern = 1 := by simpa only [d607, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4576 pattern childGuard
    simpa only [d607, d108, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d607, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c686 pattern childGuard
    simpa only [d607, d108, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4616 (pattern : Ten) (guard : d0 pattern = 1) : d15 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4617 (pattern : Ten) (guard : d608 pattern = 1) : d109 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d607 pattern = 1 := by simpa only [d608, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4615 pattern childGuard
    simpa only [d608, d109, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d608, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4616 pattern childGuard
    simpa only [d608, d109, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4618 (pattern : Ten) (guard : d0 pattern = 1) : d110 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4619 (pattern : Ten) (guard : d609 pattern = 1) : d115 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d608 pattern = 1 := by simpa only [d609, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4617 pattern childGuard
    simpa only [d609, d115, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d609, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4618 pattern childGuard
    simpa only [d609, d115, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4620 (pattern : Ten) (guard : d0 pattern = 1) : d116 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4621 (pattern : Ten) (guard : d610 pattern = 1) : d119 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d609 pattern = 1 := by simpa only [d610, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4619 pattern childGuard
    simpa only [d610, d119, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d610, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4620 pattern childGuard
    simpa only [d610, d119, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4622 (pattern : Ten) (guard : d0 pattern = 1) : d120 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4623 (pattern : Ten) (guard : d611 pattern = 1) : d121 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d610 pattern = 1 := by simpa only [d611, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4621 pattern childGuard
    simpa only [d611, d121, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d611, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4622 pattern childGuard
    simpa only [d611, d121, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4624 (pattern : Ten) (guard : d0 pattern = 1) : d122 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4625 (pattern : Ten) (guard : d612 pattern = 1) : d123 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d611 pattern = 1 := by simpa only [d612, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4623 pattern childGuard
    simpa only [d612, d123, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d612, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4624 pattern childGuard
    simpa only [d612, d123, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4626 (pattern : Ten) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4627 (pattern : Ten) (guard : d608 pattern = 1) : d124 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d607 pattern = 1 := by simpa only [d608, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4578 pattern childGuard
    simpa only [d608, d124, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d608, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4626 pattern childGuard
    simpa only [d608, d124, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4628 (pattern : Ten) (guard : d0 pattern = 1) : d48 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4629 (pattern : Ten) (guard : d609 pattern = 1) : d125 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d608 pattern = 1 := by simpa only [d609, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4627 pattern childGuard
    simpa only [d609, d125, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d609, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4628 pattern childGuard
    simpa only [d609, d125, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4630 (pattern : Ten) (guard : d610 pattern = 1) : d128 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d609 pattern = 1 := by simpa only [d610, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4629 pattern childGuard
    simpa only [d610, d128, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d610, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4628 pattern childGuard
    simpa only [d610, d128, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4631 (pattern : Ten) (guard : d0 pattern = 1) : d129 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4632 (pattern : Ten) (guard : d611 pattern = 1) : d130 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d610 pattern = 1 := by simpa only [d611, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4630 pattern childGuard
    simpa only [d611, d130, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d611, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4631 pattern childGuard
    simpa only [d611, d130, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4633 (pattern : Ten) (guard : d0 pattern = 1) : d131 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4634 (pattern : Ten) (guard : d612 pattern = 1) : d132 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d611 pattern = 1 := by simpa only [d612, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4632 pattern childGuard
    simpa only [d612, d132, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d612, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4633 pattern childGuard
    simpa only [d612, d132, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4635 (pattern : Ten) (guard : d612 pattern = 1) : d133 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d611 pattern = 1 := by simpa only [d612, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4585 pattern childGuard
    simpa only [d612, d133, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d612, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4596 pattern childGuard
    simpa only [d612, d133, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4636 (pattern : Ten) (guard : d0 pattern = 1) : d8 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4637 (pattern : Ten) (guard : d611 pattern = 1) : d134 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d610 pattern = 1 := by simpa only [d611, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4583 pattern childGuard
    simpa only [d611, d134, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d611, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4636 pattern childGuard
    simpa only [d611, d134, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4638 (pattern : Ten) (guard : d0 pattern = 1) : d56 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4639 (pattern : Ten) (guard : d612 pattern = 1) : d135 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d611 pattern = 1 := by simpa only [d612, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4637 pattern childGuard
    simpa only [d612, d135, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d612, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4638 pattern childGuard
    simpa only [d612, d135, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban41.Diagram
