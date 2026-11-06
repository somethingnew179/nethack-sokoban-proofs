/- Staged soko4-1 certificate. No result until all kernel checks pass. -/
import NetHack.Sokoban41.Comparisons02
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban41.Diagram
theorem c480 (pattern : Ten) (guard : d384 pattern = 1) : d37 pattern ≤ (0 : Int) + d149 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d37, d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c478 pattern childGuard
    simpa only [d37, d149, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d37, d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c479 pattern childGuard
    simpa only [d37, d149, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c481 (pattern : Ten) (guard : d383 pattern = 1) : d173 pattern ≤ (0 : Int) + d173 pattern := by
  omega
theorem c482 (pattern : Ten) (guard : d383 pattern = 1) : d176 pattern ≤ (0 : Int) + d173 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d383 pattern = 1 := by simpa only [d176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c430 pattern childGuard
    simpa only [d176, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d383 pattern = 1 := by simpa only [d176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c481 pattern childGuard
    simpa only [d176, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c483 (pattern : Ten) (guard : d383 pattern = 1) : d177 pattern ≤ (0 : Int) + d177 pattern := by
  omega
theorem c484 (pattern : Ten) (guard : d383 pattern = 1) : d180 pattern ≤ (0 : Int) + d302 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d383 pattern = 1 := by simpa only [d180, d302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c482 pattern childGuard
    simpa only [d180, d302, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d383 pattern = 1 := by simpa only [d180, d302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c483 pattern childGuard
    simpa only [d180, d302, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c485 (pattern : Ten) (guard : d383 pattern = 1) : d181 pattern ≤ (0 : Int) + d181 pattern := by
  omega
theorem c486 (pattern : Ten) (guard : d383 pattern = 1) : d184 pattern ≤ (0 : Int) + d304 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d383 pattern = 1 := by simpa only [d184, d304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c484 pattern childGuard
    simpa only [d184, d304, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d383 pattern = 1 := by simpa only [d184, d304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c485 pattern childGuard
    simpa only [d184, d304, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c487 (pattern : Ten) (guard : d0 pattern = 1) : d172 pattern ≤ (0 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c488 (pattern : Ten) (guard : d383 pattern = 1) : d174 pattern ≤ (0 : Int) + d173 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d383, d174, d173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c291 pattern childGuard
    simpa only [d383, d174, d173, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d383, d174, d173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c487 pattern childGuard
    simpa only [d383, d174, d173, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c489 (pattern : Ten) (guard : d383 pattern = 1) : d175 pattern ≤ (0 : Int) + d175 pattern := by
  omega
theorem c490 (pattern : Ten) (guard : d383 pattern = 1) : d178 pattern ≤ (0 : Int) + d301 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d383 pattern = 1 := by simpa only [d178, d301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c488 pattern childGuard
    simpa only [d178, d301, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d383 pattern = 1 := by simpa only [d178, d301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c489 pattern childGuard
    simpa only [d178, d301, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c491 (pattern : Ten) (guard : d383 pattern = 1) : d179 pattern ≤ (0 : Int) + d179 pattern := by
  omega
theorem c492 (pattern : Ten) (guard : d383 pattern = 1) : d182 pattern ≤ (0 : Int) + d303 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d383 pattern = 1 := by simpa only [d182, d303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c490 pattern childGuard
    simpa only [d182, d303, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d383 pattern = 1 := by simpa only [d182, d303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c491 pattern childGuard
    simpa only [d182, d303, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c493 (pattern : Ten) (guard : d383 pattern = 1) : d185 pattern ≤ (0 : Int) + d305 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d383 pattern = 1 := by simpa only [d185, d305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c492 pattern childGuard
    simpa only [d185, d305, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d383 pattern = 1 := by simpa only [d185, d305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c485 pattern childGuard
    simpa only [d185, d305, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c494 (pattern : Ten) (guard : d383 pattern = 1) : d188 pattern ≤ (0 : Int) + d306 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d383 pattern = 1 := by simpa only [d188, d306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c486 pattern childGuard
    simpa only [d188, d306, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d383 pattern = 1 := by simpa only [d188, d306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c493 pattern childGuard
    simpa only [d188, d306, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c495 (pattern : Ten) (guard : d383 pattern = 1) : d189 pattern ≤ (0 : Int) + d189 pattern := by
  omega
theorem c496 (pattern : Ten) (guard : d383 pattern = 1) : d190 pattern ≤ (0 : Int) + d307 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d383 pattern = 1 := by simpa only [d190, d307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c494 pattern childGuard
    simpa only [d190, d307, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d383 pattern = 1 := by simpa only [d190, d307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c495 pattern childGuard
    simpa only [d190, d307, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c497 (pattern : Ten) (guard : d383 pattern = 1) : d191 pattern ≤ (0 : Int) + d191 pattern := by
  omega
theorem c498 (pattern : Ten) (guard : d383 pattern = 1) : d192 pattern ≤ (0 : Int) + d308 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d383 pattern = 1 := by simpa only [d192, d308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c496 pattern childGuard
    simpa only [d192, d308, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d383 pattern = 1 := by simpa only [d192, d308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c497 pattern childGuard
    simpa only [d192, d308, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c499 (pattern : Ten) (guard : d0 pattern = 1) : d4 pattern ≤ (0 : Int) + d2 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c500 (pattern : Ten) (guard : d384 pattern = 1) : d86 pattern ≤ (0 : Int) + d15 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d384, d86, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c393 pattern childGuard
    simpa only [d384, d86, d15, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d384, d86, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c499 pattern childGuard
    simpa only [d384, d86, d15, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c501 (pattern : Ten) (guard : d0 pattern = 1) : d0 pattern ≤ (0 : Int) + d5 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c502 (pattern : Ten) (guard : d387 pattern = 1) : d87 pattern ≤ (0 : Int) + d108 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d387, d87, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c500 pattern childGuard
    simpa only [d387, d87, d108, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d387, d87, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c501 pattern childGuard
    simpa only [d387, d87, d108, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c503 (pattern : Ten) (guard : d0 pattern = 1) : d0 pattern ≤ (0 : Int) + d2 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c504 (pattern : Ten) (guard : d384 pattern = 1) : d0 pattern ≤ (0 : Int) + d15 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d384, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c393 pattern childGuard
    simpa only [d384, d15, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d384, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c503 pattern childGuard
    simpa only [d384, d15, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c505 (pattern : Ten) (guard : d0 pattern = 1) : d10 pattern ≤ (0 : Int) + d15 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c506 (pattern : Ten) (guard : d387 pattern = 1) : d88 pattern ≤ (0 : Int) + d15 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d387, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c504 pattern childGuard
    simpa only [d387, d88, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d387, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c505 pattern childGuard
    simpa only [d387, d88, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c507 (pattern : Ten) (guard : d387 pattern = 1) : d93 pattern ≤ (0 : Int) + d109 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d387 pattern = 1 := by simpa only [d93, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c502 pattern childGuard
    simpa only [d93, d109, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d387 pattern = 1 := by simpa only [d93, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c506 pattern childGuard
    simpa only [d93, d109, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c508 (pattern : Ten) (guard : d0 pattern = 1) : d11 pattern ≤ (0 : Int) + d15 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c509 (pattern : Ten) (guard : d387 pattern = 1) : d89 pattern ≤ (0 : Int) + d15 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d387, d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c504 pattern childGuard
    simpa only [d387, d89, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d387, d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c508 pattern childGuard
    simpa only [d387, d89, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c510 (pattern : Ten) (guard : d384 pattern = 1) : d11 pattern ≤ (0 : Int) + d14 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d384, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c403 pattern childGuard
    simpa only [d384, d14, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d384, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c462 pattern childGuard
    simpa only [d384, d14, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c511 (pattern : Ten) (guard : d0 pattern = 1) : d10 pattern ≤ (0 : Int) + d14 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c512 (pattern : Ten) (guard : d387 pattern = 1) : d90 pattern ≤ (0 : Int) + d14 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d387, d90, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c510 pattern childGuard
    simpa only [d387, d90, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d387, d90, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c511 pattern childGuard
    simpa only [d387, d90, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c513 (pattern : Ten) (guard : d387 pattern = 1) : d94 pattern ≤ (0 : Int) + d110 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d387 pattern = 1 := by simpa only [d94, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c509 pattern childGuard
    simpa only [d94, d110, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d387 pattern = 1 := by simpa only [d94, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c512 pattern childGuard
    simpa only [d94, d110, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c514 (pattern : Ten) (guard : d387 pattern = 1) : d99 pattern ≤ (0 : Int) + d115 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d387 pattern = 1 := by simpa only [d99, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c507 pattern childGuard
    simpa only [d99, d115, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d387 pattern = 1 := by simpa only [d99, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c513 pattern childGuard
    simpa only [d99, d115, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c515 (pattern : Ten) (guard : d0 pattern = 1) : d2 pattern ≤ (0 : Int) + d15 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c516 (pattern : Ten) (guard : d387 pattern = 1) : d91 pattern ≤ (0 : Int) + d15 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d387, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c504 pattern childGuard
    simpa only [d387, d91, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d387, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c515 pattern childGuard
    simpa only [d387, d91, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c517 (pattern : Ten) (guard : d0 pattern = 1) : d2 pattern ≤ (0 : Int) + d4 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c518 (pattern : Ten) (guard : d384 pattern = 1) : d2 pattern ≤ (0 : Int) + d44 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d384, d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c412 pattern childGuard
    simpa only [d384, d44, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d384, d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c517 pattern childGuard
    simpa only [d384, d44, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c519 (pattern : Ten) (guard : d0 pattern = 1) : d10 pattern ≤ (0 : Int) + d44 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c520 (pattern : Ten) (guard : d387 pattern = 1) : d92 pattern ≤ (0 : Int) + d44 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d387, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c518 pattern childGuard
    simpa only [d387, d92, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d387, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c519 pattern childGuard
    simpa only [d387, d92, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c521 (pattern : Ten) (guard : d387 pattern = 1) : d95 pattern ≤ (0 : Int) + d111 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d387 pattern = 1 := by simpa only [d95, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c516 pattern childGuard
    simpa only [d95, d111, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d387 pattern = 1 := by simpa only [d95, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c520 pattern childGuard
    simpa only [d95, d111, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c522 (pattern : Ten) (guard : d387 pattern = 1) : d100 pattern ≤ (0 : Int) + d116 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d387 pattern = 1 := by simpa only [d100, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c521 pattern childGuard
    simpa only [d100, d116, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d387 pattern = 1 := by simpa only [d100, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c513 pattern childGuard
    simpa only [d100, d116, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c523 (pattern : Ten) (guard : d387 pattern = 1) : d103 pattern ≤ (0 : Int) + d119 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d387 pattern = 1 := by simpa only [d103, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c514 pattern childGuard
    simpa only [d103, d119, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d387 pattern = 1 := by simpa only [d103, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c522 pattern childGuard
    simpa only [d103, d119, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c524 (pattern : Ten) (guard : d387 pattern = 1) : d10 pattern ≤ (0 : Int) + d10 pattern := by
  omega
theorem c525 (pattern : Ten) (guard : d387 pattern = 1) : d96 pattern ≤ (0 : Int) + d112 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d387 pattern = 1 := by simpa only [d96, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c506 pattern childGuard
    simpa only [d96, d112, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d387 pattern = 1 := by simpa only [d96, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c524 pattern childGuard
    simpa only [d96, d112, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c526 (pattern : Ten) (guard : d387 pattern = 1) : d97 pattern ≤ (0 : Int) + d113 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d387 pattern = 1 := by simpa only [d97, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c512 pattern childGuard
    simpa only [d97, d113, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d387 pattern = 1 := by simpa only [d97, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c524 pattern childGuard
    simpa only [d97, d113, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c527 (pattern : Ten) (guard : d387 pattern = 1) : d101 pattern ≤ (0 : Int) + d117 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d387 pattern = 1 := by simpa only [d101, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c525 pattern childGuard
    simpa only [d101, d117, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d387 pattern = 1 := by simpa only [d101, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c526 pattern childGuard
    simpa only [d101, d117, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c528 (pattern : Ten) (guard : d387 pattern = 1) : d98 pattern ≤ (0 : Int) + d114 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d387 pattern = 1 := by simpa only [d98, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c520 pattern childGuard
    simpa only [d98, d114, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d387 pattern = 1 := by simpa only [d98, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c524 pattern childGuard
    simpa only [d98, d114, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c529 (pattern : Ten) (guard : d387 pattern = 1) : d102 pattern ≤ (0 : Int) + d118 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d387 pattern = 1 := by simpa only [d102, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c528 pattern childGuard
    simpa only [d102, d118, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d387 pattern = 1 := by simpa only [d102, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c526 pattern childGuard
    simpa only [d102, d118, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c530 (pattern : Ten) (guard : d387 pattern = 1) : d104 pattern ≤ (0 : Int) + d120 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d387 pattern = 1 := by simpa only [d104, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c527 pattern childGuard
    simpa only [d104, d120, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d387 pattern = 1 := by simpa only [d104, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c529 pattern childGuard
    simpa only [d104, d120, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c531 (pattern : Ten) (guard : d387 pattern = 1) : d105 pattern ≤ (0 : Int) + d121 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d387 pattern = 1 := by simpa only [d105, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c523 pattern childGuard
    simpa only [d105, d121, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d387 pattern = 1 := by simpa only [d105, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c530 pattern childGuard
    simpa only [d105, d121, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c532 (pattern : Ten) (guard : d387 pattern = 1) : d106 pattern ≤ (0 : Int) + d122 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d387 pattern = 1 := by simpa only [d106, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c530 pattern childGuard
    simpa only [d106, d122, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d387 pattern = 1 := by simpa only [d106, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c524 pattern childGuard
    simpa only [d106, d122, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c533 (pattern : Ten) (guard : d387 pattern = 1) : d107 pattern ≤ (0 : Int) + d123 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d387 pattern = 1 := by simpa only [d107, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c531 pattern childGuard
    simpa only [d107, d123, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d387 pattern = 1 := by simpa only [d107, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c532 pattern childGuard
    simpa only [d107, d123, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c534 (pattern : Ten) (guard : d383 pattern = 1) : d173 pattern ≤ (0 : Int) + d174 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d383, d173, d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c291 pattern childGuard
    simpa only [d383, d173, d174, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d383, d173, d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c442 pattern childGuard
    simpa only [d383, d173, d174, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c535 (pattern : Ten) (guard : d388 pattern = 1) : d249 pattern ≤ (0 : Int) + d266 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d383 pattern = 1 := by simpa only [d388, d249, d266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c534 pattern childGuard
    simpa only [d388, d249, d266, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d388, d249, d266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c429 pattern childGuard
    simpa only [d388, d249, d266, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c536 (pattern : Ten) (guard : d0 pattern = 1) : d171 pattern ≤ (0 : Int) + d172 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c537 (pattern : Ten) (guard : d383 pattern = 1) : d171 pattern ≤ (0 : Int) + d174 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d383, d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c291 pattern childGuard
    simpa only [d383, d174, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d383, d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c536 pattern childGuard
    simpa only [d383, d174, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c538 (pattern : Ten) (guard : d0 pattern = 1) : d10 pattern ≤ (0 : Int) + d174 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c539 (pattern : Ten) (guard : d388 pattern = 1) : d250 pattern ≤ (0 : Int) + d174 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d383 pattern = 1 := by simpa only [d388, d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c537 pattern childGuard
    simpa only [d388, d250, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d388, d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c538 pattern childGuard
    simpa only [d388, d250, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c540 (pattern : Ten) (guard : d388 pattern = 1) : d253 pattern ≤ (0 : Int) + d267 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d388 pattern = 1 := by simpa only [d253, d267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c535 pattern childGuard
    simpa only [d253, d267, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d388 pattern = 1 := by simpa only [d253, d267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c539 pattern childGuard
    simpa only [d253, d267, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c541 (pattern : Ten) (guard : d388 pattern = 1) : d10 pattern ≤ (0 : Int) + d10 pattern := by
  omega
theorem c542 (pattern : Ten) (guard : d388 pattern = 1) : d254 pattern ≤ (0 : Int) + d268 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d388 pattern = 1 := by simpa only [d254, d268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c539 pattern childGuard
    simpa only [d254, d268, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d388 pattern = 1 := by simpa only [d254, d268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c541 pattern childGuard
    simpa only [d254, d268, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c543 (pattern : Ten) (guard : d388 pattern = 1) : d257 pattern ≤ (0 : Int) + d271 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d388 pattern = 1 := by simpa only [d257, d271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c540 pattern childGuard
    simpa only [d257, d271, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d388 pattern = 1 := by simpa only [d257, d271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c542 pattern childGuard
    simpa only [d257, d271, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c544 (pattern : Ten) (guard : d0 pattern = 1) : d172 pattern ≤ (0 : Int) + d174 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c545 (pattern : Ten) (guard : d388 pattern = 1) : d251 pattern ≤ (0 : Int) + d174 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d383 pattern = 1 := by simpa only [d388, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c537 pattern childGuard
    simpa only [d388, d251, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d388, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c544 pattern childGuard
    simpa only [d388, d251, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c546 (pattern : Ten) (guard : d0 pattern = 1) : d172 pattern ≤ (0 : Int) + d193 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c547 (pattern : Ten) (guard : d383 pattern = 1) : d172 pattern ≤ (0 : Int) + d199 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d383, d199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c441 pattern childGuard
    simpa only [d383, d199, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d383, d199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c546 pattern childGuard
    simpa only [d383, d199, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c548 (pattern : Ten) (guard : d0 pattern = 1) : d10 pattern ≤ (0 : Int) + d199 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c549 (pattern : Ten) (guard : d388 pattern = 1) : d252 pattern ≤ (0 : Int) + d199 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d383 pattern = 1 := by simpa only [d388, d252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c547 pattern childGuard
    simpa only [d388, d252, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d388, d252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c548 pattern childGuard
    simpa only [d388, d252, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c550 (pattern : Ten) (guard : d388 pattern = 1) : d255 pattern ≤ (0 : Int) + d269 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d388 pattern = 1 := by simpa only [d255, d269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c545 pattern childGuard
    simpa only [d255, d269, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d388 pattern = 1 := by simpa only [d255, d269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c549 pattern childGuard
    simpa only [d255, d269, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c551 (pattern : Ten) (guard : d388 pattern = 1) : d258 pattern ≤ (0 : Int) + d272 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d388 pattern = 1 := by simpa only [d258, d272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c550 pattern childGuard
    simpa only [d258, d272, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d388 pattern = 1 := by simpa only [d258, d272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c542 pattern childGuard
    simpa only [d258, d272, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c552 (pattern : Ten) (guard : d388 pattern = 1) : d261 pattern ≤ (0 : Int) + d275 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d388 pattern = 1 := by simpa only [d261, d275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c543 pattern childGuard
    simpa only [d261, d275, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d388 pattern = 1 := by simpa only [d261, d275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c551 pattern childGuard
    simpa only [d261, d275, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c553 (pattern : Ten) (guard : d388 pattern = 1) : d259 pattern ≤ (0 : Int) + d273 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d388 pattern = 1 := by simpa only [d259, d273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c542 pattern childGuard
    simpa only [d259, d273, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d388 pattern = 1 := by simpa only [d259, d273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c541 pattern childGuard
    simpa only [d259, d273, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c554 (pattern : Ten) (guard : d388 pattern = 1) : d256 pattern ≤ (0 : Int) + d270 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d388 pattern = 1 := by simpa only [d256, d270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c549 pattern childGuard
    simpa only [d256, d270, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d388 pattern = 1 := by simpa only [d256, d270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c541 pattern childGuard
    simpa only [d256, d270, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c555 (pattern : Ten) (guard : d388 pattern = 1) : d260 pattern ≤ (0 : Int) + d274 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d388 pattern = 1 := by simpa only [d260, d274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c554 pattern childGuard
    simpa only [d260, d274, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d388 pattern = 1 := by simpa only [d260, d274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c541 pattern childGuard
    simpa only [d260, d274, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c556 (pattern : Ten) (guard : d388 pattern = 1) : d262 pattern ≤ (0 : Int) + d276 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d388 pattern = 1 := by simpa only [d262, d276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c553 pattern childGuard
    simpa only [d262, d276, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d388 pattern = 1 := by simpa only [d262, d276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c555 pattern childGuard
    simpa only [d262, d276, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c557 (pattern : Ten) (guard : d388 pattern = 1) : d263 pattern ≤ (0 : Int) + d277 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d388 pattern = 1 := by simpa only [d263, d277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c552 pattern childGuard
    simpa only [d263, d277, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d388 pattern = 1 := by simpa only [d263, d277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c556 pattern childGuard
    simpa only [d263, d277, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c558 (pattern : Ten) (guard : d388 pattern = 1) : d264 pattern ≤ (0 : Int) + d278 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d388 pattern = 1 := by simpa only [d264, d278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c556 pattern childGuard
    simpa only [d264, d278, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d388 pattern = 1 := by simpa only [d264, d278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c541 pattern childGuard
    simpa only [d264, d278, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c559 (pattern : Ten) (guard : d388 pattern = 1) : d265 pattern ≤ (0 : Int) + d279 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d388 pattern = 1 := by simpa only [d265, d279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c557 pattern childGuard
    simpa only [d265, d279, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d388 pattern = 1 := by simpa only [d265, d279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c558 pattern childGuard
    simpa only [d265, d279, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c560 (pattern : Ten) (guard : d0 pattern = 1) : d4 pattern ≤ (0 : Int) + d137 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c561 (pattern : Ten) (guard : d384 pattern = 1) : d86 pattern ≤ (0 : Int) + d138 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d384, d86, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c393 pattern childGuard
    simpa only [d384, d86, d138, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d384, d86, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c560 pattern childGuard
    simpa only [d384, d86, d138, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c562 (pattern : Ten) (guard : d384 pattern = 1) : d0 pattern ≤ (0 : Int) + d12 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d384, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c393 pattern childGuard
    simpa only [d384, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d384, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c90 pattern childGuard
    simpa only [d384, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c563 (pattern : Ten) (guard : d384 pattern = 1) : d87 pattern ≤ (0 : Int) + d139 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d87, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c561 pattern childGuard
    simpa only [d87, d139, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d87, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c562 pattern childGuard
    simpa only [d87, d139, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c564 (pattern : Ten) (guard : d384 pattern = 1) : d88 pattern ≤ (0 : Int) + d18 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d88, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c562 pattern childGuard
    simpa only [d88, d18, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d88, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c398 pattern childGuard
    simpa only [d88, d18, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c565 (pattern : Ten) (guard : d384 pattern = 1) : d93 pattern ≤ (0 : Int) + d142 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d93, d142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c563 pattern childGuard
    simpa only [d93, d142, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d93, d142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c564 pattern childGuard
    simpa only [d93, d142, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c566 (pattern : Ten) (guard : d384 pattern = 1) : d89 pattern ≤ (0 : Int) + d140 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d89, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c562 pattern childGuard
    simpa only [d89, d140, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d89, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c510 pattern childGuard
    simpa only [d89, d140, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c567 (pattern : Ten) (guard : d384 pattern = 1) : d90 pattern ≤ (0 : Int) + d20 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d90, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c510 pattern childGuard
    simpa only [d90, d20, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d90, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c398 pattern childGuard
    simpa only [d90, d20, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c568 (pattern : Ten) (guard : d384 pattern = 1) : d94 pattern ≤ (0 : Int) + d143 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d94, d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c566 pattern childGuard
    simpa only [d94, d143, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d94, d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c567 pattern childGuard
    simpa only [d94, d143, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c569 (pattern : Ten) (guard : d384 pattern = 1) : d99 pattern ≤ (0 : Int) + d145 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d99, d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c565 pattern childGuard
    simpa only [d99, d145, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d99, d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c568 pattern childGuard
    simpa only [d99, d145, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c570 (pattern : Ten) (guard : d384 pattern = 1) : d2 pattern ≤ (0 : Int) + d16 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d384, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c412 pattern childGuard
    simpa only [d384, d16, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d384, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c469 pattern childGuard
    simpa only [d384, d16, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c571 (pattern : Ten) (guard : d384 pattern = 1) : d91 pattern ≤ (0 : Int) + d141 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d91, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c562 pattern childGuard
    simpa only [d91, d141, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d91, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c570 pattern childGuard
    simpa only [d91, d141, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c572 (pattern : Ten) (guard : d384 pattern = 1) : d92 pattern ≤ (0 : Int) + d22 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d92, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c570 pattern childGuard
    simpa only [d92, d22, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d92, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c398 pattern childGuard
    simpa only [d92, d22, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c573 (pattern : Ten) (guard : d384 pattern = 1) : d95 pattern ≤ (0 : Int) + d144 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d95, d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c571 pattern childGuard
    simpa only [d95, d144, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d95, d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c572 pattern childGuard
    simpa only [d95, d144, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c574 (pattern : Ten) (guard : d384 pattern = 1) : d100 pattern ≤ (0 : Int) + d146 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d100, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c573 pattern childGuard
    simpa only [d100, d146, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d100, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c568 pattern childGuard
    simpa only [d100, d146, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c575 (pattern : Ten) (guard : d384 pattern = 1) : d103 pattern ≤ (0 : Int) + d147 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d103, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c569 pattern childGuard
    simpa only [d103, d147, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d103, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c574 pattern childGuard
    simpa only [d103, d147, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c576 (pattern : Ten) (guard : d384 pattern = 1) : d96 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d96, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c564 pattern childGuard
    simpa only [d96, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d96, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c398 pattern childGuard
    simpa only [d96, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c577 (pattern : Ten) (guard : d384 pattern = 1) : d97 pattern ≤ (0 : Int) + d27 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d97, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c567 pattern childGuard
    simpa only [d97, d27, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d97, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c398 pattern childGuard
    simpa only [d97, d27, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c578 (pattern : Ten) (guard : d384 pattern = 1) : d101 pattern ≤ (0 : Int) + d31 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d101, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c576 pattern childGuard
    simpa only [d101, d31, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d101, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c577 pattern childGuard
    simpa only [d101, d31, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c579 (pattern : Ten) (guard : d384 pattern = 1) : d98 pattern ≤ (0 : Int) + d28 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d98, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c572 pattern childGuard
    simpa only [d98, d28, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d98, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c398 pattern childGuard
    simpa only [d98, d28, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c580 (pattern : Ten) (guard : d384 pattern = 1) : d102 pattern ≤ (0 : Int) + d32 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d102, d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c579 pattern childGuard
    simpa only [d102, d32, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d102, d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c577 pattern childGuard
    simpa only [d102, d32, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c581 (pattern : Ten) (guard : d384 pattern = 1) : d104 pattern ≤ (0 : Int) + d34 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d104, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c578 pattern childGuard
    simpa only [d104, d34, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d104, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c580 pattern childGuard
    simpa only [d104, d34, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c582 (pattern : Ten) (guard : d384 pattern = 1) : d105 pattern ≤ (0 : Int) + d148 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d105, d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c575 pattern childGuard
    simpa only [d105, d148, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d105, d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c581 pattern childGuard
    simpa only [d105, d148, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c583 (pattern : Ten) (guard : d384 pattern = 1) : d106 pattern ≤ (0 : Int) + d36 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d106, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c581 pattern childGuard
    simpa only [d106, d36, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d106, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c398 pattern childGuard
    simpa only [d106, d36, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c584 (pattern : Ten) (guard : d384 pattern = 1) : d107 pattern ≤ (0 : Int) + d149 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d107, d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c582 pattern childGuard
    simpa only [d107, d149, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d107, d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c583 pattern childGuard
    simpa only [d107, d149, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c585 (pattern : Ten) (guard : d383 pattern = 1) : d249 pattern ≤ (0 : Int) + d173 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d383 pattern = 1 := by simpa only [d249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c481 pattern childGuard
    simpa only [d249, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d383 pattern = 1 := by simpa only [d249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c430 pattern childGuard
    simpa only [d249, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c586 (pattern : Ten) (guard : d383 pattern = 1) : d250 pattern ≤ (0 : Int) + d177 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d383 pattern = 1 := by simpa only [d250, d177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c430 pattern childGuard
    simpa only [d250, d177, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d383 pattern = 1 := by simpa only [d250, d177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c434 pattern childGuard
    simpa only [d250, d177, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c587 (pattern : Ten) (guard : d383 pattern = 1) : d253 pattern ≤ (0 : Int) + d302 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d383 pattern = 1 := by simpa only [d253, d302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c585 pattern childGuard
    simpa only [d253, d302, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d383 pattern = 1 := by simpa only [d253, d302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c586 pattern childGuard
    simpa only [d253, d302, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c588 (pattern : Ten) (guard : d383 pattern = 1) : d254 pattern ≤ (0 : Int) + d181 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d383 pattern = 1 := by simpa only [d254, d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c586 pattern childGuard
    simpa only [d254, d181, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d383 pattern = 1 := by simpa only [d254, d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c434 pattern childGuard
    simpa only [d254, d181, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c589 (pattern : Ten) (guard : d383 pattern = 1) : d257 pattern ≤ (0 : Int) + d304 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d383 pattern = 1 := by simpa only [d257, d304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c587 pattern childGuard
    simpa only [d257, d304, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d383 pattern = 1 := by simpa only [d257, d304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c588 pattern childGuard
    simpa only [d257, d304, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c590 (pattern : Ten) (guard : d383 pattern = 1) : d172 pattern ≤ (0 : Int) + d175 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d383, d175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c441 pattern childGuard
    simpa only [d383, d175, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d383, d175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c487 pattern childGuard
    simpa only [d383, d175, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c591 (pattern : Ten) (guard : d383 pattern = 1) : d251 pattern ≤ (0 : Int) + d301 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d383 pattern = 1 := by simpa only [d251, d301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c430 pattern childGuard
    simpa only [d251, d301, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d383 pattern = 1 := by simpa only [d251, d301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c590 pattern childGuard
    simpa only [d251, d301, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c592 (pattern : Ten) (guard : d383 pattern = 1) : d252 pattern ≤ (0 : Int) + d179 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d383 pattern = 1 := by simpa only [d252, d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c590 pattern childGuard
    simpa only [d252, d179, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d383 pattern = 1 := by simpa only [d252, d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c434 pattern childGuard
    simpa only [d252, d179, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c593 (pattern : Ten) (guard : d383 pattern = 1) : d255 pattern ≤ (0 : Int) + d303 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d383 pattern = 1 := by simpa only [d255, d303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c591 pattern childGuard
    simpa only [d255, d303, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d383 pattern = 1 := by simpa only [d255, d303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c592 pattern childGuard
    simpa only [d255, d303, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c594 (pattern : Ten) (guard : d383 pattern = 1) : d258 pattern ≤ (0 : Int) + d305 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d383 pattern = 1 := by simpa only [d258, d305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c593 pattern childGuard
    simpa only [d258, d305, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d383 pattern = 1 := by simpa only [d258, d305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c588 pattern childGuard
    simpa only [d258, d305, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c595 (pattern : Ten) (guard : d383 pattern = 1) : d261 pattern ≤ (0 : Int) + d306 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d383 pattern = 1 := by simpa only [d261, d306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c589 pattern childGuard
    simpa only [d261, d306, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d383 pattern = 1 := by simpa only [d261, d306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c594 pattern childGuard
    simpa only [d261, d306, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c596 (pattern : Ten) (guard : d383 pattern = 1) : d259 pattern ≤ (0 : Int) + d186 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d383 pattern = 1 := by simpa only [d259, d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c588 pattern childGuard
    simpa only [d259, d186, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d383 pattern = 1 := by simpa only [d259, d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c434 pattern childGuard
    simpa only [d259, d186, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c597 (pattern : Ten) (guard : d383 pattern = 1) : d256 pattern ≤ (0 : Int) + d183 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d383 pattern = 1 := by simpa only [d256, d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c592 pattern childGuard
    simpa only [d256, d183, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d383 pattern = 1 := by simpa only [d256, d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c434 pattern childGuard
    simpa only [d256, d183, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c598 (pattern : Ten) (guard : d383 pattern = 1) : d260 pattern ≤ (0 : Int) + d187 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d383 pattern = 1 := by simpa only [d260, d187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c597 pattern childGuard
    simpa only [d260, d187, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d383 pattern = 1 := by simpa only [d260, d187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c434 pattern childGuard
    simpa only [d260, d187, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c599 (pattern : Ten) (guard : d383 pattern = 1) : d262 pattern ≤ (0 : Int) + d189 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d383 pattern = 1 := by simpa only [d262, d189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c596 pattern childGuard
    simpa only [d262, d189, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d383 pattern = 1 := by simpa only [d262, d189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c598 pattern childGuard
    simpa only [d262, d189, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c600 (pattern : Ten) (guard : d383 pattern = 1) : d263 pattern ≤ (0 : Int) + d307 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d383 pattern = 1 := by simpa only [d263, d307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c595 pattern childGuard
    simpa only [d263, d307, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d383 pattern = 1 := by simpa only [d263, d307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c599 pattern childGuard
    simpa only [d263, d307, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c601 (pattern : Ten) (guard : d383 pattern = 1) : d264 pattern ≤ (0 : Int) + d191 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d383 pattern = 1 := by simpa only [d264, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c599 pattern childGuard
    simpa only [d264, d191, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d383 pattern = 1 := by simpa only [d264, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c434 pattern childGuard
    simpa only [d264, d191, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c602 (pattern : Ten) (guard : d383 pattern = 1) : d265 pattern ≤ (0 : Int) + d308 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d383 pattern = 1 := by simpa only [d265, d308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c600 pattern childGuard
    simpa only [d265, d308, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d383 pattern = 1 := by simpa only [d265, d308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c601 pattern childGuard
    simpa only [d265, d308, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c603 (pattern : Ten) (guard : d0 pattern = 1) : d4 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c604 (pattern : Ten) (guard : d384 pattern = 1) : d86 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d384, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c393 pattern childGuard
    simpa only [d384, d86, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d384, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c603 pattern childGuard
    simpa only [d384, d86, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c605 (pattern : Ten) (guard : d384 pattern = 1) : d87 pattern ≤ (0 : Int) + d17 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d87, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c604 pattern childGuard
    simpa only [d87, d17, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d87, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c562 pattern childGuard
    simpa only [d87, d17, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c606 (pattern : Ten) (guard : d384 pattern = 1) : d93 pattern ≤ (0 : Int) + d23 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d93, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c605 pattern childGuard
    simpa only [d93, d23, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d93, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c564 pattern childGuard
    simpa only [d93, d23, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c607 (pattern : Ten) (guard : d0 pattern = 1) : d0 pattern ≤ (0 : Int) + d11 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c608 (pattern : Ten) (guard : d384 pattern = 1) : d0 pattern ≤ (0 : Int) + d13 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d384, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c393 pattern childGuard
    simpa only [d384, d13, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d384, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c607 pattern childGuard
    simpa only [d384, d13, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c609 (pattern : Ten) (guard : d384 pattern = 1) : d89 pattern ≤ (0 : Int) + d19 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d89, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c608 pattern childGuard
    simpa only [d89, d19, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d89, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c510 pattern childGuard
    simpa only [d89, d19, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c610 (pattern : Ten) (guard : d384 pattern = 1) : d94 pattern ≤ (0 : Int) + d24 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d94, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c609 pattern childGuard
    simpa only [d94, d24, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d94, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c567 pattern childGuard
    simpa only [d94, d24, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c611 (pattern : Ten) (guard : d384 pattern = 1) : d99 pattern ≤ (0 : Int) + d29 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d99, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c606 pattern childGuard
    simpa only [d99, d29, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d99, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c610 pattern childGuard
    simpa only [d99, d29, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c612 (pattern : Ten) (guard : d384 pattern = 1) : d91 pattern ≤ (0 : Int) + d21 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d91, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c504 pattern childGuard
    simpa only [d91, d21, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d91, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c570 pattern childGuard
    simpa only [d91, d21, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c613 (pattern : Ten) (guard : d384 pattern = 1) : d95 pattern ≤ (0 : Int) + d25 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d95, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c612 pattern childGuard
    simpa only [d95, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d95, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c572 pattern childGuard
    simpa only [d95, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c614 (pattern : Ten) (guard : d384 pattern = 1) : d100 pattern ≤ (0 : Int) + d30 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d100, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c613 pattern childGuard
    simpa only [d100, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d100, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c610 pattern childGuard
    simpa only [d100, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c615 (pattern : Ten) (guard : d384 pattern = 1) : d103 pattern ≤ (0 : Int) + d33 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d103, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c611 pattern childGuard
    simpa only [d103, d33, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d103, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c614 pattern childGuard
    simpa only [d103, d33, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c616 (pattern : Ten) (guard : d384 pattern = 1) : d105 pattern ≤ (0 : Int) + d35 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d105, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c615 pattern childGuard
    simpa only [d105, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d105, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c581 pattern childGuard
    simpa only [d105, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c617 (pattern : Ten) (guard : d384 pattern = 1) : d107 pattern ≤ (0 : Int) + d37 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d107, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c616 pattern childGuard
    simpa only [d107, d37, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d107, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c583 pattern childGuard
    simpa only [d107, d37, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c618 (pattern : Ten) (guard : d383 pattern = 1) : d249 pattern ≤ (0 : Int) + d176 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d383 pattern = 1 := by simpa only [d249, d176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c432 pattern childGuard
    simpa only [d249, d176, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d383 pattern = 1 := by simpa only [d249, d176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c430 pattern childGuard
    simpa only [d249, d176, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c619 (pattern : Ten) (guard : d383 pattern = 1) : d253 pattern ≤ (0 : Int) + d180 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d383 pattern = 1 := by simpa only [d253, d180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c618 pattern childGuard
    simpa only [d253, d180, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d383 pattern = 1 := by simpa only [d253, d180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c586 pattern childGuard
    simpa only [d253, d180, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c620 (pattern : Ten) (guard : d383 pattern = 1) : d257 pattern ≤ (0 : Int) + d184 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d383 pattern = 1 := by simpa only [d257, d184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c619 pattern childGuard
    simpa only [d257, d184, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d383 pattern = 1 := by simpa only [d257, d184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c588 pattern childGuard
    simpa only [d257, d184, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c621 (pattern : Ten) (guard : d383 pattern = 1) : d251 pattern ≤ (0 : Int) + d178 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d383 pattern = 1 := by simpa only [d251, d178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c537 pattern childGuard
    simpa only [d251, d178, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d383 pattern = 1 := by simpa only [d251, d178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c590 pattern childGuard
    simpa only [d251, d178, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c622 (pattern : Ten) (guard : d383 pattern = 1) : d255 pattern ≤ (0 : Int) + d182 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d383 pattern = 1 := by simpa only [d255, d182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c621 pattern childGuard
    simpa only [d255, d182, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d383 pattern = 1 := by simpa only [d255, d182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c592 pattern childGuard
    simpa only [d255, d182, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c623 (pattern : Ten) (guard : d383 pattern = 1) : d258 pattern ≤ (0 : Int) + d185 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d383 pattern = 1 := by simpa only [d258, d185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c622 pattern childGuard
    simpa only [d258, d185, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d383 pattern = 1 := by simpa only [d258, d185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c588 pattern childGuard
    simpa only [d258, d185, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c624 (pattern : Ten) (guard : d383 pattern = 1) : d261 pattern ≤ (0 : Int) + d188 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d383 pattern = 1 := by simpa only [d261, d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c620 pattern childGuard
    simpa only [d261, d188, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d383 pattern = 1 := by simpa only [d261, d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c623 pattern childGuard
    simpa only [d261, d188, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c625 (pattern : Ten) (guard : d383 pattern = 1) : d263 pattern ≤ (0 : Int) + d190 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d383 pattern = 1 := by simpa only [d263, d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c624 pattern childGuard
    simpa only [d263, d190, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d383 pattern = 1 := by simpa only [d263, d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c599 pattern childGuard
    simpa only [d263, d190, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c626 (pattern : Ten) (guard : d383 pattern = 1) : d265 pattern ≤ (0 : Int) + d192 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d383 pattern = 1 := by simpa only [d265, d192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c625 pattern childGuard
    simpa only [d265, d192, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d383 pattern = 1 := by simpa only [d265, d192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c601 pattern childGuard
    simpa only [d265, d192, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c627 (pattern : Ten) (guard : d350 pattern = 1) : d15 pattern ≤ (0 : Int) + d15 pattern := by
  omega
theorem c628 (pattern : Ten) (guard : d0 pattern = 1) : d5 pattern ≤ (0 : Int) + d42 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c629 (pattern : Ten) (guard : d389 pattern = 1) : d108 pattern ≤ (0 : Int) + d48 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d389, d108, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c627 pattern childGuard
    simpa only [d389, d108, d48, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d389, d108, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c628 pattern childGuard
    simpa only [d389, d108, d48, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c630 (pattern : Ten) (guard : d0 pattern = 1) : d15 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c631 (pattern : Ten) (guard : d390 pattern = 1) : d109 pattern ≤ (0 : Int) + d124 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d389 pattern = 1 := by simpa only [d390, d109, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c629 pattern childGuard
    simpa only [d390, d109, d124, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d390, d109, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c630 pattern childGuard
    simpa only [d390, d109, d124, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c632 (pattern : Ten) (guard : d0 pattern = 1) : d15 pattern ≤ (0 : Int) + d42 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c633 (pattern : Ten) (guard : d389 pattern = 1) : d15 pattern ≤ (0 : Int) + d48 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d389, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c627 pattern childGuard
    simpa only [d389, d48, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d389, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c632 pattern childGuard
    simpa only [d389, d48, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c634 (pattern : Ten) (guard : d0 pattern = 1) : d14 pattern ≤ (0 : Int) + d48 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c635 (pattern : Ten) (guard : d390 pattern = 1) : d110 pattern ≤ (0 : Int) + d48 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d389 pattern = 1 := by simpa only [d390, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c633 pattern childGuard
    simpa only [d390, d110, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d390, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c634 pattern childGuard
    simpa only [d390, d110, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c636 (pattern : Ten) (guard : d390 pattern = 1) : d115 pattern ≤ (0 : Int) + d125 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d390 pattern = 1 := by simpa only [d115, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c631 pattern childGuard
    simpa only [d115, d125, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d390 pattern = 1 := by simpa only [d115, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c635 pattern childGuard
    simpa only [d115, d125, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c637 (pattern : Ten) (guard : d0 pattern = 1) : d44 pattern ≤ (0 : Int) + d48 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c638 (pattern : Ten) (guard : d390 pattern = 1) : d111 pattern ≤ (0 : Int) + d48 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d389 pattern = 1 := by simpa only [d390, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c633 pattern childGuard
    simpa only [d390, d111, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d390, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c637 pattern childGuard
    simpa only [d390, d111, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c639 (pattern : Ten) (guard : d390 pattern = 1) : d116 pattern ≤ (0 : Int) + d48 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d390 pattern = 1 := by simpa only [d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c638 pattern childGuard
    simpa only [d116, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d390 pattern = 1 := by simpa only [d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c635 pattern childGuard
    simpa only [d116, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban41.Diagram
