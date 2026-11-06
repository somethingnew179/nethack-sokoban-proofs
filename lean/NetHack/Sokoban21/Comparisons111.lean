/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons110
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c15540 (pattern : Twelve) (guard : d1 pattern = 1) : d832 pattern ≤ (1 : Int) + d56 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d832, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15508 pattern childGuard
    simpa only [d832, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d832, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15448 pattern childGuard
    simpa only [d832, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15541 (pattern : Twelve) (guard : d1859 pattern = 1) : d847 pattern ≤ (1 : Int) + d56 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1859, d847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15170 pattern childGuard
    simpa only [d1859, d847, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1859, d847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15540 pattern childGuard
    simpa only [d1859, d847, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15542 (pattern : Twelve) (guard : d2496 pattern = 1) : d987 pattern ≤ (1 : Int) + d2549 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1859 pattern = 1 := by simpa only [d2496, d987, d2549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15541 pattern childGuard
    simpa only [d2496, d987, d2549, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2496, d987, d2549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15517 pattern childGuard
    simpa only [d2496, d987, d2549, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15543 (pattern : Twelve) (guard : d2496 pattern = 1) : d995 pattern ≤ (1 : Int) + d2550 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d995, d2550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15539 pattern childGuard
    simpa only [d995, d2550, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d995, d2550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15542 pattern childGuard
    simpa only [d995, d2550, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15544 (pattern : Twelve) (guard : d1 pattern = 1) : d834 pattern ≤ (1 : Int) + d30 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15508 pattern childGuard
    simpa only [d834, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15455 pattern childGuard
    simpa only [d834, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15545 (pattern : Twelve) (guard : d1859 pattern = 1) : d849 pattern ≤ (1 : Int) + d30 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1859, d849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15178 pattern childGuard
    simpa only [d1859, d849, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1859, d849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15544 pattern childGuard
    simpa only [d1859, d849, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15546 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (1 : Int) + d34 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15547 (pattern : Twelve) (guard : d2496 pattern = 1) : d988 pattern ≤ (1 : Int) + d2551 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1859 pattern = 1 := by simpa only [d2496, d988, d2551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15545 pattern childGuard
    simpa only [d2496, d988, d2551, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2496, d988, d2551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15546 pattern childGuard
    simpa only [d2496, d988, d2551, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15548 (pattern : Twelve) (guard : d1 pattern = 1) : d836 pattern ≤ (1 : Int) + d59 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d836, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15528 pattern childGuard
    simpa only [d836, d59, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d836, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11821 pattern childGuard
    simpa only [d836, d59, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15549 (pattern : Twelve) (guard : d1859 pattern = 1) : d851 pattern ≤ (1 : Int) + d59 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1859, d851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15184 pattern childGuard
    simpa only [d1859, d851, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1859, d851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15548 pattern childGuard
    simpa only [d1859, d851, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15550 (pattern : Twelve) (guard : d2496 pattern = 1) : d989 pattern ≤ (1 : Int) + d2552 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1859 pattern = 1 := by simpa only [d2496, d989, d2552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15549 pattern childGuard
    simpa only [d2496, d989, d2552, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2496, d989, d2552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15533 pattern childGuard
    simpa only [d2496, d989, d2552, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15551 (pattern : Twelve) (guard : d2496 pattern = 1) : d996 pattern ≤ (1 : Int) + d2553 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d996, d2553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15547 pattern childGuard
    simpa only [d996, d2553, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d996, d2553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15550 pattern childGuard
    simpa only [d996, d2553, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15552 (pattern : Twelve) (guard : d2496 pattern = 1) : d997 pattern ≤ (1 : Int) + d2554 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d997, d2554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15542 pattern childGuard
    simpa only [d997, d2554, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d997, d2554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15193 pattern childGuard
    simpa only [d997, d2554, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15553 (pattern : Twelve) (guard : d2496 pattern = 1) : d1002 pattern ≤ (1 : Int) + d2555 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d1002, d2555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15551 pattern childGuard
    simpa only [d1002, d2555, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d1002, d2555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15552 pattern childGuard
    simpa only [d1002, d2555, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15554 (pattern : Twelve) (guard : d2496 pattern = 1) : d1005 pattern ≤ (1 : Int) + d2556 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d1005, d2556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15543 pattern childGuard
    simpa only [d1005, d2556, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d1005, d2556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15553 pattern childGuard
    simpa only [d1005, d2556, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15555 (pattern : Twelve) (guard : d2496 pattern = 1) : d1007 pattern ≤ (1 : Int) + d2556 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d1007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15538 pattern childGuard
    simpa only [d1007, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d1007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15554 pattern childGuard
    simpa only [d1007, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15556 (pattern : Twelve) (guard : d2496 pattern = 1) : d998 pattern ≤ (1 : Int) + d2550 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d998, d2550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15539 pattern childGuard
    simpa only [d998, d2550, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d998, d2550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15518 pattern childGuard
    simpa only [d998, d2550, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15557 (pattern : Twelve) (guard : d2496 pattern = 1) : d990 pattern ≤ (1 : Int) + d2551 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1859 pattern = 1 := by simpa only [d2496, d990, d2551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15523 pattern childGuard
    simpa only [d2496, d990, d2551, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2496, d990, d2551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15546 pattern childGuard
    simpa only [d2496, d990, d2551, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15558 (pattern : Twelve) (guard : d2496 pattern = 1) : d999 pattern ≤ (1 : Int) + d2553 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d999, d2553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15557 pattern childGuard
    simpa only [d999, d2553, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d999, d2553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15534 pattern childGuard
    simpa only [d999, d2553, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15559 (pattern : Twelve) (guard : d2496 pattern = 1) : d1003 pattern ≤ (1 : Int) + d2555 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d1003, d2555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15558 pattern childGuard
    simpa only [d1003, d2555, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d1003, d2555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15536 pattern childGuard
    simpa only [d1003, d2555, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15560 (pattern : Twelve) (guard : d2496 pattern = 1) : d1006 pattern ≤ (1 : Int) + d2556 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d1006, d2556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15556 pattern childGuard
    simpa only [d1006, d2556, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d1006, d2556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15559 pattern childGuard
    simpa only [d1006, d2556, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15561 (pattern : Twelve) (guard : d2496 pattern = 1) : d1008 pattern ≤ (1 : Int) + d2556 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d1008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15560 pattern childGuard
    simpa only [d1008, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d1008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15554 pattern childGuard
    simpa only [d1008, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15562 (pattern : Twelve) (guard : d2496 pattern = 1) : d1009 pattern ≤ (1 : Int) + d2556 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d1009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15555 pattern childGuard
    simpa only [d1009, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d1009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15561 pattern childGuard
    simpa only [d1009, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15563 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (1 : Int) + d886 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15564 (pattern : Twelve) (guard : d2496 pattern = 1) : d990 pattern ≤ (1 : Int) + d2557 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1859 pattern = 1 := by simpa only [d2496, d990, d2557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15523 pattern childGuard
    simpa only [d2496, d990, d2557, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2496, d990, d2557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15563 pattern childGuard
    simpa only [d2496, d990, d2557, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15565 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (1 : Int) + d888 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15566 (pattern : Twelve) (guard : d2496 pattern = 1) : d985 pattern ≤ (1 : Int) + d2558 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1859 pattern = 1 := by simpa only [d2496, d985, d2558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15532 pattern childGuard
    simpa only [d2496, d985, d2558, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2496, d985, d2558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15565 pattern childGuard
    simpa only [d2496, d985, d2558, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15567 (pattern : Twelve) (guard : d2496 pattern = 1) : d999 pattern ≤ (1 : Int) + d2559 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d999, d2559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15564 pattern childGuard
    simpa only [d999, d2559, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d999, d2559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15566 pattern childGuard
    simpa only [d999, d2559, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15568 (pattern : Twelve) (guard : d2496 pattern = 1) : d1003 pattern ≤ (1 : Int) + d2560 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d1003, d2560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15567 pattern childGuard
    simpa only [d1003, d2560, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d1003, d2560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15536 pattern childGuard
    simpa only [d1003, d2560, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15569 (pattern : Twelve) (guard : d2496 pattern = 1) : d1006 pattern ≤ (1 : Int) + d2561 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d1006, d2561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15556 pattern childGuard
    simpa only [d1006, d2561, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d1006, d2561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15568 pattern childGuard
    simpa only [d1006, d2561, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15570 (pattern : Twelve) (guard : d2496 pattern = 1) : d988 pattern ≤ (1 : Int) + d2557 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1859 pattern = 1 := by simpa only [d2496, d988, d2557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15545 pattern childGuard
    simpa only [d2496, d988, d2557, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2496, d988, d2557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15563 pattern childGuard
    simpa only [d2496, d988, d2557, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15571 (pattern : Twelve) (guard : d2496 pattern = 1) : d989 pattern ≤ (1 : Int) + d2558 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1859 pattern = 1 := by simpa only [d2496, d989, d2558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15549 pattern childGuard
    simpa only [d2496, d989, d2558, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2496, d989, d2558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15565 pattern childGuard
    simpa only [d2496, d989, d2558, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15572 (pattern : Twelve) (guard : d2496 pattern = 1) : d996 pattern ≤ (1 : Int) + d2559 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d996, d2559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15570 pattern childGuard
    simpa only [d996, d2559, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d996, d2559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15571 pattern childGuard
    simpa only [d996, d2559, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15573 (pattern : Twelve) (guard : d2496 pattern = 1) : d1002 pattern ≤ (1 : Int) + d2560 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d1002, d2560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15572 pattern childGuard
    simpa only [d1002, d2560, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d1002, d2560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15552 pattern childGuard
    simpa only [d1002, d2560, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15574 (pattern : Twelve) (guard : d2496 pattern = 1) : d1005 pattern ≤ (1 : Int) + d2561 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d1005, d2561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15543 pattern childGuard
    simpa only [d1005, d2561, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d1005, d2561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15573 pattern childGuard
    simpa only [d1005, d2561, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15575 (pattern : Twelve) (guard : d2496 pattern = 1) : d1008 pattern ≤ (1 : Int) + d2561 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d1008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15569 pattern childGuard
    simpa only [d1008, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d1008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15574 pattern childGuard
    simpa only [d1008, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15576 (pattern : Twelve) (guard : d2496 pattern = 1) : d1010 pattern ≤ (1 : Int) + d2562 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d1010, d2562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15562 pattern childGuard
    simpa only [d1010, d2562, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d1010, d2562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15575 pattern childGuard
    simpa only [d1010, d2562, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15577 (pattern : Twelve) (guard : d0 pattern = 1) : d17 pattern ≤ (1 : Int) + d17 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15578 (pattern : Twelve) (guard : d1 pattern = 1) : d1275 pattern ≤ (1 : Int) + d17 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1275, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15153 pattern childGuard
    simpa only [d1275, d17, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1275, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15266 pattern childGuard
    simpa only [d1275, d17, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15579 (pattern : Twelve) (guard : d1 pattern = 1) : d1278 pattern ≤ (1 : Int) + d17 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15578 pattern childGuard
    simpa only [d1278, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15267 pattern childGuard
    simpa only [d1278, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15580 (pattern : Twelve) (guard : d1 pattern = 1) : d1284 pattern ≤ (1 : Int) + d17 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15579 pattern childGuard
    simpa only [d1284, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15267 pattern childGuard
    simpa only [d1284, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15581 (pattern : Twelve) (guard : d1859 pattern = 1) : d1293 pattern ≤ (1 : Int) + d17 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1859, d1293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15577 pattern childGuard
    simpa only [d1859, d1293, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1859, d1293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15580 pattern childGuard
    simpa only [d1859, d1293, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15582 (pattern : Twelve) (guard : d0 pattern = 1) : d1355 pattern ≤ (1 : Int) + d19 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15583 (pattern : Twelve) (guard : d2496 pattern = 1) : d1412 pattern ≤ (1 : Int) + d2563 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1859 pattern = 1 := by simpa only [d2496, d1412, d2563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15581 pattern childGuard
    simpa only [d2496, d1412, d2563, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2496, d1412, d2563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15582 pattern childGuard
    simpa only [d2496, d1412, d2563, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15584 (pattern : Twelve) (guard : d0 pattern = 1) : d827 pattern ≤ (1 : Int) + d827 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15585 (pattern : Twelve) (guard : d1 pattern = 1) : d1276 pattern ≤ (1 : Int) + d23 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1276, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15185 pattern childGuard
    simpa only [d1276, d23, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1276, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11185 pattern childGuard
    simpa only [d1276, d23, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15586 (pattern : Twelve) (guard : d1 pattern = 1) : d1279 pattern ≤ (1 : Int) + d34 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1279, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15578 pattern childGuard
    simpa only [d1279, d34, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1279, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15585 pattern childGuard
    simpa only [d1279, d34, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15587 (pattern : Twelve) (guard : d1 pattern = 1) : d1280 pattern ≤ (1 : Int) + d36 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1280, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15267 pattern childGuard
    simpa only [d1280, d36, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1280, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11282 pattern childGuard
    simpa only [d1280, d36, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15588 (pattern : Twelve) (guard : d1 pattern = 1) : d1285 pattern ≤ (1 : Int) + d827 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1285, d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15586 pattern childGuard
    simpa only [d1285, d827, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1285, d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15587 pattern childGuard
    simpa only [d1285, d827, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15589 (pattern : Twelve) (guard : d1859 pattern = 1) : d1295 pattern ≤ (1 : Int) + d827 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1859, d1295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15584 pattern childGuard
    simpa only [d1859, d1295, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1859, d1295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15588 pattern childGuard
    simpa only [d1859, d1295, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15590 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (1 : Int) + d1286 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15591 (pattern : Twelve) (guard : d2496 pattern = 1) : d1413 pattern ≤ (1 : Int) + d2564 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1859 pattern = 1 := by simpa only [d2496, d1413, d2564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15589 pattern childGuard
    simpa only [d2496, d1413, d2564, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2496, d1413, d2564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15590 pattern childGuard
    simpa only [d2496, d1413, d2564, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15592 (pattern : Twelve) (guard : d2496 pattern = 1) : d1417 pattern ≤ (1 : Int) + d2565 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d1417, d2565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15583 pattern childGuard
    simpa only [d1417, d2565, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d1417, d2565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15591 pattern childGuard
    simpa only [d1417, d2565, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15593 (pattern : Twelve) (guard : d2496 pattern = 1) : d1414 pattern ≤ (1 : Int) + d2563 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1859 pattern = 1 := by simpa only [d2496, d1414, d2563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15581 pattern childGuard
    simpa only [d2496, d1414, d2563, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2496, d1414, d2563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11226 pattern childGuard
    simpa only [d2496, d1414, d2563, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15594 (pattern : Twelve) (guard : d2496 pattern = 1) : d1418 pattern ≤ (1 : Int) + d2565 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d1418, d2565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15593 pattern childGuard
    simpa only [d1418, d2565, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d1418, d2565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15591 pattern childGuard
    simpa only [d1418, d2565, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15595 (pattern : Twelve) (guard : d2496 pattern = 1) : d1421 pattern ≤ (1 : Int) + d2565 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d1421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15592 pattern childGuard
    simpa only [d1421, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d1421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15594 pattern childGuard
    simpa only [d1421, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15596 (pattern : Twelve) (guard : d0 pattern = 1) : d34 pattern ≤ (1 : Int) + d34 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15597 (pattern : Twelve) (guard : d1 pattern = 1) : d1281 pattern ≤ (1 : Int) + d34 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1281, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15267 pattern childGuard
    simpa only [d1281, d34, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1281, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11186 pattern childGuard
    simpa only [d1281, d34, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15598 (pattern : Twelve) (guard : d1 pattern = 1) : d1287 pattern ≤ (1 : Int) + d34 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15586 pattern childGuard
    simpa only [d1287, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15597 pattern childGuard
    simpa only [d1287, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15599 (pattern : Twelve) (guard : d1859 pattern = 1) : d1297 pattern ≤ (1 : Int) + d34 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1859, d1297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15596 pattern childGuard
    simpa only [d1859, d1297, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1859, d1297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15598 pattern childGuard
    simpa only [d1859, d1297, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15600 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (1 : Int) + d817 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15601 (pattern : Twelve) (guard : d2496 pattern = 1) : d1415 pattern ≤ (1 : Int) + d2566 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1859 pattern = 1 := by simpa only [d2496, d1415, d2566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15599 pattern childGuard
    simpa only [d2496, d1415, d2566, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2496, d1415, d2566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15600 pattern childGuard
    simpa only [d2496, d1415, d2566, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15602 (pattern : Twelve) (guard : d0 pattern = 1) : d830 pattern ≤ (1 : Int) + d830 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15603 (pattern : Twelve) (guard : d1 pattern = 1) : d1277 pattern ≤ (1 : Int) + d24 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1277, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15526 pattern childGuard
    simpa only [d1277, d24, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1277, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11886 pattern childGuard
    simpa only [d1277, d24, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15604 (pattern : Twelve) (guard : d1 pattern = 1) : d1282 pattern ≤ (1 : Int) + d41 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1282, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15585 pattern childGuard
    simpa only [d1282, d41, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1282, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15603 pattern childGuard
    simpa only [d1282, d41, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15605 (pattern : Twelve) (guard : d1 pattern = 1) : d1288 pattern ≤ (1 : Int) + d830 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1288, d830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15604 pattern childGuard
    simpa only [d1288, d830, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1288, d830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11889 pattern childGuard
    simpa only [d1288, d830, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15606 (pattern : Twelve) (guard : d1859 pattern = 1) : d1299 pattern ≤ (1 : Int) + d830 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1859, d1299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15602 pattern childGuard
    simpa only [d1859, d1299, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1859, d1299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15605 pattern childGuard
    simpa only [d1859, d1299, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15607 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (1 : Int) + d1289 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15608 (pattern : Twelve) (guard : d2496 pattern = 1) : d1416 pattern ≤ (1 : Int) + d2567 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1859 pattern = 1 := by simpa only [d2496, d1416, d2567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15606 pattern childGuard
    simpa only [d2496, d1416, d2567, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2496, d1416, d2567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15607 pattern childGuard
    simpa only [d2496, d1416, d2567, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15609 (pattern : Twelve) (guard : d2496 pattern = 1) : d1419 pattern ≤ (1 : Int) + d2568 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d1419, d2568, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15601 pattern childGuard
    simpa only [d1419, d2568, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d1419, d2568, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15608 pattern childGuard
    simpa only [d1419, d2568, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15610 (pattern : Twelve) (guard : d2496 pattern = 1) : d1420 pattern ≤ (1 : Int) + d2569 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d1420, d2569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15591 pattern childGuard
    simpa only [d1420, d2569, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d1420, d2569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15193 pattern childGuard
    simpa only [d1420, d2569, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15611 (pattern : Twelve) (guard : d2496 pattern = 1) : d1422 pattern ≤ (1 : Int) + d2570 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d1422, d2570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15609 pattern childGuard
    simpa only [d1422, d2570, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d1422, d2570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15610 pattern childGuard
    simpa only [d1422, d2570, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15612 (pattern : Twelve) (guard : d2496 pattern = 1) : d1423 pattern ≤ (1 : Int) + d2571 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d1423, d2571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15595 pattern childGuard
    simpa only [d1423, d2571, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d1423, d2571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15611 pattern childGuard
    simpa only [d1423, d2571, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15613 (pattern : Twelve) (guard : d2496 pattern = 1) : d1424 pattern ≤ (1 : Int) + d2571 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d1424, d2571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15594 pattern childGuard
    simpa only [d1424, d2571, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d1424, d2571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15611 pattern childGuard
    simpa only [d1424, d2571, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15614 (pattern : Twelve) (guard : d2496 pattern = 1) : d1425 pattern ≤ (1 : Int) + d2571 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d1425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15612 pattern childGuard
    simpa only [d1425, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d1425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15613 pattern childGuard
    simpa only [d1425, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15615 (pattern : Twelve) (guard : d2496 pattern = 1) : d1426 pattern ≤ (1 : Int) + d2571 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d1426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15614 pattern childGuard
    simpa only [d1426, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d1426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15613 pattern childGuard
    simpa only [d1426, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15616 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (1 : Int) + d1336 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15617 (pattern : Twelve) (guard : d2496 pattern = 1) : d1415 pattern ≤ (1 : Int) + d2572 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1859 pattern = 1 := by simpa only [d2496, d1415, d2572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15599 pattern childGuard
    simpa only [d2496, d1415, d2572, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2496, d1415, d2572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15616 pattern childGuard
    simpa only [d2496, d1415, d2572, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15618 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (1 : Int) + d1338 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15619 (pattern : Twelve) (guard : d2496 pattern = 1) : d1416 pattern ≤ (1 : Int) + d2573 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1859 pattern = 1 := by simpa only [d2496, d1416, d2573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15606 pattern childGuard
    simpa only [d2496, d1416, d2573, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2496, d1416, d2573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15618 pattern childGuard
    simpa only [d2496, d1416, d2573, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15620 (pattern : Twelve) (guard : d2496 pattern = 1) : d1419 pattern ≤ (1 : Int) + d2574 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d1419, d2574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15617 pattern childGuard
    simpa only [d1419, d2574, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d1419, d2574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15619 pattern childGuard
    simpa only [d1419, d2574, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15621 (pattern : Twelve) (guard : d2496 pattern = 1) : d1422 pattern ≤ (1 : Int) + d2575 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d1422, d2575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15620 pattern childGuard
    simpa only [d1422, d2575, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d1422, d2575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15610 pattern childGuard
    simpa only [d1422, d2575, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15622 (pattern : Twelve) (guard : d2496 pattern = 1) : d1424 pattern ≤ (1 : Int) + d2576 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d1424, d2576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15594 pattern childGuard
    simpa only [d1424, d2576, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d1424, d2576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15621 pattern childGuard
    simpa only [d1424, d2576, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15623 (pattern : Twelve) (guard : d2496 pattern = 1) : d1427 pattern ≤ (1 : Int) + d2577 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d1427, d2577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15615 pattern childGuard
    simpa only [d1427, d2577, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d1427, d2577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15622 pattern childGuard
    simpa only [d1427, d2577, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15624 (pattern : Twelve) (guard : d0 pattern = 1) : d19 pattern ≤ (1 : Int) + d19 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15625 (pattern : Twelve) (guard : d1859 pattern = 1) : d1649 pattern ≤ (1 : Int) + d19 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1859, d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15624 pattern childGuard
    simpa only [d1859, d1649, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1859, d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15341 pattern childGuard
    simpa only [d1859, d1649, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15626 (pattern : Twelve) (guard : d2496 pattern = 1) : d1705 pattern ≤ (1 : Int) + d2578 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1859 pattern = 1 := by simpa only [d2496, d1705, d2578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15625 pattern childGuard
    simpa only [d2496, d1705, d2578, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2496, d1705, d2578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11068 pattern childGuard
    simpa only [d2496, d1705, d2578, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15627 (pattern : Twelve) (guard : d0 pattern = 1) : d1286 pattern ≤ (1 : Int) + d1286 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15628 (pattern : Twelve) (guard : d1 pattern = 1) : d1644 pattern ≤ (1 : Int) + d817 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1644, d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15341 pattern childGuard
    simpa only [d1644, d817, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1644, d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11199 pattern childGuard
    simpa only [d1644, d817, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15629 (pattern : Twelve) (guard : d1 pattern = 1) : d1645 pattern ≤ (1 : Int) + d29 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1645, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15341 pattern childGuard
    simpa only [d1645, d29, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1645, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11282 pattern childGuard
    simpa only [d1645, d29, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15630 (pattern : Twelve) (guard : d1 pattern = 1) : d1647 pattern ≤ (1 : Int) + d1286 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1647, d1286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15628 pattern childGuard
    simpa only [d1647, d1286, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1647, d1286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15629 pattern childGuard
    simpa only [d1647, d1286, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15631 (pattern : Twelve) (guard : d1859 pattern = 1) : d1651 pattern ≤ (1 : Int) + d1286 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1859, d1651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15627 pattern childGuard
    simpa only [d1859, d1651, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1859, d1651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15630 pattern childGuard
    simpa only [d1859, d1651, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15632 (pattern : Twelve) (guard : d2496 pattern = 1) : d1706 pattern ≤ (1 : Int) + d2579 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1859 pattern = 1 := by simpa only [d2496, d1706, d2579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15631 pattern childGuard
    simpa only [d2496, d1706, d2579, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2496, d1706, d2579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15607 pattern childGuard
    simpa only [d2496, d1706, d2579, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15633 (pattern : Twelve) (guard : d2496 pattern = 1) : d1709 pattern ≤ (1 : Int) + d2580 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d1709, d2580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15626 pattern childGuard
    simpa only [d1709, d2580, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d1709, d2580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15632 pattern childGuard
    simpa only [d1709, d2580, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15634 (pattern : Twelve) (guard : d0 pattern = 1) : d817 pattern ≤ (1 : Int) + d817 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15635 (pattern : Twelve) (guard : d1859 pattern = 1) : d1652 pattern ≤ (1 : Int) + d817 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1859, d1652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15634 pattern childGuard
    simpa only [d1859, d1652, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1859, d1652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15628 pattern childGuard
    simpa only [d1859, d1652, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15636 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (1 : Int) + d821 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15637 (pattern : Twelve) (guard : d2496 pattern = 1) : d1707 pattern ≤ (1 : Int) + d2581 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1859 pattern = 1 := by simpa only [d2496, d1707, d2581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15635 pattern childGuard
    simpa only [d2496, d1707, d2581, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2496, d1707, d2581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15636 pattern childGuard
    simpa only [d2496, d1707, d2581, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15638 (pattern : Twelve) (guard : d0 pattern = 1) : d1289 pattern ≤ (1 : Int) + d1289 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15639 (pattern : Twelve) (guard : d1 pattern = 1) : d1646 pattern ≤ (1 : Int) + d821 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1646, d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11199 pattern childGuard
    simpa only [d1646, d821, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1646, d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11932 pattern childGuard
    simpa only [d1646, d821, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15640 (pattern : Twelve) (guard : d1 pattern = 1) : d1648 pattern ≤ (1 : Int) + d1289 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1648, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15639 pattern childGuard
    simpa only [d1648, d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1648, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11934 pattern childGuard
    simpa only [d1648, d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15641 (pattern : Twelve) (guard : d1859 pattern = 1) : d1654 pattern ≤ (1 : Int) + d1289 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1859, d1654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15638 pattern childGuard
    simpa only [d1859, d1654, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1859, d1654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15640 pattern childGuard
    simpa only [d1859, d1654, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15642 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (1 : Int) + d822 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15643 (pattern : Twelve) (guard : d2496 pattern = 1) : d1708 pattern ≤ (1 : Int) + d2582 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1859 pattern = 1 := by simpa only [d2496, d1708, d2582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15641 pattern childGuard
    simpa only [d2496, d1708, d2582, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2496, d1708, d2582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15642 pattern childGuard
    simpa only [d2496, d1708, d2582, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15644 (pattern : Twelve) (guard : d2496 pattern = 1) : d1710 pattern ≤ (1 : Int) + d2583 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d1710, d2583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15637 pattern childGuard
    simpa only [d1710, d2583, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d1710, d2583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15643 pattern childGuard
    simpa only [d1710, d2583, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15645 (pattern : Twelve) (guard : d2496 pattern = 1) : d1711 pattern ≤ (1 : Int) + d2584 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d1711, d2584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15632 pattern childGuard
    simpa only [d1711, d2584, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d1711, d2584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15193 pattern childGuard
    simpa only [d1711, d2584, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15646 (pattern : Twelve) (guard : d2496 pattern = 1) : d1712 pattern ≤ (1 : Int) + d2585 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d1712, d2585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15644 pattern childGuard
    simpa only [d1712, d2585, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d1712, d2585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15645 pattern childGuard
    simpa only [d1712, d2585, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15647 (pattern : Twelve) (guard : d2496 pattern = 1) : d1713 pattern ≤ (1 : Int) + d2586 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d1713, d2586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15633 pattern childGuard
    simpa only [d1713, d2586, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d1713, d2586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15646 pattern childGuard
    simpa only [d1713, d2586, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15648 (pattern : Twelve) (guard : d2496 pattern = 1) : d1707 pattern ≤ (1 : Int) + d2587 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1859 pattern = 1 := by simpa only [d2496, d1707, d2587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15635 pattern childGuard
    simpa only [d2496, d1707, d2587, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2496, d1707, d2587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15607 pattern childGuard
    simpa only [d2496, d1707, d2587, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15649 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (1 : Int) + d1252 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15650 (pattern : Twelve) (guard : d2496 pattern = 1) : d1708 pattern ≤ (1 : Int) + d2588 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1859 pattern = 1 := by simpa only [d2496, d1708, d2588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15641 pattern childGuard
    simpa only [d2496, d1708, d2588, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2496, d1708, d2588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15649 pattern childGuard
    simpa only [d2496, d1708, d2588, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15651 (pattern : Twelve) (guard : d2496 pattern = 1) : d1710 pattern ≤ (1 : Int) + d2589 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d1710, d2589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15648 pattern childGuard
    simpa only [d1710, d2589, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d1710, d2589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15650 pattern childGuard
    simpa only [d1710, d2589, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15652 (pattern : Twelve) (guard : d2496 pattern = 1) : d1712 pattern ≤ (1 : Int) + d2590 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d1712, d2590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15651 pattern childGuard
    simpa only [d1712, d2590, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d1712, d2590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15645 pattern childGuard
    simpa only [d1712, d2590, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15653 (pattern : Twelve) (guard : d2496 pattern = 1) : d1713 pattern ≤ (1 : Int) + d2591 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d1713, d2591, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15633 pattern childGuard
    simpa only [d1713, d2591, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d1713, d2591, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15652 pattern childGuard
    simpa only [d1713, d2591, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15654 (pattern : Twelve) (guard : d2496 pattern = 1) : d1713 pattern ≤ (1 : Int) + d2592 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d2496 pattern = 1 := by simpa only [d2592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15647 pattern childGuard
    simpa only [d2592, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2496 pattern = 1 := by simpa only [d2592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15653 pattern childGuard
    simpa only [d2592, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15655 (pattern : Twelve) (guard : d477 pattern = 1) : d0 pattern ≤ (1 : Int) + d0 pattern := by
  omega
theorem c15656 (pattern : Twelve) (guard : d477 pattern = 1) : d26 pattern ≤ (1 : Int) + d26 pattern := by
  omega
theorem c15657 (pattern : Twelve) (guard : d477 pattern = 1) : d17 pattern ≤ (1 : Int) + d0 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d477, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15150 pattern childGuard
    simpa only [d477, d17, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d477, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15153 pattern childGuard
    simpa only [d477, d17, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15658 (pattern : Twelve) (guard : d477 pattern = 1) : d1 pattern ≤ (1 : Int) + d1 pattern := by
  omega
theorem c15659 (pattern : Twelve) (guard : d477 pattern = 1) : d27 pattern ≤ (1 : Int) + d26 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d27, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15657 pattern childGuard
    simpa only [d27, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d27, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15658 pattern childGuard
    simpa only [d27, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15660 (pattern : Twelve) (guard : d477 pattern = 1) : d50 pattern ≤ (1 : Int) + d26 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15656 pattern childGuard
    simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15659 pattern childGuard
    simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15661 (pattern : Twelve) (guard : d477 pattern = 1) : d72 pattern ≤ (1 : Int) + d2593 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d72, d2593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15655 pattern childGuard
    simpa only [d72, d2593, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d72, d2593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15660 pattern childGuard
    simpa only [d72, d2593, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15662 (pattern : Twelve) (guard : d477 pattern = 1) : d18 pattern ≤ (1 : Int) + d8 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d477, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12821 pattern childGuard
    simpa only [d477, d18, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d477, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12155 pattern childGuard
    simpa only [d477, d18, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15663 (pattern : Twelve) (guard : d477 pattern = 1) : d28 pattern ≤ (1 : Int) + d2594 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d28, d2594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15657 pattern childGuard
    simpa only [d28, d2594, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d28, d2594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15662 pattern childGuard
    simpa only [d28, d2594, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15664 (pattern : Twelve) (guard : d0 pattern = 1) : d10 pattern ≤ (1 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15665 (pattern : Twelve) (guard : d477 pattern = 1) : d19 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d477, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15664 pattern childGuard
    simpa only [d477, d19, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d477, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15340 pattern childGuard
    simpa only [d477, d19, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15666 (pattern : Twelve) (guard : d477 pattern = 1) : d6 pattern ≤ (1 : Int) + d6 pattern := by
  omega
theorem c15667 (pattern : Twelve) (guard : d477 pattern = 1) : d29 pattern ≤ (1 : Int) + d2595 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d29, d2595, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15665 pattern childGuard
    simpa only [d29, d2595, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d29, d2595, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15666 pattern childGuard
    simpa only [d29, d2595, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15668 (pattern : Twelve) (guard : d477 pattern = 1) : d51 pattern ≤ (1 : Int) + d2596 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d51, d2596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15663 pattern childGuard
    simpa only [d51, d2596, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d51, d2596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15667 pattern childGuard
    simpa only [d51, d2596, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15669 (pattern : Twelve) (guard : d477 pattern = 1) : d73 pattern ≤ (1 : Int) + d2597 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d73, d2597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15655 pattern childGuard
    simpa only [d73, d2597, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d73, d2597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15668 pattern childGuard
    simpa only [d73, d2597, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15670 (pattern : Twelve) (guard : d477 pattern = 1) : d91 pattern ≤ (1 : Int) + d2598 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d91, d2598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15661 pattern childGuard
    simpa only [d91, d2598, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d91, d2598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15669 pattern childGuard
    simpa only [d91, d2598, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15671 (pattern : Twelve) (guard : d477 pattern = 1) : d30 pattern ≤ (1 : Int) + d30 pattern := by
  omega
theorem c15672 (pattern : Twelve) (guard : d477 pattern = 1) : d20 pattern ≤ (1 : Int) + d12 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d477, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12735 pattern childGuard
    simpa only [d477, d20, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d477, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11198 pattern childGuard
    simpa only [d477, d20, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15673 (pattern : Twelve) (guard : d477 pattern = 1) : d31 pattern ≤ (1 : Int) + d2599 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d31, d2599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15655 pattern childGuard
    simpa only [d31, d2599, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d31, d2599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15672 pattern childGuard
    simpa only [d31, d2599, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15674 (pattern : Twelve) (guard : d477 pattern = 1) : d52 pattern ≤ (1 : Int) + d2600 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d52, d2600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15671 pattern childGuard
    simpa only [d52, d2600, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d52, d2600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15673 pattern childGuard
    simpa only [d52, d2600, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15675 (pattern : Twelve) (guard : d477 pattern = 1) : d21 pattern ≤ (1 : Int) + d13 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d477, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12693 pattern childGuard
    simpa only [d477, d21, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d477, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11387 pattern childGuard
    simpa only [d477, d21, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15676 (pattern : Twelve) (guard : d477 pattern = 1) : d32 pattern ≤ (1 : Int) + d2065 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d32, d2065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15657 pattern childGuard
    simpa only [d32, d2065, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d32, d2065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15675 pattern childGuard
    simpa only [d32, d2065, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15677 (pattern : Twelve) (guard : d477 pattern = 1) : d53 pattern ≤ (1 : Int) + d2066 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d53, d2066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15671 pattern childGuard
    simpa only [d53, d2066, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d53, d2066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15676 pattern childGuard
    simpa only [d53, d2066, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15678 (pattern : Twelve) (guard : d477 pattern = 1) : d74 pattern ≤ (1 : Int) + d2601 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d74, d2601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15674 pattern childGuard
    simpa only [d74, d2601, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d74, d2601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15677 pattern childGuard
    simpa only [d74, d2601, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15679 (pattern : Twelve) (guard : d477 pattern = 1) : d22 pattern ≤ (1 : Int) + d14 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d477, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12697 pattern childGuard
    simpa only [d477, d22, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d477, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11931 pattern childGuard
    simpa only [d477, d22, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
