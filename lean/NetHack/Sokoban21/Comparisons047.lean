/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons046
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c6580 (pattern : Twelve) (guard : d1870 pattern = 1) : d432 pattern ≤ (0 : Int) + d399 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1870, d432, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2589 pattern childGuard
    simpa only [d1870, d432, d399, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1870, d432, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6571 pattern childGuard
    simpa only [d1870, d432, d399, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6581 (pattern : Twelve) (guard : d1870 pattern = 1) : d432 pattern ≤ (0 : Int) + d407 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6580 pattern childGuard
    simpa only [d407, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6550 pattern childGuard
    simpa only [d407, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6582 (pattern : Twelve) (guard : d1870 pattern = 1) : d460 pattern ≤ (0 : Int) + d407 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6574 pattern childGuard
    simpa only [d460, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6581 pattern childGuard
    simpa only [d460, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6583 (pattern : Twelve) (guard : d1870 pattern = 1) : d467 pattern ≤ (0 : Int) + d407 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6579 pattern childGuard
    simpa only [d467, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6582 pattern childGuard
    simpa only [d467, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6584 (pattern : Twelve) (guard : d1870 pattern = 1) : d441 pattern ≤ (0 : Int) + d399 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1870, d441, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1312 pattern childGuard
    simpa only [d1870, d441, d399, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1870, d441, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6571 pattern childGuard
    simpa only [d1870, d441, d399, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6585 (pattern : Twelve) (guard : d1870 pattern = 1) : d441 pattern ≤ (0 : Int) + d394 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1870, d441, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1312 pattern childGuard
    simpa only [d1870, d441, d394, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1870, d441, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6549 pattern childGuard
    simpa only [d1870, d441, d394, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6586 (pattern : Twelve) (guard : d1870 pattern = 1) : d441 pattern ≤ (0 : Int) + d407 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6584 pattern childGuard
    simpa only [d407, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6585 pattern childGuard
    simpa only [d407, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6587 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d384 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6588 (pattern : Twelve) (guard : d1870 pattern = 1) : d436 pattern ≤ (0 : Int) + d397 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1870, d436, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2582 pattern childGuard
    simpa only [d1870, d436, d397, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1870, d436, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6587 pattern childGuard
    simpa only [d1870, d436, d397, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6589 (pattern : Twelve) (guard : d1870 pattern = 1) : d436 pattern ≤ (0 : Int) + d406 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6588 pattern childGuard
    simpa only [d406, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6562 pattern childGuard
    simpa only [d406, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6590 (pattern : Twelve) (guard : d1870 pattern = 1) : d461 pattern ≤ (0 : Int) + d413 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d461, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6586 pattern childGuard
    simpa only [d461, d413, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d461, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6589 pattern childGuard
    simpa only [d461, d413, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6591 (pattern : Twelve) (guard : d1870 pattern = 1) : d462 pattern ≤ (0 : Int) + d412 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d462, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6581 pattern childGuard
    simpa only [d462, d412, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d462, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5294 pattern childGuard
    simpa only [d462, d412, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6592 (pattern : Twelve) (guard : d1870 pattern = 1) : d468 pattern ≤ (0 : Int) + d417 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d468, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6590 pattern childGuard
    simpa only [d468, d417, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d468, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6591 pattern childGuard
    simpa only [d468, d417, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6593 (pattern : Twelve) (guard : d1870 pattern = 1) : d472 pattern ≤ (0 : Int) + d420 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d472, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6583 pattern childGuard
    simpa only [d472, d420, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d472, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6592 pattern childGuard
    simpa only [d472, d420, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6594 (pattern : Twelve) (guard : d1870 pattern = 1) : d474 pattern ≤ (0 : Int) + d422 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d474, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6570 pattern childGuard
    simpa only [d474, d422, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d474, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6593 pattern childGuard
    simpa only [d474, d422, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6595 (pattern : Twelve) (guard : d1870 pattern = 1) : d475 pattern ≤ (0 : Int) + d423 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d475, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6594 pattern childGuard
    simpa only [d475, d423, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d475, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6593 pattern childGuard
    simpa only [d475, d423, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6596 (pattern : Twelve) (guard : d1870 pattern = 1) : d452 pattern ≤ (0 : Int) + d407 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d452, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6575 pattern childGuard
    simpa only [d452, d407, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d452, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6550 pattern childGuard
    simpa only [d452, d407, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6597 (pattern : Twelve) (guard : d1870 pattern = 1) : d463 pattern ≤ (0 : Int) + d407 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6574 pattern childGuard
    simpa only [d463, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6596 pattern childGuard
    simpa only [d463, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6598 (pattern : Twelve) (guard : d1870 pattern = 1) : d469 pattern ≤ (0 : Int) + d407 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6597 pattern childGuard
    simpa only [d469, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6582 pattern childGuard
    simpa only [d469, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6599 (pattern : Twelve) (guard : d1848 pattern = 1) : d123 pattern ≤ (0 : Int) + d35 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d123, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1848, d123, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d123, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2923 pattern childGuard
    simpa only [d1848, d123, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6600 (pattern : Twelve) (guard : d1848 pattern = 1) : d132 pattern ≤ (0 : Int) + d35 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1312 pattern childGuard
    simpa only [d132, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6599 pattern childGuard
    simpa only [d132, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6601 (pattern : Twelve) (guard : d1870 pattern = 1) : d442 pattern ≤ (0 : Int) + d394 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1870, d442, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6600 pattern childGuard
    simpa only [d1870, d442, d394, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1870, d442, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6549 pattern childGuard
    simpa only [d1870, d442, d394, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6602 (pattern : Twelve) (guard : d1870 pattern = 1) : d453 pattern ≤ (0 : Int) + d407 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d453, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6584 pattern childGuard
    simpa only [d453, d407, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d453, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6601 pattern childGuard
    simpa only [d453, d407, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6603 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d386 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6604 (pattern : Twelve) (guard : d1870 pattern = 1) : d436 pattern ≤ (0 : Int) + d400 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1870, d436, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2582 pattern childGuard
    simpa only [d1870, d436, d400, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1870, d436, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6603 pattern childGuard
    simpa only [d1870, d436, d400, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6605 (pattern : Twelve) (guard : d1848 pattern = 1) : d126 pattern ≤ (0 : Int) + d39 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d126, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1333 pattern childGuard
    simpa only [d1848, d126, d39, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d126, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3025 pattern childGuard
    simpa only [d1848, d126, d39, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6606 (pattern : Twelve) (guard : d1848 pattern = 1) : d134 pattern ≤ (0 : Int) + d387 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d134, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6605 pattern childGuard
    simpa only [d134, d387, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d134, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5337 pattern childGuard
    simpa only [d134, d387, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6607 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d388 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6608 (pattern : Twelve) (guard : d1870 pattern = 1) : d443 pattern ≤ (0 : Int) + d401 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1870, d443, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6606 pattern childGuard
    simpa only [d1870, d443, d401, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1870, d443, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6607 pattern childGuard
    simpa only [d1870, d443, d401, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6609 (pattern : Twelve) (guard : d1870 pattern = 1) : d454 pattern ≤ (0 : Int) + d408 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d454, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6604 pattern childGuard
    simpa only [d454, d408, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d454, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6608 pattern childGuard
    simpa only [d454, d408, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6610 (pattern : Twelve) (guard : d1870 pattern = 1) : d464 pattern ≤ (0 : Int) + d414 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d464, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6602 pattern childGuard
    simpa only [d464, d414, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d464, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6609 pattern childGuard
    simpa only [d464, d414, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6611 (pattern : Twelve) (guard : d1870 pattern = 1) : d470 pattern ≤ (0 : Int) + d418 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d470, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6610 pattern childGuard
    simpa only [d470, d418, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d470, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6591 pattern childGuard
    simpa only [d470, d418, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6612 (pattern : Twelve) (guard : d1870 pattern = 1) : d473 pattern ≤ (0 : Int) + d421 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d473, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6598 pattern childGuard
    simpa only [d473, d421, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d473, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6611 pattern childGuard
    simpa only [d473, d421, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6613 (pattern : Twelve) (guard : d1870 pattern = 1) : d476 pattern ≤ (0 : Int) + d424 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d476, d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6595 pattern childGuard
    simpa only [d476, d424, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d476, d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6612 pattern childGuard
    simpa only [d476, d424, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6614 (pattern : Twelve) (guard : d0 pattern = 1) : d186 pattern ≤ (0 : Int) + d1030 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6615 (pattern : Twelve) (guard : d1870 pattern = 1) : d426 pattern ≤ (0 : Int) + d1038 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1870, d426, d1038, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2664 pattern childGuard
    simpa only [d1870, d426, d1038, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1870, d426, d1038, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6614 pattern childGuard
    simpa only [d1870, d426, d1038, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6616 (pattern : Twelve) (guard : d0 pattern = 1) : d908 pattern ≤ (0 : Int) + d1032 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6617 (pattern : Twelve) (guard : d1870 pattern = 1) : d1070 pattern ≤ (0 : Int) + d1039 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1870, d1070, d1039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2746 pattern childGuard
    simpa only [d1870, d1070, d1039, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1870, d1070, d1039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6616 pattern childGuard
    simpa only [d1870, d1070, d1039, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6618 (pattern : Twelve) (guard : d1870 pattern = 1) : d1078 pattern ≤ (0 : Int) + d1048 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1078, d1048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6615 pattern childGuard
    simpa only [d1078, d1048, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1078, d1048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6617 pattern childGuard
    simpa only [d1078, d1048, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6619 (pattern : Twelve) (guard : d0 pattern = 1) : d189 pattern ≤ (0 : Int) + d1033 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6620 (pattern : Twelve) (guard : d1870 pattern = 1) : d1071 pattern ≤ (0 : Int) + d1040 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1870, d1071, d1040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2670 pattern childGuard
    simpa only [d1870, d1071, d1040, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1870, d1071, d1040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6619 pattern childGuard
    simpa only [d1870, d1071, d1040, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6621 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1032 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6622 (pattern : Twelve) (guard : d1870 pattern = 1) : d1072 pattern ≤ (0 : Int) + d1041 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1870, d1072, d1041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2753 pattern childGuard
    simpa only [d1870, d1072, d1041, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1870, d1072, d1041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6621 pattern childGuard
    simpa only [d1870, d1072, d1041, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6623 (pattern : Twelve) (guard : d1870 pattern = 1) : d1079 pattern ≤ (0 : Int) + d1049 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1079, d1049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6620 pattern childGuard
    simpa only [d1079, d1049, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1079, d1049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6622 pattern childGuard
    simpa only [d1079, d1049, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6624 (pattern : Twelve) (guard : d1870 pattern = 1) : d1088 pattern ≤ (0 : Int) + d1054 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1088, d1054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6618 pattern childGuard
    simpa only [d1088, d1054, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1088, d1054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6623 pattern childGuard
    simpa only [d1088, d1054, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6625 (pattern : Twelve) (guard : d1870 pattern = 1) : d430 pattern ≤ (0 : Int) + d1040 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1870, d430, d1040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2677 pattern childGuard
    simpa only [d1870, d430, d1040, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1870, d430, d1040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6619 pattern childGuard
    simpa only [d1870, d430, d1040, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6626 (pattern : Twelve) (guard : d1870 pattern = 1) : d1073 pattern ≤ (0 : Int) + d1041 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1870, d1073, d1041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1418 pattern childGuard
    simpa only [d1870, d1073, d1041, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1870, d1073, d1041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6621 pattern childGuard
    simpa only [d1870, d1073, d1041, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6627 (pattern : Twelve) (guard : d1870 pattern = 1) : d1080 pattern ≤ (0 : Int) + d1049 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1080, d1049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6625 pattern childGuard
    simpa only [d1080, d1049, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1080, d1049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6626 pattern childGuard
    simpa only [d1080, d1049, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6628 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1033 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6629 (pattern : Twelve) (guard : d1870 pattern = 1) : d432 pattern ≤ (0 : Int) + d1042 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1870, d432, d1042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2589 pattern childGuard
    simpa only [d1870, d432, d1042, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1870, d432, d1042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6628 pattern childGuard
    simpa only [d1870, d432, d1042, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6630 (pattern : Twelve) (guard : d1870 pattern = 1) : d1081 pattern ≤ (0 : Int) + d1050 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1081, d1050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6629 pattern childGuard
    simpa only [d1081, d1050, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1081, d1050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6622 pattern childGuard
    simpa only [d1081, d1050, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6631 (pattern : Twelve) (guard : d1870 pattern = 1) : d1089 pattern ≤ (0 : Int) + d1055 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1089, d1055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6627 pattern childGuard
    simpa only [d1089, d1055, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1089, d1055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6630 pattern childGuard
    simpa only [d1089, d1055, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6632 (pattern : Twelve) (guard : d1870 pattern = 1) : d1095 pattern ≤ (0 : Int) + d1060 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1095, d1060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6624 pattern childGuard
    simpa only [d1095, d1060, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1095, d1060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6631 pattern childGuard
    simpa only [d1095, d1060, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6633 (pattern : Twelve) (guard : d0 pattern = 1) : d194 pattern ≤ (0 : Int) + d1033 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6634 (pattern : Twelve) (guard : d1870 pattern = 1) : d434 pattern ≤ (0 : Int) + d1043 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1870, d434, d1043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2686 pattern childGuard
    simpa only [d1870, d434, d1043, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1870, d434, d1043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6633 pattern childGuard
    simpa only [d1870, d434, d1043, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6635 (pattern : Twelve) (guard : d1870 pattern = 1) : d1074 pattern ≤ (0 : Int) + d1041 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1870, d1074, d1041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1291 pattern childGuard
    simpa only [d1870, d1074, d1041, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1870, d1074, d1041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6621 pattern childGuard
    simpa only [d1870, d1074, d1041, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6636 (pattern : Twelve) (guard : d1870 pattern = 1) : d1082 pattern ≤ (0 : Int) + d1051 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1082, d1051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6634 pattern childGuard
    simpa only [d1082, d1051, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1082, d1051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6635 pattern childGuard
    simpa only [d1082, d1051, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6637 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1034 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6638 (pattern : Twelve) (guard : d1870 pattern = 1) : d436 pattern ≤ (0 : Int) + d1044 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1870, d436, d1044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2582 pattern childGuard
    simpa only [d1870, d436, d1044, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1870, d436, d1044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6637 pattern childGuard
    simpa only [d1870, d436, d1044, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6639 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1035 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6640 (pattern : Twelve) (guard : d1870 pattern = 1) : d1075 pattern ≤ (0 : Int) + d1045 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1870, d1075, d1045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2769 pattern childGuard
    simpa only [d1870, d1075, d1045, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1870, d1075, d1045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6639 pattern childGuard
    simpa only [d1870, d1075, d1045, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6641 (pattern : Twelve) (guard : d1870 pattern = 1) : d1083 pattern ≤ (0 : Int) + d1052 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1083, d1052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6638 pattern childGuard
    simpa only [d1083, d1052, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1083, d1052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6640 pattern childGuard
    simpa only [d1083, d1052, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6642 (pattern : Twelve) (guard : d1870 pattern = 1) : d1090 pattern ≤ (0 : Int) + d1056 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1090, d1056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6636 pattern childGuard
    simpa only [d1090, d1056, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1090, d1056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6641 pattern childGuard
    simpa only [d1090, d1056, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6643 (pattern : Twelve) (guard : d1870 pattern = 1) : d1091 pattern ≤ (0 : Int) + d1057 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1091, d1057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6630 pattern childGuard
    simpa only [d1091, d1057, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1091, d1057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5294 pattern childGuard
    simpa only [d1091, d1057, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6644 (pattern : Twelve) (guard : d1870 pattern = 1) : d1096 pattern ≤ (0 : Int) + d1061 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1096, d1061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6642 pattern childGuard
    simpa only [d1096, d1061, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1096, d1061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6643 pattern childGuard
    simpa only [d1096, d1061, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6645 (pattern : Twelve) (guard : d1870 pattern = 1) : d1099 pattern ≤ (0 : Int) + d1064 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1099, d1064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6632 pattern childGuard
    simpa only [d1099, d1064, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1099, d1064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6644 pattern childGuard
    simpa only [d1099, d1064, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6646 (pattern : Twelve) (guard : d1870 pattern = 1) : d438 pattern ≤ (0 : Int) + d1042 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1870, d438, d1042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1354 pattern childGuard
    simpa only [d1870, d438, d1042, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1870, d438, d1042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6628 pattern childGuard
    simpa only [d1870, d438, d1042, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6647 (pattern : Twelve) (guard : d1870 pattern = 1) : d1084 pattern ≤ (0 : Int) + d1050 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1084, d1050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6646 pattern childGuard
    simpa only [d1084, d1050, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1084, d1050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6626 pattern childGuard
    simpa only [d1084, d1050, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6648 (pattern : Twelve) (guard : d1870 pattern = 1) : d1092 pattern ≤ (0 : Int) + d1050 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1092, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6647 pattern childGuard
    simpa only [d1092, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1092, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6630 pattern childGuard
    simpa only [d1092, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6649 (pattern : Twelve) (guard : d1870 pattern = 1) : d441 pattern ≤ (0 : Int) + d1042 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1870, d441, d1042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1312 pattern childGuard
    simpa only [d1870, d441, d1042, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1870, d441, d1042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6628 pattern childGuard
    simpa only [d1870, d441, d1042, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6650 (pattern : Twelve) (guard : d1870 pattern = 1) : d1085 pattern ≤ (0 : Int) + d1050 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1085, d1050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6649 pattern childGuard
    simpa only [d1085, d1050, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1085, d1050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6635 pattern childGuard
    simpa only [d1085, d1050, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6651 (pattern : Twelve) (guard : d1870 pattern = 1) : d1093 pattern ≤ (0 : Int) + d1058 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1093, d1058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6650 pattern childGuard
    simpa only [d1093, d1058, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1093, d1058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6641 pattern childGuard
    simpa only [d1093, d1058, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6652 (pattern : Twelve) (guard : d1870 pattern = 1) : d1097 pattern ≤ (0 : Int) + d1062 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1097, d1062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6651 pattern childGuard
    simpa only [d1097, d1062, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1097, d1062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6643 pattern childGuard
    simpa only [d1097, d1062, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6653 (pattern : Twelve) (guard : d1870 pattern = 1) : d1100 pattern ≤ (0 : Int) + d1065 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1100, d1065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6648 pattern childGuard
    simpa only [d1100, d1065, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1100, d1065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6652 pattern childGuard
    simpa only [d1100, d1065, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6654 (pattern : Twelve) (guard : d1870 pattern = 1) : d1102 pattern ≤ (0 : Int) + d1067 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1102, d1067, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6645 pattern childGuard
    simpa only [d1102, d1067, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1102, d1067, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6653 pattern childGuard
    simpa only [d1102, d1067, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6655 (pattern : Twelve) (guard : d1870 pattern = 1) : d1103 pattern ≤ (0 : Int) + d1068 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1103, d1068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6654 pattern childGuard
    simpa only [d1103, d1068, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1103, d1068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6653 pattern childGuard
    simpa only [d1103, d1068, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6656 (pattern : Twelve) (guard : d0 pattern = 1) : d119 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6657 (pattern : Twelve) (guard : d1848 pattern = 1) : d879 pattern ≤ (0 : Int) + d36 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d879, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c240 pattern childGuard
    simpa only [d1848, d879, d36, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d879, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6656 pattern childGuard
    simpa only [d1848, d879, d36, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6658 (pattern : Twelve) (guard : d1848 pattern = 1) : d886 pattern ≤ (0 : Int) + d36 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1291 pattern childGuard
    simpa only [d886, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6657 pattern childGuard
    simpa only [d886, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6659 (pattern : Twelve) (guard : d1870 pattern = 1) : d1076 pattern ≤ (0 : Int) + d1041 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1870, d1076, d1041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6658 pattern childGuard
    simpa only [d1870, d1076, d1041, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1870, d1076, d1041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6621 pattern childGuard
    simpa only [d1870, d1076, d1041, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6660 (pattern : Twelve) (guard : d1870 pattern = 1) : d1086 pattern ≤ (0 : Int) + d1050 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1086, d1050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6649 pattern childGuard
    simpa only [d1086, d1050, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1086, d1050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6659 pattern childGuard
    simpa only [d1086, d1050, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6661 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1036 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6662 (pattern : Twelve) (guard : d1870 pattern = 1) : d436 pattern ≤ (0 : Int) + d1046 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1870, d436, d1046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2582 pattern childGuard
    simpa only [d1870, d436, d1046, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1870, d436, d1046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6661 pattern childGuard
    simpa only [d1870, d436, d1046, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6663 (pattern : Twelve) (guard : d0 pattern = 1) : d118 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6664 (pattern : Twelve) (guard : d1848 pattern = 1) : d881 pattern ≤ (0 : Int) + d40 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d881, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1340 pattern childGuard
    simpa only [d1848, d881, d40, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d881, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6663 pattern childGuard
    simpa only [d1848, d881, d40, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6665 (pattern : Twelve) (guard : d1848 pattern = 1) : d888 pattern ≤ (0 : Int) + d1037 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d888, d1037, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6664 pattern childGuard
    simpa only [d888, d1037, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d888, d1037, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5401 pattern childGuard
    simpa only [d888, d1037, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6666 (pattern : Twelve) (guard : d1870 pattern = 1) : d1077 pattern ≤ (0 : Int) + d1047 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1870, d1077, d1047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6665 pattern childGuard
    simpa only [d1870, d1077, d1047, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1870, d1077, d1047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6458 pattern childGuard
    simpa only [d1870, d1077, d1047, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6667 (pattern : Twelve) (guard : d1870 pattern = 1) : d1087 pattern ≤ (0 : Int) + d1053 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1087, d1053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6662 pattern childGuard
    simpa only [d1087, d1053, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1087, d1053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6666 pattern childGuard
    simpa only [d1087, d1053, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6668 (pattern : Twelve) (guard : d1870 pattern = 1) : d1094 pattern ≤ (0 : Int) + d1059 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1094, d1059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6660 pattern childGuard
    simpa only [d1094, d1059, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1094, d1059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6667 pattern childGuard
    simpa only [d1094, d1059, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6669 (pattern : Twelve) (guard : d1870 pattern = 1) : d1098 pattern ≤ (0 : Int) + d1063 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1098, d1063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6668 pattern childGuard
    simpa only [d1098, d1063, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1098, d1063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6643 pattern childGuard
    simpa only [d1098, d1063, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6670 (pattern : Twelve) (guard : d1870 pattern = 1) : d1101 pattern ≤ (0 : Int) + d1066 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1101, d1066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6648 pattern childGuard
    simpa only [d1101, d1066, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1101, d1066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6669 pattern childGuard
    simpa only [d1101, d1066, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6671 (pattern : Twelve) (guard : d1870 pattern = 1) : d1104 pattern ≤ (0 : Int) + d1069 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1104, d1069, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6655 pattern childGuard
    simpa only [d1104, d1069, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1104, d1069, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6670 pattern childGuard
    simpa only [d1104, d1069, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6672 (pattern : Twelve) (guard : d0 pattern = 1) : d908 pattern ≤ (0 : Int) + d1445 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6673 (pattern : Twelve) (guard : d1870 pattern = 1) : d1070 pattern ≤ (0 : Int) + d1448 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1870, d1070, d1448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2746 pattern childGuard
    simpa only [d1870, d1070, d1448, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1870, d1070, d1448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6672 pattern childGuard
    simpa only [d1870, d1070, d1448, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6674 (pattern : Twelve) (guard : d1870 pattern = 1) : d1294 pattern ≤ (0 : Int) + d1449 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1870, d1294, d1449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1473 pattern childGuard
    simpa only [d1870, d1294, d1449, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1870, d1294, d1449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d1870, d1294, d1449, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6675 (pattern : Twelve) (guard : d1870 pattern = 1) : d1472 pattern ≤ (0 : Int) + d1455 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1472, d1455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6673 pattern childGuard
    simpa only [d1472, d1455, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1472, d1455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6674 pattern childGuard
    simpa only [d1472, d1455, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6676 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1445 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6677 (pattern : Twelve) (guard : d1870 pattern = 1) : d1072 pattern ≤ (0 : Int) + d1450 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1870, d1072, d1450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2753 pattern childGuard
    simpa only [d1870, d1072, d1450, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1870, d1072, d1450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6676 pattern childGuard
    simpa only [d1870, d1072, d1450, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6678 (pattern : Twelve) (guard : d1870 pattern = 1) : d1296 pattern ≤ (0 : Int) + d1449 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1870, d1296, d1449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2796 pattern childGuard
    simpa only [d1870, d1296, d1449, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1870, d1296, d1449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d1870, d1296, d1449, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6679 (pattern : Twelve) (guard : d1870 pattern = 1) : d1473 pattern ≤ (0 : Int) + d1456 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1473, d1456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6677 pattern childGuard
    simpa only [d1473, d1456, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1473, d1456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6678 pattern childGuard
    simpa only [d1473, d1456, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6680 (pattern : Twelve) (guard : d1870 pattern = 1) : d1479 pattern ≤ (0 : Int) + d1459 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1479, d1459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6675 pattern childGuard
    simpa only [d1479, d1459, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1479, d1459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6679 pattern childGuard
    simpa only [d1479, d1459, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6681 (pattern : Twelve) (guard : d1870 pattern = 1) : d1073 pattern ≤ (0 : Int) + d1450 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1870, d1073, d1450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1418 pattern childGuard
    simpa only [d1870, d1073, d1450, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1870, d1073, d1450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6676 pattern childGuard
    simpa only [d1870, d1073, d1450, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6682 (pattern : Twelve) (guard : d1870 pattern = 1) : d1474 pattern ≤ (0 : Int) + d1456 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1474, d1456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6681 pattern childGuard
    simpa only [d1474, d1456, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1474, d1456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6674 pattern childGuard
    simpa only [d1474, d1456, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6683 (pattern : Twelve) (guard : d1870 pattern = 1) : d1480 pattern ≤ (0 : Int) + d1456 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6682 pattern childGuard
    simpa only [d1480, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6679 pattern childGuard
    simpa only [d1480, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6684 (pattern : Twelve) (guard : d1870 pattern = 1) : d1484 pattern ≤ (0 : Int) + d1463 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1484, d1463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6680 pattern childGuard
    simpa only [d1484, d1463, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1484, d1463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6683 pattern childGuard
    simpa only [d1484, d1463, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6685 (pattern : Twelve) (guard : d1870 pattern = 1) : d1074 pattern ≤ (0 : Int) + d1450 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1870, d1074, d1450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1291 pattern childGuard
    simpa only [d1870, d1074, d1450, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1870, d1074, d1450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6676 pattern childGuard
    simpa only [d1870, d1074, d1450, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6686 (pattern : Twelve) (guard : d1870 pattern = 1) : d1298 pattern ≤ (0 : Int) + d1449 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1870, d1298, d1449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1405 pattern childGuard
    simpa only [d1870, d1298, d1449, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1870, d1298, d1449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d1870, d1298, d1449, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6687 (pattern : Twelve) (guard : d1870 pattern = 1) : d1475 pattern ≤ (0 : Int) + d1456 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1475, d1456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6685 pattern childGuard
    simpa only [d1475, d1456, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1475, d1456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6686 pattern childGuard
    simpa only [d1475, d1456, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6688 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1446 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6689 (pattern : Twelve) (guard : d1870 pattern = 1) : d1075 pattern ≤ (0 : Int) + d1451 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1870, d1075, d1451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2769 pattern childGuard
    simpa only [d1870, d1075, d1451, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1870, d1075, d1451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6688 pattern childGuard
    simpa only [d1870, d1075, d1451, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6690 (pattern : Twelve) (guard : d1870 pattern = 1) : d1300 pattern ≤ (0 : Int) + d1452 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1870, d1300, d1452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2807 pattern childGuard
    simpa only [d1870, d1300, d1452, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1870, d1300, d1452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d1870, d1300, d1452, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6691 (pattern : Twelve) (guard : d1870 pattern = 1) : d1476 pattern ≤ (0 : Int) + d1457 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1476, d1457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6689 pattern childGuard
    simpa only [d1476, d1457, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1476, d1457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6690 pattern childGuard
    simpa only [d1476, d1457, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6692 (pattern : Twelve) (guard : d1870 pattern = 1) : d1481 pattern ≤ (0 : Int) + d1460 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1481, d1460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6687 pattern childGuard
    simpa only [d1481, d1460, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1481, d1460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6691 pattern childGuard
    simpa only [d1481, d1460, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6693 (pattern : Twelve) (guard : d1870 pattern = 1) : d1482 pattern ≤ (0 : Int) + d1461 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1482, d1461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6679 pattern childGuard
    simpa only [d1482, d1461, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1482, d1461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5294 pattern childGuard
    simpa only [d1482, d1461, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6694 (pattern : Twelve) (guard : d1870 pattern = 1) : d1485 pattern ≤ (0 : Int) + d1464 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1485, d1464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6692 pattern childGuard
    simpa only [d1485, d1464, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1485, d1464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6693 pattern childGuard
    simpa only [d1485, d1464, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6695 (pattern : Twelve) (guard : d1870 pattern = 1) : d1487 pattern ≤ (0 : Int) + d1466 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1487, d1466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6684 pattern childGuard
    simpa only [d1487, d1466, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1487, d1466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6694 pattern childGuard
    simpa only [d1487, d1466, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6696 (pattern : Twelve) (guard : d1870 pattern = 1) : d1488 pattern ≤ (0 : Int) + d1467 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1488, d1467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6683 pattern childGuard
    simpa only [d1488, d1467, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1488, d1467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6694 pattern childGuard
    simpa only [d1488, d1467, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6697 (pattern : Twelve) (guard : d1870 pattern = 1) : d1490 pattern ≤ (0 : Int) + d1469 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1490, d1469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6695 pattern childGuard
    simpa only [d1490, d1469, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1490, d1469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6696 pattern childGuard
    simpa only [d1490, d1469, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6698 (pattern : Twelve) (guard : d1870 pattern = 1) : d1491 pattern ≤ (0 : Int) + d1470 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1491, d1470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6697 pattern childGuard
    simpa only [d1491, d1470, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1491, d1470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6696 pattern childGuard
    simpa only [d1491, d1470, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6699 (pattern : Twelve) (guard : d1848 pattern = 1) : d1329 pattern ≤ (0 : Int) + d29 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d1329, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c328 pattern childGuard
    simpa only [d1848, d1329, d29, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d1329, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1530 pattern childGuard
    simpa only [d1848, d1329, d29, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6700 (pattern : Twelve) (guard : d1848 pattern = 1) : d1336 pattern ≤ (0 : Int) + d29 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1405 pattern childGuard
    simpa only [d1336, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6699 pattern childGuard
    simpa only [d1336, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6701 (pattern : Twelve) (guard : d1870 pattern = 1) : d1342 pattern ≤ (0 : Int) + d1449 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1870, d1342, d1449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6700 pattern childGuard
    simpa only [d1870, d1342, d1449, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1870, d1342, d1449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d1870, d1342, d1449, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6702 (pattern : Twelve) (guard : d1870 pattern = 1) : d1477 pattern ≤ (0 : Int) + d1456 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1477, d1456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6685 pattern childGuard
    simpa only [d1477, d1456, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1477, d1456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6701 pattern childGuard
    simpa only [d1477, d1456, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6703 (pattern : Twelve) (guard : d1870 pattern = 1) : d1075 pattern ≤ (0 : Int) + d1453 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1870, d1075, d1453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2769 pattern childGuard
    simpa only [d1870, d1075, d1453, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1870, d1075, d1453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6496 pattern childGuard
    simpa only [d1870, d1075, d1453, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6704 (pattern : Twelve) (guard : d1848 pattern = 1) : d1332 pattern ≤ (0 : Int) + d42 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d1332, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c392 pattern childGuard
    simpa only [d1848, d1332, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d1332, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1537 pattern childGuard
    simpa only [d1848, d1332, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6705 (pattern : Twelve) (guard : d1848 pattern = 1) : d1338 pattern ≤ (0 : Int) + d1447 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1338, d1447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6704 pattern childGuard
    simpa only [d1338, d1447, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1338, d1447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5446 pattern childGuard
    simpa only [d1338, d1447, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6706 (pattern : Twelve) (guard : d1870 pattern = 1) : d1344 pattern ≤ (0 : Int) + d1454 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1870, d1344, d1454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6705 pattern childGuard
    simpa only [d1870, d1344, d1454, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1870, d1344, d1454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d1870, d1344, d1454, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6707 (pattern : Twelve) (guard : d1870 pattern = 1) : d1478 pattern ≤ (0 : Int) + d1458 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1478, d1458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6703 pattern childGuard
    simpa only [d1478, d1458, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1478, d1458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6706 pattern childGuard
    simpa only [d1478, d1458, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6708 (pattern : Twelve) (guard : d1870 pattern = 1) : d1483 pattern ≤ (0 : Int) + d1462 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1483, d1462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6702 pattern childGuard
    simpa only [d1483, d1462, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1483, d1462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6707 pattern childGuard
    simpa only [d1483, d1462, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6709 (pattern : Twelve) (guard : d1870 pattern = 1) : d1486 pattern ≤ (0 : Int) + d1465 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1486, d1465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6708 pattern childGuard
    simpa only [d1486, d1465, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1486, d1465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6693 pattern childGuard
    simpa only [d1486, d1465, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6710 (pattern : Twelve) (guard : d1870 pattern = 1) : d1489 pattern ≤ (0 : Int) + d1468 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1489, d1468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6683 pattern childGuard
    simpa only [d1489, d1468, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1489, d1468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6709 pattern childGuard
    simpa only [d1489, d1468, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6711 (pattern : Twelve) (guard : d1870 pattern = 1) : d1492 pattern ≤ (0 : Int) + d1471 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1492, d1471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6698 pattern childGuard
    simpa only [d1492, d1471, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1492, d1471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6710 pattern childGuard
    simpa only [d1492, d1471, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6712 (pattern : Twelve) (guard : d1870 pattern = 1) : d1294 pattern ≤ (0 : Int) + d1716 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1870, d1294, d1716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1473 pattern childGuard
    simpa only [d1870, d1294, d1716, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1870, d1294, d1716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1109 pattern childGuard
    simpa only [d1870, d1294, d1716, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6713 (pattern : Twelve) (guard : d1870 pattern = 1) : d1650 pattern ≤ (0 : Int) + d1452 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1870, d1650, d1452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1526 pattern childGuard
    simpa only [d1870, d1650, d1452, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1870, d1650, d1452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d1870, d1650, d1452, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6714 (pattern : Twelve) (guard : d1870 pattern = 1) : d1730 pattern ≤ (0 : Int) + d1719 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1730, d1719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6712 pattern childGuard
    simpa only [d1730, d1719, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1730, d1719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6713 pattern childGuard
    simpa only [d1730, d1719, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6715 (pattern : Twelve) (guard : d1870 pattern = 1) : d1296 pattern ≤ (0 : Int) + d1716 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1870, d1296, d1716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2796 pattern childGuard
    simpa only [d1870, d1296, d1716, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1870, d1296, d1716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1109 pattern childGuard
    simpa only [d1870, d1296, d1716, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6716 (pattern : Twelve) (guard : d1870 pattern = 1) : d1731 pattern ≤ (0 : Int) + d1719 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1731, d1719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6715 pattern childGuard
    simpa only [d1731, d1719, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1731, d1719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6690 pattern childGuard
    simpa only [d1731, d1719, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6717 (pattern : Twelve) (guard : d1870 pattern = 1) : d1736 pattern ≤ (0 : Int) + d1719 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6714 pattern childGuard
    simpa only [d1736, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6716 pattern childGuard
    simpa only [d1736, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6718 (pattern : Twelve) (guard : d1870 pattern = 1) : d1298 pattern ≤ (0 : Int) + d1716 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1870, d1298, d1716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1405 pattern childGuard
    simpa only [d1870, d1298, d1716, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1870, d1298, d1716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1109 pattern childGuard
    simpa only [d1870, d1298, d1716, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6719 (pattern : Twelve) (guard : d1870 pattern = 1) : d1653 pattern ≤ (0 : Int) + d1452 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1870, d1653, d1452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1432 pattern childGuard
    simpa only [d1870, d1653, d1452, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1870, d1653, d1452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d1870, d1653, d1452, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
