/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons060
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c8540 (pattern : Twelve) (guard : d1867 pattern = 1) : d716 pattern ≤ (0 : Int) + d78 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d716, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8539 pattern childGuard
    simpa only [d716, d78, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d716, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8516 pattern childGuard
    simpa only [d716, d78, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8541 (pattern : Twelve) (guard : d1867 pattern = 1) : d739 pattern ≤ (0 : Int) + d94 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d739, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8538 pattern childGuard
    simpa only [d739, d94, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d739, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8540 pattern childGuard
    simpa only [d739, d94, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8542 (pattern : Twelve) (guard : d1867 pattern = 1) : d755 pattern ≤ (0 : Int) + d103 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d755, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8530 pattern childGuard
    simpa only [d755, d103, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d755, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8541 pattern childGuard
    simpa only [d755, d103, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8543 (pattern : Twelve) (guard : d1867 pattern = 1) : d766 pattern ≤ (0 : Int) + d110 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d766, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8519 pattern childGuard
    simpa only [d766, d110, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d766, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8542 pattern childGuard
    simpa only [d766, d110, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8544 (pattern : Twelve) (guard : d0 pattern = 1) : d630 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c8545 (pattern : Twelve) (guard : d1867 pattern = 1) : d630 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7782 pattern childGuard
    simpa only [d1867, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8544 pattern childGuard
    simpa only [d1867, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8546 (pattern : Twelve) (guard : d1867 pattern = 1) : d642 pattern ≤ (0 : Int) + d2 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7810 pattern childGuard
    simpa only [d1867, d642, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8499 pattern childGuard
    simpa only [d1867, d642, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8547 (pattern : Twelve) (guard : d1867 pattern = 1) : d664 pattern ≤ (0 : Int) + d30 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d664, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8545 pattern childGuard
    simpa only [d664, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d664, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8546 pattern childGuard
    simpa only [d664, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8548 (pattern : Twelve) (guard : d1867 pattern = 1) : d665 pattern ≤ (0 : Int) + d30 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d665, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8520 pattern childGuard
    simpa only [d665, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d665, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8506 pattern childGuard
    simpa only [d665, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8549 (pattern : Twelve) (guard : d1867 pattern = 1) : d693 pattern ≤ (0 : Int) + d30 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8547 pattern childGuard
    simpa only [d693, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8548 pattern childGuard
    simpa only [d693, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8550 (pattern : Twelve) (guard : d0 pattern = 1) : d159 pattern ≤ (0 : Int) + d3 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c8551 (pattern : Twelve) (guard : d1867 pattern = 1) : d159 pattern ≤ (0 : Int) + d3 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7815 pattern childGuard
    simpa only [d1867, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8550 pattern childGuard
    simpa only [d1867, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8552 (pattern : Twelve) (guard : d1867 pattern = 1) : d666 pattern ≤ (0 : Int) + d37 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d666, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8508 pattern childGuard
    simpa only [d666, d37, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d666, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8551 pattern childGuard
    simpa only [d666, d37, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8553 (pattern : Twelve) (guard : d1867 pattern = 1) : d694 pattern ≤ (0 : Int) + d58 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d694, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8548 pattern childGuard
    simpa only [d694, d58, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d694, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8552 pattern childGuard
    simpa only [d694, d58, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8554 (pattern : Twelve) (guard : d1867 pattern = 1) : d717 pattern ≤ (0 : Int) + d79 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d717, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8549 pattern childGuard
    simpa only [d717, d79, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d717, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8553 pattern childGuard
    simpa only [d717, d79, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8555 (pattern : Twelve) (guard : d1867 pattern = 1) : d695 pattern ≤ (0 : Int) + d30 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8548 pattern childGuard
    simpa only [d695, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8535 pattern childGuard
    simpa only [d695, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8556 (pattern : Twelve) (guard : d1867 pattern = 1) : d718 pattern ≤ (0 : Int) + d80 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d718, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8555 pattern childGuard
    simpa only [d718, d80, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d718, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8516 pattern childGuard
    simpa only [d718, d80, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8557 (pattern : Twelve) (guard : d1867 pattern = 1) : d740 pattern ≤ (0 : Int) + d95 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d740, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8554 pattern childGuard
    simpa only [d740, d95, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d740, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8556 pattern childGuard
    simpa only [d740, d95, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8558 (pattern : Twelve) (guard : d1867 pattern = 1) : d643 pattern ≤ (0 : Int) + d2 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7823 pattern childGuard
    simpa only [d1867, d643, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8499 pattern childGuard
    simpa only [d1867, d643, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8559 (pattern : Twelve) (guard : d0 pattern = 1) : d13 pattern ≤ (0 : Int) + d4 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c8560 (pattern : Twelve) (guard : d1867 pattern = 1) : d13 pattern ≤ (0 : Int) + d4 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7825 pattern childGuard
    simpa only [d1867, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8559 pattern childGuard
    simpa only [d1867, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8561 (pattern : Twelve) (guard : d1867 pattern = 1) : d667 pattern ≤ (0 : Int) + d38 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d667, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8558 pattern childGuard
    simpa only [d667, d38, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d667, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8560 pattern childGuard
    simpa only [d667, d38, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8562 (pattern : Twelve) (guard : d1867 pattern = 1) : d668 pattern ≤ (0 : Int) + d39 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d668, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8506 pattern childGuard
    simpa only [d668, d39, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d668, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d668, d39, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8563 (pattern : Twelve) (guard : d1867 pattern = 1) : d696 pattern ≤ (0 : Int) + d59 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d696, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8561 pattern childGuard
    simpa only [d696, d59, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d696, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8562 pattern childGuard
    simpa only [d696, d59, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8564 (pattern : Twelve) (guard : d1867 pattern = 1) : d669 pattern ≤ (0 : Int) + d38 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d669, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8506 pattern childGuard
    simpa only [d669, d38, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d669, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8560 pattern childGuard
    simpa only [d669, d38, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8565 (pattern : Twelve) (guard : d1867 pattern = 1) : d668 pattern ≤ (0 : Int) + d40 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d668, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8514 pattern childGuard
    simpa only [d668, d40, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d668, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d668, d40, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8566 (pattern : Twelve) (guard : d1867 pattern = 1) : d697 pattern ≤ (0 : Int) + d60 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d697, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8564 pattern childGuard
    simpa only [d697, d60, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d697, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8565 pattern childGuard
    simpa only [d697, d60, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8567 (pattern : Twelve) (guard : d1867 pattern = 1) : d719 pattern ≤ (0 : Int) + d81 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d719, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8563 pattern childGuard
    simpa only [d719, d81, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d719, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8566 pattern childGuard
    simpa only [d719, d81, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8568 (pattern : Twelve) (guard : d1867 pattern = 1) : d697 pattern ≤ (0 : Int) + d59 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d697, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8564 pattern childGuard
    simpa only [d697, d59, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d697, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8562 pattern childGuard
    simpa only [d697, d59, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8569 (pattern : Twelve) (guard : d0 pattern = 1) : d13 pattern ≤ (0 : Int) + d15 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c8570 (pattern : Twelve) (guard : d1867 pattern = 1) : d13 pattern ≤ (0 : Int) + d24 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7825 pattern childGuard
    simpa only [d1867, d24, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8569 pattern childGuard
    simpa only [d1867, d24, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8571 (pattern : Twelve) (guard : d1867 pattern = 1) : d669 pattern ≤ (0 : Int) + d41 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d669, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8514 pattern childGuard
    simpa only [d669, d41, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d669, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8570 pattern childGuard
    simpa only [d669, d41, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8572 (pattern : Twelve) (guard : d0 pattern = 1) : d159 pattern ≤ (0 : Int) + d12 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c8573 (pattern : Twelve) (guard : d1867 pattern = 1) : d644 pattern ≤ (0 : Int) + d25 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d644, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7837 pattern childGuard
    simpa only [d1867, d644, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d644, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8572 pattern childGuard
    simpa only [d1867, d644, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8574 (pattern : Twelve) (guard : d1867 pattern = 1) : d670 pattern ≤ (0 : Int) + d42 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d670, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8573 pattern childGuard
    simpa only [d670, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d670, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d670, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8575 (pattern : Twelve) (guard : d1867 pattern = 1) : d698 pattern ≤ (0 : Int) + d61 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d698, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8571 pattern childGuard
    simpa only [d698, d61, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d698, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8574 pattern childGuard
    simpa only [d698, d61, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8576 (pattern : Twelve) (guard : d1867 pattern = 1) : d720 pattern ≤ (0 : Int) + d82 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d720, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8568 pattern childGuard
    simpa only [d720, d82, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d720, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8575 pattern childGuard
    simpa only [d720, d82, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8577 (pattern : Twelve) (guard : d1867 pattern = 1) : d741 pattern ≤ (0 : Int) + d96 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d741, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8567 pattern childGuard
    simpa only [d741, d96, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d741, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8576 pattern childGuard
    simpa only [d741, d96, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8578 (pattern : Twelve) (guard : d1867 pattern = 1) : d756 pattern ≤ (0 : Int) + d104 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d756, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8557 pattern childGuard
    simpa only [d756, d104, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d756, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8577 pattern childGuard
    simpa only [d756, d104, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8579 (pattern : Twelve) (guard : d1867 pattern = 1) : d645 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7845 pattern childGuard
    simpa only [d1867, d645, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6994 pattern childGuard
    simpa only [d1867, d645, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8580 (pattern : Twelve) (guard : d1867 pattern = 1) : d671 pattern ≤ (0 : Int) + d30 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d671, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8579 pattern childGuard
    simpa only [d671, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d671, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8506 pattern childGuard
    simpa only [d671, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8581 (pattern : Twelve) (guard : d1867 pattern = 1) : d699 pattern ≤ (0 : Int) + d56 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d699, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8580 pattern childGuard
    simpa only [d699, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d699, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8533 pattern childGuard
    simpa only [d699, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8582 (pattern : Twelve) (guard : d1867 pattern = 1) : d721 pattern ≤ (0 : Int) + d77 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d721, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8581 pattern childGuard
    simpa only [d721, d77, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d721, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8537 pattern childGuard
    simpa only [d721, d77, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8583 (pattern : Twelve) (guard : d1867 pattern = 1) : d742 pattern ≤ (0 : Int) + d94 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d742, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8582 pattern childGuard
    simpa only [d742, d94, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d742, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8540 pattern childGuard
    simpa only [d742, d94, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8584 (pattern : Twelve) (guard : d1867 pattern = 1) : d757 pattern ≤ (0 : Int) + d105 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d757, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8583 pattern childGuard
    simpa only [d757, d105, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d757, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d757, d105, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8585 (pattern : Twelve) (guard : d1867 pattern = 1) : d767 pattern ≤ (0 : Int) + d111 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d767, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8578 pattern childGuard
    simpa only [d767, d111, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d767, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8584 pattern childGuard
    simpa only [d767, d111, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8586 (pattern : Twelve) (guard : d1867 pattern = 1) : d772 pattern ≤ (0 : Int) + d114 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d772, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8543 pattern childGuard
    simpa only [d772, d114, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d772, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8585 pattern childGuard
    simpa only [d772, d114, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8587 (pattern : Twelve) (guard : d1867 pattern = 1) : d661 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d661, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8485 pattern childGuard
    simpa only [d661, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d661, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8480 pattern childGuard
    simpa only [d661, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8588 (pattern : Twelve) (guard : d1867 pattern = 1) : d661 pattern ≤ (0 : Int) + d50 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8587 pattern childGuard
    simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8525 pattern childGuard
    simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8589 (pattern : Twelve) (guard : d1867 pattern = 1) : d722 pattern ≤ (0 : Int) + d72 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d722, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8485 pattern childGuard
    simpa only [d722, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d722, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8588 pattern childGuard
    simpa only [d722, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8590 (pattern : Twelve) (guard : d1867 pattern = 1) : d672 pattern ≤ (0 : Int) + d28 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d672, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8508 pattern childGuard
    simpa only [d672, d28, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d672, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8489 pattern childGuard
    simpa only [d672, d28, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8591 (pattern : Twelve) (guard : d1867 pattern = 1) : d700 pattern ≤ (0 : Int) + d51 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d700, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8590 pattern childGuard
    simpa only [d700, d51, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d700, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8493 pattern childGuard
    simpa only [d700, d51, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8592 (pattern : Twelve) (guard : d1867 pattern = 1) : d723 pattern ≤ (0 : Int) + d73 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d723, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8485 pattern childGuard
    simpa only [d723, d73, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d723, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8591 pattern childGuard
    simpa only [d723, d73, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8593 (pattern : Twelve) (guard : d1867 pattern = 1) : d743 pattern ≤ (0 : Int) + d91 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d743, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8589 pattern childGuard
    simpa only [d743, d91, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d743, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8592 pattern childGuard
    simpa only [d743, d91, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8594 (pattern : Twelve) (guard : d1867 pattern = 1) : d673 pattern ≤ (0 : Int) + d31 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d673, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8485 pattern childGuard
    simpa only [d673, d31, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d673, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8503 pattern childGuard
    simpa only [d673, d31, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8595 (pattern : Twelve) (guard : d1867 pattern = 1) : d701 pattern ≤ (0 : Int) + d52 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d701, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8535 pattern childGuard
    simpa only [d701, d52, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d701, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8594 pattern childGuard
    simpa only [d701, d52, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8596 (pattern : Twelve) (guard : d1867 pattern = 1) : d702 pattern ≤ (0 : Int) + d53 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d702, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8535 pattern childGuard
    simpa only [d702, d53, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d702, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8509 pattern childGuard
    simpa only [d702, d53, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8597 (pattern : Twelve) (guard : d1867 pattern = 1) : d724 pattern ≤ (0 : Int) + d74 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d724, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8595 pattern childGuard
    simpa only [d724, d74, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d724, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8596 pattern childGuard
    simpa only [d724, d74, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8598 (pattern : Twelve) (guard : d1867 pattern = 1) : d703 pattern ≤ (0 : Int) + d54 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d703, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8535 pattern childGuard
    simpa only [d703, d54, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d703, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8512 pattern childGuard
    simpa only [d703, d54, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8599 (pattern : Twelve) (guard : d1867 pattern = 1) : d725 pattern ≤ (0 : Int) + d75 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d725, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8598 pattern childGuard
    simpa only [d725, d75, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d725, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8516 pattern childGuard
    simpa only [d725, d75, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8600 (pattern : Twelve) (guard : d1867 pattern = 1) : d744 pattern ≤ (0 : Int) + d92 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d744, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8597 pattern childGuard
    simpa only [d744, d92, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d744, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8599 pattern childGuard
    simpa only [d744, d92, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8601 (pattern : Twelve) (guard : d1867 pattern = 1) : d758 pattern ≤ (0 : Int) + d102 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d758, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8593 pattern childGuard
    simpa only [d758, d102, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d758, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8600 pattern childGuard
    simpa only [d758, d102, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8602 (pattern : Twelve) (guard : d1867 pattern = 1) : d726 pattern ≤ (0 : Int) + d76 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d726, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8485 pattern childGuard
    simpa only [d726, d76, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d726, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8516 pattern childGuard
    simpa only [d726, d76, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8603 (pattern : Twelve) (guard : d1867 pattern = 1) : d745 pattern ≤ (0 : Int) + d93 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d745, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8589 pattern childGuard
    simpa only [d745, d93, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d745, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8602 pattern childGuard
    simpa only [d745, d93, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8604 (pattern : Twelve) (guard : d1867 pattern = 1) : d692 pattern ≤ (0 : Int) + d77 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8539 pattern childGuard
    simpa only [d77, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8537 pattern childGuard
    simpa only [d77, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8605 (pattern : Twelve) (guard : d1867 pattern = 1) : d746 pattern ≤ (0 : Int) + d94 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d746, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8604 pattern childGuard
    simpa only [d746, d94, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d746, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8540 pattern childGuard
    simpa only [d746, d94, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8606 (pattern : Twelve) (guard : d1867 pattern = 1) : d759 pattern ≤ (0 : Int) + d103 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d759, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8603 pattern childGuard
    simpa only [d759, d103, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d759, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8605 pattern childGuard
    simpa only [d759, d103, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8607 (pattern : Twelve) (guard : d1867 pattern = 1) : d768 pattern ≤ (0 : Int) + d110 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d768, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8601 pattern childGuard
    simpa only [d768, d110, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d768, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8606 pattern childGuard
    simpa only [d768, d110, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8608 (pattern : Twelve) (guard : d1867 pattern = 1) : d704 pattern ≤ (0 : Int) + d58 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d704, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8535 pattern childGuard
    simpa only [d704, d58, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d704, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8552 pattern childGuard
    simpa only [d704, d58, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8609 (pattern : Twelve) (guard : d1867 pattern = 1) : d727 pattern ≤ (0 : Int) + d79 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d727, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8535 pattern childGuard
    simpa only [d727, d79, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d727, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8608 pattern childGuard
    simpa only [d727, d79, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8610 (pattern : Twelve) (guard : d1867 pattern = 1) : d728 pattern ≤ (0 : Int) + d80 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d728, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8535 pattern childGuard
    simpa only [d728, d80, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d728, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8516 pattern childGuard
    simpa only [d728, d80, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8611 (pattern : Twelve) (guard : d1867 pattern = 1) : d747 pattern ≤ (0 : Int) + d95 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d747, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8609 pattern childGuard
    simpa only [d747, d95, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d747, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8610 pattern childGuard
    simpa only [d747, d95, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8612 (pattern : Twelve) (guard : d1867 pattern = 1) : d697 pattern ≤ (0 : Int) + d81 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8568 pattern childGuard
    simpa only [d81, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8566 pattern childGuard
    simpa only [d81, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8613 (pattern : Twelve) (guard : d1867 pattern = 1) : d748 pattern ≤ (0 : Int) + d96 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d748, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8612 pattern childGuard
    simpa only [d748, d96, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d748, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8576 pattern childGuard
    simpa only [d748, d96, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8614 (pattern : Twelve) (guard : d1867 pattern = 1) : d760 pattern ≤ (0 : Int) + d104 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d760, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8611 pattern childGuard
    simpa only [d760, d104, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d760, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8613 pattern childGuard
    simpa only [d760, d104, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8615 (pattern : Twelve) (guard : d1867 pattern = 1) : d761 pattern ≤ (0 : Int) + d105 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d761, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8605 pattern childGuard
    simpa only [d761, d105, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d761, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d761, d105, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8616 (pattern : Twelve) (guard : d1867 pattern = 1) : d769 pattern ≤ (0 : Int) + d111 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d769, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8614 pattern childGuard
    simpa only [d769, d111, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d769, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8615 pattern childGuard
    simpa only [d769, d111, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8617 (pattern : Twelve) (guard : d1867 pattern = 1) : d773 pattern ≤ (0 : Int) + d114 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d773, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8607 pattern childGuard
    simpa only [d773, d114, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d773, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8616 pattern childGuard
    simpa only [d773, d114, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8618 (pattern : Twelve) (guard : d1867 pattern = 1) : d775 pattern ≤ (0 : Int) + d114 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8586 pattern childGuard
    simpa only [d775, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8617 pattern childGuard
    simpa only [d775, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8619 (pattern : Twelve) (guard : d1867 pattern = 1) : d776 pattern ≤ (0 : Int) + d114 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8618 pattern childGuard
    simpa only [d776, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8617 pattern childGuard
    simpa only [d776, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8620 (pattern : Twelve) (guard : d1867 pattern = 1) : d674 pattern ≤ (0 : Int) + d120 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d674, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8508 pattern childGuard
    simpa only [d674, d120, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d674, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8573 pattern childGuard
    simpa only [d674, d120, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8621 (pattern : Twelve) (guard : d1867 pattern = 1) : d705 pattern ≤ (0 : Int) + d129 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d705, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8620 pattern childGuard
    simpa only [d705, d129, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d705, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8493 pattern childGuard
    simpa only [d705, d129, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8622 (pattern : Twelve) (guard : d1867 pattern = 1) : d729 pattern ≤ (0 : Int) + d136 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d729, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8485 pattern childGuard
    simpa only [d729, d136, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d729, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8621 pattern childGuard
    simpa only [d729, d136, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8623 (pattern : Twelve) (guard : d1867 pattern = 1) : d749 pattern ≤ (0 : Int) + d144 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d749, d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8589 pattern childGuard
    simpa only [d749, d144, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d749, d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8622 pattern childGuard
    simpa only [d749, d144, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8624 (pattern : Twelve) (guard : d1867 pattern = 1) : d657 pattern ≤ (0 : Int) + d121 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d657, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8485 pattern childGuard
    simpa only [d657, d121, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d657, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8514 pattern childGuard
    simpa only [d657, d121, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8625 (pattern : Twelve) (guard : d1867 pattern = 1) : d692 pattern ≤ (0 : Int) + d130 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d692, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8624 pattern childGuard
    simpa only [d692, d130, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d692, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8536 pattern childGuard
    simpa only [d692, d130, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8626 (pattern : Twelve) (guard : d1867 pattern = 1) : d730 pattern ≤ (0 : Int) + d137 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d730, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8595 pattern childGuard
    simpa only [d730, d137, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d730, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8625 pattern childGuard
    simpa only [d730, d137, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8627 (pattern : Twelve) (guard : d1867 pattern = 1) : d731 pattern ≤ (0 : Int) + d138 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d731, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8539 pattern childGuard
    simpa only [d731, d138, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d731, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8621 pattern childGuard
    simpa only [d731, d138, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8628 (pattern : Twelve) (guard : d1867 pattern = 1) : d750 pattern ≤ (0 : Int) + d145 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d750, d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8626 pattern childGuard
    simpa only [d750, d145, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d750, d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8627 pattern childGuard
    simpa only [d750, d145, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8629 (pattern : Twelve) (guard : d1867 pattern = 1) : d762 pattern ≤ (0 : Int) + d149 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d762, d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8623 pattern childGuard
    simpa only [d762, d149, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d762, d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8628 pattern childGuard
    simpa only [d762, d149, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8630 (pattern : Twelve) (guard : d1867 pattern = 1) : d692 pattern ≤ (0 : Int) + d139 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8539 pattern childGuard
    simpa only [d139, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8625 pattern childGuard
    simpa only [d139, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8631 (pattern : Twelve) (guard : d1867 pattern = 1) : d751 pattern ≤ (0 : Int) + d146 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d751, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8630 pattern childGuard
    simpa only [d751, d146, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d751, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8627 pattern childGuard
    simpa only [d751, d146, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8632 (pattern : Twelve) (guard : d1867 pattern = 1) : d763 pattern ≤ (0 : Int) + d150 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d763, d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8623 pattern childGuard
    simpa only [d763, d150, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d763, d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8631 pattern childGuard
    simpa only [d763, d150, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8633 (pattern : Twelve) (guard : d1867 pattern = 1) : d770 pattern ≤ (0 : Int) + d153 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d770, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8629 pattern childGuard
    simpa only [d770, d153, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d770, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8632 pattern childGuard
    simpa only [d770, d153, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8634 (pattern : Twelve) (guard : d1867 pattern = 1) : d675 pattern ≤ (0 : Int) + d122 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d675, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8508 pattern childGuard
    simpa only [d675, d122, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d675, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8560 pattern childGuard
    simpa only [d675, d122, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8635 (pattern : Twelve) (guard : d1867 pattern = 1) : d706 pattern ≤ (0 : Int) + d131 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d706, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8624 pattern childGuard
    simpa only [d706, d131, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d706, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8634 pattern childGuard
    simpa only [d706, d131, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8636 (pattern : Twelve) (guard : d1867 pattern = 1) : d732 pattern ≤ (0 : Int) + d140 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d732, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8535 pattern childGuard
    simpa only [d732, d140, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d732, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8635 pattern childGuard
    simpa only [d732, d140, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8637 (pattern : Twelve) (guard : d1867 pattern = 1) : d666 pattern ≤ (0 : Int) + d123 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d666, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8485 pattern childGuard
    simpa only [d666, d123, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d666, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8551 pattern childGuard
    simpa only [d666, d123, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8638 (pattern : Twelve) (guard : d1867 pattern = 1) : d704 pattern ≤ (0 : Int) + d132 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d704, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8535 pattern childGuard
    simpa only [d704, d132, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d704, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8637 pattern childGuard
    simpa only [d704, d132, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8639 (pattern : Twelve) (guard : d1867 pattern = 1) : d733 pattern ≤ (0 : Int) + d141 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d733, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8638 pattern childGuard
    simpa only [d733, d141, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d733, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8621 pattern childGuard
    simpa only [d733, d141, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8640 (pattern : Twelve) (guard : d1867 pattern = 1) : d752 pattern ≤ (0 : Int) + d147 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d752, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8636 pattern childGuard
    simpa only [d752, d147, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d752, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8639 pattern childGuard
    simpa only [d752, d147, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8641 (pattern : Twelve) (guard : d1867 pattern = 1) : d14 pattern ≤ (0 : Int) + d118 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7908 pattern childGuard
    simpa only [d1867, d118, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3445 pattern childGuard
    simpa only [d1867, d118, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8642 (pattern : Twelve) (guard : d1867 pattern = 1) : d676 pattern ≤ (0 : Int) + d124 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d676, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8506 pattern childGuard
    simpa only [d676, d124, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d676, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8641 pattern childGuard
    simpa only [d676, d124, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8643 (pattern : Twelve) (guard : d0 pattern = 1) : d159 pattern ≤ (0 : Int) + d117 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c8644 (pattern : Twelve) (guard : d1867 pattern = 1) : d159 pattern ≤ (0 : Int) + d119 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7815 pattern childGuard
    simpa only [d1867, d119, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8643 pattern childGuard
    simpa only [d1867, d119, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8645 (pattern : Twelve) (guard : d1867 pattern = 1) : d677 pattern ≤ (0 : Int) + d125 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d677, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8644 pattern childGuard
    simpa only [d677, d125, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d677, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d677, d125, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8646 (pattern : Twelve) (guard : d1867 pattern = 1) : d707 pattern ≤ (0 : Int) + d133 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d707, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8642 pattern childGuard
    simpa only [d707, d133, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d707, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8645 pattern childGuard
    simpa only [d707, d133, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8647 (pattern : Twelve) (guard : d1867 pattern = 1) : d734 pattern ≤ (0 : Int) + d142 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d734, d142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8568 pattern childGuard
    simpa only [d734, d142, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d734, d142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8646 pattern childGuard
    simpa only [d734, d142, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8648 (pattern : Twelve) (guard : d0 pattern = 1) : d14 pattern ≤ (0 : Int) + d5 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c8649 (pattern : Twelve) (guard : d1867 pattern = 1) : d14 pattern ≤ (0 : Int) + d5 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7908 pattern childGuard
    simpa only [d1867, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8648 pattern childGuard
    simpa only [d1867, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8650 (pattern : Twelve) (guard : d1867 pattern = 1) : d676 pattern ≤ (0 : Int) + d126 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d676, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8506 pattern childGuard
    simpa only [d676, d126, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d676, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8649 pattern childGuard
    simpa only [d676, d126, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8651 (pattern : Twelve) (guard : d1867 pattern = 1) : d677 pattern ≤ (0 : Int) + d47 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d677, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8551 pattern childGuard
    simpa only [d677, d47, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d677, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d677, d47, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8652 (pattern : Twelve) (guard : d1867 pattern = 1) : d707 pattern ≤ (0 : Int) + d134 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d707, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8650 pattern childGuard
    simpa only [d707, d134, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d707, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8651 pattern childGuard
    simpa only [d707, d134, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8653 (pattern : Twelve) (guard : d1867 pattern = 1) : d678 pattern ≤ (0 : Int) + d127 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d678, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8514 pattern childGuard
    simpa only [d678, d127, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d678, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3302 pattern childGuard
    simpa only [d678, d127, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8654 (pattern : Twelve) (guard : d1867 pattern = 1) : d679 pattern ≤ (0 : Int) + d128 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d679, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8503 pattern childGuard
    simpa only [d679, d128, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d679, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d679, d128, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8655 (pattern : Twelve) (guard : d1867 pattern = 1) : d708 pattern ≤ (0 : Int) + d135 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d708, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8653 pattern childGuard
    simpa only [d708, d135, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d708, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8654 pattern childGuard
    simpa only [d708, d135, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8656 (pattern : Twelve) (guard : d1867 pattern = 1) : d735 pattern ≤ (0 : Int) + d143 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d735, d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8652 pattern childGuard
    simpa only [d735, d143, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d735, d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8655 pattern childGuard
    simpa only [d735, d143, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8657 (pattern : Twelve) (guard : d1867 pattern = 1) : d753 pattern ≤ (0 : Int) + d148 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d753, d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8647 pattern childGuard
    simpa only [d753, d148, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d753, d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8656 pattern childGuard
    simpa only [d753, d148, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8658 (pattern : Twelve) (guard : d1867 pattern = 1) : d764 pattern ≤ (0 : Int) + d151 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d764, d151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8640 pattern childGuard
    simpa only [d764, d151, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d764, d151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8657 pattern childGuard
    simpa only [d764, d151, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8659 (pattern : Twelve) (guard : d1867 pattern = 1) : d765 pattern ≤ (0 : Int) + d152 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d765, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8631 pattern childGuard
    simpa only [d765, d152, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d765, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d765, d152, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8660 (pattern : Twelve) (guard : d1867 pattern = 1) : d771 pattern ≤ (0 : Int) + d154 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d771, d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8658 pattern childGuard
    simpa only [d771, d154, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d771, d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8659 pattern childGuard
    simpa only [d771, d154, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8661 (pattern : Twelve) (guard : d1867 pattern = 1) : d774 pattern ≤ (0 : Int) + d155 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d774, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8633 pattern childGuard
    simpa only [d774, d155, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d774, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8660 pattern childGuard
    simpa only [d774, d155, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8662 (pattern : Twelve) (guard : d1867 pattern = 1) : d777 pattern ≤ (0 : Int) + d156 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d777, d156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8619 pattern childGuard
    simpa only [d777, d156, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d777, d156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8661 pattern childGuard
    simpa only [d777, d156, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8663 (pattern : Twelve) (guard : d1867 pattern = 1) : d636 pattern ≤ (0 : Int) + d814 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d636, d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7739 pattern childGuard
    simpa only [d1867, d636, d814, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d636, d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6985 pattern childGuard
    simpa only [d1867, d636, d814, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8664 (pattern : Twelve) (guard : d1867 pattern = 1) : d1183 pattern ≤ (0 : Int) + d816 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1183, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8663 pattern childGuard
    simpa only [d1183, d816, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1183, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8480 pattern childGuard
    simpa only [d1183, d816, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8665 (pattern : Twelve) (guard : d1867 pattern = 1) : d1189 pattern ≤ (0 : Int) + d824 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1189, d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8481 pattern childGuard
    simpa only [d1189, d824, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1189, d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8664 pattern childGuard
    simpa only [d1189, d824, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8666 (pattern : Twelve) (guard : d1867 pattern = 1) : d1199 pattern ≤ (0 : Int) + d838 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1199, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8487 pattern childGuard
    simpa only [d1199, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1199, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8665 pattern childGuard
    simpa only [d1199, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8667 (pattern : Twelve) (guard : d1867 pattern = 1) : d649 pattern ≤ (0 : Int) + d17 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8479 pattern childGuard
    simpa only [d649, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8508 pattern childGuard
    simpa only [d649, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8668 (pattern : Twelve) (guard : d1867 pattern = 1) : d1190 pattern ≤ (0 : Int) + d17 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8667 pattern childGuard
    simpa only [d1190, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8508 pattern childGuard
    simpa only [d1190, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8669 (pattern : Twelve) (guard : d1867 pattern = 1) : d1184 pattern ≤ (0 : Int) + d817 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1184, d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8492 pattern childGuard
    simpa only [d1184, d817, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1184, d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8573 pattern childGuard
    simpa only [d1184, d817, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8670 (pattern : Twelve) (guard : d1867 pattern = 1) : d1191 pattern ≤ (0 : Int) + d825 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1191, d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8669 pattern childGuard
    simpa only [d1191, d825, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1191, d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8574 pattern childGuard
    simpa only [d1191, d825, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8671 (pattern : Twelve) (guard : d1867 pattern = 1) : d1200 pattern ≤ (0 : Int) + d839 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1200, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8668 pattern childGuard
    simpa only [d1200, d839, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1200, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8670 pattern childGuard
    simpa only [d1200, d839, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8672 (pattern : Twelve) (guard : d1867 pattern = 1) : d1216 pattern ≤ (0 : Int) + d853 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1216, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8666 pattern childGuard
    simpa only [d1216, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1216, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8671 pattern childGuard
    simpa only [d1216, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8673 (pattern : Twelve) (guard : d1867 pattern = 1) : d1192 pattern ≤ (0 : Int) + d56 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1192, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8507 pattern childGuard
    simpa only [d1192, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1192, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8533 pattern childGuard
    simpa only [d1192, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8674 (pattern : Twelve) (guard : d1867 pattern = 1) : d651 pattern ≤ (0 : Int) + d818 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d651, d818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8663 pattern childGuard
    simpa only [d651, d818, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d651, d818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d651, d818, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8675 (pattern : Twelve) (guard : d1867 pattern = 1) : d687 pattern ≤ (0 : Int) + d826 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d687, d826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8515 pattern childGuard
    simpa only [d687, d826, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d687, d826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8674 pattern childGuard
    simpa only [d687, d826, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8676 (pattern : Twelve) (guard : d1867 pattern = 1) : d1201 pattern ≤ (0 : Int) + d840 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1201, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8673 pattern childGuard
    simpa only [d1201, d840, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1201, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8675 pattern childGuard
    simpa only [d1201, d840, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8677 (pattern : Twelve) (guard : d1867 pattern = 1) : d692 pattern ≤ (0 : Int) + d827 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d692, d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8515 pattern childGuard
    simpa only [d692, d827, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d692, d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8536 pattern childGuard
    simpa only [d692, d827, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8678 (pattern : Twelve) (guard : d1867 pattern = 1) : d1202 pattern ≤ (0 : Int) + d841 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1202, d841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8677 pattern childGuard
    simpa only [d1202, d841, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1202, d841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8670 pattern childGuard
    simpa only [d1202, d841, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8679 (pattern : Twelve) (guard : d1867 pattern = 1) : d1217 pattern ≤ (0 : Int) + d854 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1217, d854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8676 pattern childGuard
    simpa only [d1217, d854, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1217, d854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8678 pattern childGuard
    simpa only [d1217, d854, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
