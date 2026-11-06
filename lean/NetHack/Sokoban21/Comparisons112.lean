/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons111
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c15680 (pattern : Twelve) (guard : d477 pattern = 1) : d33 pattern ≤ (1 : Int) + d2602 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d33, d2602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15655 pattern childGuard
    simpa only [d33, d2602, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d33, d2602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15679 pattern childGuard
    simpa only [d33, d2602, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15681 (pattern : Twelve) (guard : d477 pattern = 1) : d54 pattern ≤ (1 : Int) + d2603 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d54, d2603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15671 pattern childGuard
    simpa only [d54, d2603, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d54, d2603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15680 pattern childGuard
    simpa only [d54, d2603, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15682 (pattern : Twelve) (guard : d0 pattern = 1) : d2 pattern ≤ (1 : Int) + d2 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15683 (pattern : Twelve) (guard : d477 pattern = 1) : d23 pattern ≤ (1 : Int) + d2 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d477, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15682 pattern childGuard
    simpa only [d477, d23, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d477, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15185 pattern childGuard
    simpa only [d477, d23, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15684 (pattern : Twelve) (guard : d477 pattern = 1) : d34 pattern ≤ (1 : Int) + d30 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d34, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15657 pattern childGuard
    simpa only [d34, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d34, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15683 pattern childGuard
    simpa only [d34, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15685 (pattern : Twelve) (guard : d477 pattern = 1) : d55 pattern ≤ (1 : Int) + d2604 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d55, d2604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15684 pattern childGuard
    simpa only [d55, d2604, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d55, d2604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15667 pattern childGuard
    simpa only [d55, d2604, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15686 (pattern : Twelve) (guard : d477 pattern = 1) : d75 pattern ≤ (1 : Int) + d2605 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d75, d2605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15681 pattern childGuard
    simpa only [d75, d2605, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d75, d2605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15685 pattern childGuard
    simpa only [d75, d2605, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15687 (pattern : Twelve) (guard : d477 pattern = 1) : d92 pattern ≤ (1 : Int) + d2606 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d92, d2606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15678 pattern childGuard
    simpa only [d92, d2606, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d92, d2606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15686 pattern childGuard
    simpa only [d92, d2606, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15688 (pattern : Twelve) (guard : d477 pattern = 1) : d102 pattern ≤ (1 : Int) + d2607 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d102, d2607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15670 pattern childGuard
    simpa only [d102, d2607, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d102, d2607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15687 pattern childGuard
    simpa only [d102, d2607, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15689 (pattern : Twelve) (guard : d477 pattern = 1) : d76 pattern ≤ (1 : Int) + d2608 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d76, d2608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15655 pattern childGuard
    simpa only [d76, d2608, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d76, d2608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15685 pattern childGuard
    simpa only [d76, d2608, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15690 (pattern : Twelve) (guard : d477 pattern = 1) : d93 pattern ≤ (1 : Int) + d2609 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d93, d2609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15661 pattern childGuard
    simpa only [d93, d2609, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d93, d2609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15689 pattern childGuard
    simpa only [d93, d2609, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15691 (pattern : Twelve) (guard : d477 pattern = 1) : d56 pattern ≤ (1 : Int) + d56 pattern := by
  omega
theorem c15692 (pattern : Twelve) (guard : d477 pattern = 1) : d36 pattern ≤ (1 : Int) + d35 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d36, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15657 pattern childGuard
    simpa only [d36, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d36, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15666 pattern childGuard
    simpa only [d36, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15693 (pattern : Twelve) (guard : d477 pattern = 1) : d57 pattern ≤ (1 : Int) + d56 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d57, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15671 pattern childGuard
    simpa only [d57, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d57, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15692 pattern childGuard
    simpa only [d57, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15694 (pattern : Twelve) (guard : d477 pattern = 1) : d77 pattern ≤ (1 : Int) + d56 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15691 pattern childGuard
    simpa only [d77, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15693 pattern childGuard
    simpa only [d77, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15695 (pattern : Twelve) (guard : d477 pattern = 1) : d78 pattern ≤ (1 : Int) + d2610 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d78, d2610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15691 pattern childGuard
    simpa only [d78, d2610, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d78, d2610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15685 pattern childGuard
    simpa only [d78, d2610, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15696 (pattern : Twelve) (guard : d477 pattern = 1) : d94 pattern ≤ (1 : Int) + d2611 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d94, d2611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15694 pattern childGuard
    simpa only [d94, d2611, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d94, d2611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15695 pattern childGuard
    simpa only [d94, d2611, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15697 (pattern : Twelve) (guard : d477 pattern = 1) : d103 pattern ≤ (1 : Int) + d2612 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d103, d2612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15690 pattern childGuard
    simpa only [d103, d2612, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d103, d2612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15696 pattern childGuard
    simpa only [d103, d2612, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15698 (pattern : Twelve) (guard : d477 pattern = 1) : d110 pattern ≤ (1 : Int) + d2613 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d110, d2613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15688 pattern childGuard
    simpa only [d110, d2613, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d110, d2613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15697 pattern childGuard
    simpa only [d110, d2613, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15699 (pattern : Twelve) (guard : d477 pattern = 1) : d3 pattern ≤ (1 : Int) + d3 pattern := by
  omega
theorem c15700 (pattern : Twelve) (guard : d477 pattern = 1) : d37 pattern ≤ (1 : Int) + d123 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d37, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15657 pattern childGuard
    simpa only [d37, d123, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d37, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15699 pattern childGuard
    simpa only [d37, d123, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15701 (pattern : Twelve) (guard : d477 pattern = 1) : d58 pattern ≤ (1 : Int) + d132 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d58, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15671 pattern childGuard
    simpa only [d58, d132, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d58, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15700 pattern childGuard
    simpa only [d58, d132, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15702 (pattern : Twelve) (guard : d477 pattern = 1) : d79 pattern ≤ (1 : Int) + d2614 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d79, d2614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15671 pattern childGuard
    simpa only [d79, d2614, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d79, d2614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15701 pattern childGuard
    simpa only [d79, d2614, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15703 (pattern : Twelve) (guard : d477 pattern = 1) : d80 pattern ≤ (1 : Int) + d2615 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d80, d2615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15671 pattern childGuard
    simpa only [d80, d2615, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d80, d2615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15685 pattern childGuard
    simpa only [d80, d2615, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15704 (pattern : Twelve) (guard : d477 pattern = 1) : d95 pattern ≤ (1 : Int) + d2616 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d95, d2616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15702 pattern childGuard
    simpa only [d95, d2616, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d95, d2616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15703 pattern childGuard
    simpa only [d95, d2616, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15705 (pattern : Twelve) (guard : d477 pattern = 1) : d59 pattern ≤ (1 : Int) + d59 pattern := by
  omega
theorem c15706 (pattern : Twelve) (guard : d477 pattern = 1) : d38 pattern ≤ (1 : Int) + d38 pattern := by
  omega
theorem c15707 (pattern : Twelve) (guard : d477 pattern = 1) : d40 pattern ≤ (1 : Int) + d39 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d40, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15683 pattern childGuard
    simpa only [d40, d39, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d40, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15666 pattern childGuard
    simpa only [d40, d39, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15708 (pattern : Twelve) (guard : d477 pattern = 1) : d60 pattern ≤ (1 : Int) + d59 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d60, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15706 pattern childGuard
    simpa only [d60, d59, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d60, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15707 pattern childGuard
    simpa only [d60, d59, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15709 (pattern : Twelve) (guard : d477 pattern = 1) : d81 pattern ≤ (1 : Int) + d59 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15705 pattern childGuard
    simpa only [d81, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15708 pattern childGuard
    simpa only [d81, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15710 (pattern : Twelve) (guard : d0 pattern = 1) : d4 pattern ≤ (1 : Int) + d4 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15711 (pattern : Twelve) (guard : d477 pattern = 1) : d24 pattern ≤ (1 : Int) + d4 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d477, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15710 pattern childGuard
    simpa only [d477, d24, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d477, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15526 pattern childGuard
    simpa only [d477, d24, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15712 (pattern : Twelve) (guard : d477 pattern = 1) : d41 pattern ≤ (1 : Int) + d38 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d41, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15683 pattern childGuard
    simpa only [d41, d38, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d41, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15711 pattern childGuard
    simpa only [d41, d38, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15713 (pattern : Twelve) (guard : d477 pattern = 1) : d25 pattern ≤ (1 : Int) + d16 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d477, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12892 pattern childGuard
    simpa only [d477, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d477, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11196 pattern childGuard
    simpa only [d477, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15714 (pattern : Twelve) (guard : d477 pattern = 1) : d42 pattern ≤ (1 : Int) + d2237 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d42, d2237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15713 pattern childGuard
    simpa only [d42, d2237, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d42, d2237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15666 pattern childGuard
    simpa only [d42, d2237, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15715 (pattern : Twelve) (guard : d477 pattern = 1) : d61 pattern ≤ (1 : Int) + d2617 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d61, d2617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15712 pattern childGuard
    simpa only [d61, d2617, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d61, d2617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15714 pattern childGuard
    simpa only [d61, d2617, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15716 (pattern : Twelve) (guard : d477 pattern = 1) : d82 pattern ≤ (1 : Int) + d2618 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d82, d2618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15705 pattern childGuard
    simpa only [d82, d2618, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d82, d2618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15715 pattern childGuard
    simpa only [d82, d2618, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15717 (pattern : Twelve) (guard : d477 pattern = 1) : d96 pattern ≤ (1 : Int) + d2619 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d96, d2619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15709 pattern childGuard
    simpa only [d96, d2619, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d96, d2619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15716 pattern childGuard
    simpa only [d96, d2619, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15718 (pattern : Twelve) (guard : d477 pattern = 1) : d104 pattern ≤ (1 : Int) + d2620 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d104, d2620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15704 pattern childGuard
    simpa only [d104, d2620, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d104, d2620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15717 pattern childGuard
    simpa only [d104, d2620, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15719 (pattern : Twelve) (guard : d477 pattern = 1) : d105 pattern ≤ (1 : Int) + d2621 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d105, d2621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15696 pattern childGuard
    simpa only [d105, d2621, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d105, d2621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15666 pattern childGuard
    simpa only [d105, d2621, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15720 (pattern : Twelve) (guard : d477 pattern = 1) : d111 pattern ≤ (1 : Int) + d2622 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d111, d2622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15718 pattern childGuard
    simpa only [d111, d2622, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d111, d2622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15719 pattern childGuard
    simpa only [d111, d2622, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15721 (pattern : Twelve) (guard : d477 pattern = 1) : d114 pattern ≤ (1 : Int) + d2623 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d114, d2623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15698 pattern childGuard
    simpa only [d114, d2623, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d114, d2623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15720 pattern childGuard
    simpa only [d114, d2623, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15722 (pattern : Twelve) (guard : d477 pattern = 1) : d120 pattern ≤ (1 : Int) + d2624 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d120, d2624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15657 pattern childGuard
    simpa only [d120, d2624, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d120, d2624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15713 pattern childGuard
    simpa only [d120, d2624, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15723 (pattern : Twelve) (guard : d477 pattern = 1) : d129 pattern ≤ (1 : Int) + d2625 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d129, d2625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15722 pattern childGuard
    simpa only [d129, d2625, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d129, d2625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15667 pattern childGuard
    simpa only [d129, d2625, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15724 (pattern : Twelve) (guard : d477 pattern = 1) : d136 pattern ≤ (1 : Int) + d2626 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d136, d2626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15655 pattern childGuard
    simpa only [d136, d2626, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d136, d2626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15723 pattern childGuard
    simpa only [d136, d2626, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15725 (pattern : Twelve) (guard : d477 pattern = 1) : d144 pattern ≤ (1 : Int) + d2627 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d144, d2627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15661 pattern childGuard
    simpa only [d144, d2627, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d144, d2627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15724 pattern childGuard
    simpa only [d144, d2627, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15726 (pattern : Twelve) (guard : d477 pattern = 1) : d121 pattern ≤ (1 : Int) + d30 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d121, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15655 pattern childGuard
    simpa only [d121, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d121, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15683 pattern childGuard
    simpa only [d121, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15727 (pattern : Twelve) (guard : d477 pattern = 1) : d130 pattern ≤ (1 : Int) + d56 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d130, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15726 pattern childGuard
    simpa only [d130, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d130, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15692 pattern childGuard
    simpa only [d130, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15728 (pattern : Twelve) (guard : d477 pattern = 1) : d137 pattern ≤ (1 : Int) + d2628 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d137, d2628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15674 pattern childGuard
    simpa only [d137, d2628, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d137, d2628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15727 pattern childGuard
    simpa only [d137, d2628, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15729 (pattern : Twelve) (guard : d477 pattern = 1) : d138 pattern ≤ (1 : Int) + d2629 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d138, d2629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15691 pattern childGuard
    simpa only [d138, d2629, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d138, d2629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15723 pattern childGuard
    simpa only [d138, d2629, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15730 (pattern : Twelve) (guard : d477 pattern = 1) : d145 pattern ≤ (1 : Int) + d2630 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d145, d2630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15728 pattern childGuard
    simpa only [d145, d2630, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d145, d2630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15729 pattern childGuard
    simpa only [d145, d2630, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15731 (pattern : Twelve) (guard : d477 pattern = 1) : d149 pattern ≤ (1 : Int) + d2631 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d149, d2631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15725 pattern childGuard
    simpa only [d149, d2631, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d149, d2631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15730 pattern childGuard
    simpa only [d149, d2631, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15732 (pattern : Twelve) (guard : d477 pattern = 1) : d139 pattern ≤ (1 : Int) + d56 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15691 pattern childGuard
    simpa only [d139, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15727 pattern childGuard
    simpa only [d139, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15733 (pattern : Twelve) (guard : d477 pattern = 1) : d146 pattern ≤ (1 : Int) + d2632 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d146, d2632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15732 pattern childGuard
    simpa only [d146, d2632, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d146, d2632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15729 pattern childGuard
    simpa only [d146, d2632, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15734 (pattern : Twelve) (guard : d477 pattern = 1) : d150 pattern ≤ (1 : Int) + d2633 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d150, d2633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15725 pattern childGuard
    simpa only [d150, d2633, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d150, d2633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15733 pattern childGuard
    simpa only [d150, d2633, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15735 (pattern : Twelve) (guard : d477 pattern = 1) : d153 pattern ≤ (1 : Int) + d2634 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d153, d2634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15731 pattern childGuard
    simpa only [d153, d2634, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d153, d2634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15734 pattern childGuard
    simpa only [d153, d2634, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15736 (pattern : Twelve) (guard : d477 pattern = 1) : d4 pattern ≤ (1 : Int) + d4 pattern := by
  omega
theorem c15737 (pattern : Twelve) (guard : d477 pattern = 1) : d122 pattern ≤ (1 : Int) + d2635 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d122, d2635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15657 pattern childGuard
    simpa only [d122, d2635, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d122, d2635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15736 pattern childGuard
    simpa only [d122, d2635, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15738 (pattern : Twelve) (guard : d477 pattern = 1) : d131 pattern ≤ (1 : Int) + d2636 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d131, d2636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15726 pattern childGuard
    simpa only [d131, d2636, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d131, d2636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15737 pattern childGuard
    simpa only [d131, d2636, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15739 (pattern : Twelve) (guard : d477 pattern = 1) : d140 pattern ≤ (1 : Int) + d2637 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d140, d2637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15671 pattern childGuard
    simpa only [d140, d2637, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d140, d2637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15738 pattern childGuard
    simpa only [d140, d2637, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15740 (pattern : Twelve) (guard : d477 pattern = 1) : d132 pattern ≤ (1 : Int) + d132 pattern := by
  omega
theorem c15741 (pattern : Twelve) (guard : d477 pattern = 1) : d141 pattern ≤ (1 : Int) + d2638 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d141, d2638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15740 pattern childGuard
    simpa only [d141, d2638, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d141, d2638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15723 pattern childGuard
    simpa only [d141, d2638, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15742 (pattern : Twelve) (guard : d477 pattern = 1) : d147 pattern ≤ (1 : Int) + d2639 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d147, d2639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15739 pattern childGuard
    simpa only [d147, d2639, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d147, d2639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15741 pattern childGuard
    simpa only [d147, d2639, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15743 (pattern : Twelve) (guard : d477 pattern = 1) : d2 pattern ≤ (1 : Int) + d2 pattern := by
  omega
theorem c15744 (pattern : Twelve) (guard : d0 pattern = 1) : d5 pattern ≤ (1 : Int) + d5 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15745 (pattern : Twelve) (guard : d477 pattern = 1) : d118 pattern ≤ (1 : Int) + d5 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d477, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15744 pattern childGuard
    simpa only [d477, d118, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d477, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15217 pattern childGuard
    simpa only [d477, d118, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15746 (pattern : Twelve) (guard : d477 pattern = 1) : d124 pattern ≤ (1 : Int) + d126 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d124, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15743 pattern childGuard
    simpa only [d124, d126, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d124, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15745 pattern childGuard
    simpa only [d124, d126, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15747 (pattern : Twelve) (guard : d477 pattern = 1) : d119 pattern ≤ (1 : Int) + d3 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d477, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12806 pattern childGuard
    simpa only [d477, d119, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d477, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15220 pattern childGuard
    simpa only [d477, d119, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15748 (pattern : Twelve) (guard : d477 pattern = 1) : d125 pattern ≤ (1 : Int) + d47 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d125, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15747 pattern childGuard
    simpa only [d125, d47, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d125, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15666 pattern childGuard
    simpa only [d125, d47, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15749 (pattern : Twelve) (guard : d477 pattern = 1) : d133 pattern ≤ (1 : Int) + d134 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d133, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15746 pattern childGuard
    simpa only [d133, d134, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d133, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15748 pattern childGuard
    simpa only [d133, d134, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15750 (pattern : Twelve) (guard : d477 pattern = 1) : d142 pattern ≤ (1 : Int) + d2640 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d142, d2640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15705 pattern childGuard
    simpa only [d142, d2640, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d142, d2640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15749 pattern childGuard
    simpa only [d142, d2640, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15751 (pattern : Twelve) (guard : d477 pattern = 1) : d134 pattern ≤ (1 : Int) + d134 pattern := by
  omega
theorem c15752 (pattern : Twelve) (guard : d477 pattern = 1) : d127 pattern ≤ (1 : Int) + d2115 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d127, d2115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15683 pattern childGuard
    simpa only [d127, d2115, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d127, d2115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15679 pattern childGuard
    simpa only [d127, d2115, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15753 (pattern : Twelve) (guard : d477 pattern = 1) : d128 pattern ≤ (1 : Int) + d2088 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d128, d2088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15672 pattern childGuard
    simpa only [d128, d2088, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d128, d2088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15666 pattern childGuard
    simpa only [d128, d2088, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15754 (pattern : Twelve) (guard : d477 pattern = 1) : d135 pattern ≤ (1 : Int) + d2641 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d135, d2641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15752 pattern childGuard
    simpa only [d135, d2641, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d135, d2641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15753 pattern childGuard
    simpa only [d135, d2641, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15755 (pattern : Twelve) (guard : d477 pattern = 1) : d143 pattern ≤ (1 : Int) + d2642 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d143, d2642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15751 pattern childGuard
    simpa only [d143, d2642, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d143, d2642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15754 pattern childGuard
    simpa only [d143, d2642, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15756 (pattern : Twelve) (guard : d477 pattern = 1) : d148 pattern ≤ (1 : Int) + d2643 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d148, d2643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15750 pattern childGuard
    simpa only [d148, d2643, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d148, d2643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15755 pattern childGuard
    simpa only [d148, d2643, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15757 (pattern : Twelve) (guard : d477 pattern = 1) : d151 pattern ≤ (1 : Int) + d2644 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d151, d2644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15742 pattern childGuard
    simpa only [d151, d2644, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d151, d2644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15756 pattern childGuard
    simpa only [d151, d2644, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15758 (pattern : Twelve) (guard : d477 pattern = 1) : d152 pattern ≤ (1 : Int) + d2645 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d152, d2645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15733 pattern childGuard
    simpa only [d152, d2645, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d152, d2645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15666 pattern childGuard
    simpa only [d152, d2645, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15759 (pattern : Twelve) (guard : d477 pattern = 1) : d154 pattern ≤ (1 : Int) + d2646 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d154, d2646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15757 pattern childGuard
    simpa only [d154, d2646, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d154, d2646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15758 pattern childGuard
    simpa only [d154, d2646, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15760 (pattern : Twelve) (guard : d477 pattern = 1) : d155 pattern ≤ (1 : Int) + d2647 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d155, d2647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15735 pattern childGuard
    simpa only [d155, d2647, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d155, d2647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15759 pattern childGuard
    simpa only [d155, d2647, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15761 (pattern : Twelve) (guard : d477 pattern = 1) : d156 pattern ≤ (1 : Int) + d2648 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d156, d2648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15721 pattern childGuard
    simpa only [d156, d2648, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d156, d2648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15760 pattern childGuard
    simpa only [d156, d2648, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15762 (pattern : Twelve) (guard : d477 pattern = 1) : d814 pattern ≤ (1 : Int) + d7 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d477, d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12675 pattern childGuard
    simpa only [d477, d814, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d477, d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15233 pattern childGuard
    simpa only [d477, d814, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15763 (pattern : Twelve) (guard : d477 pattern = 1) : d816 pattern ≤ (1 : Int) + d2057 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d816, d2057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15762 pattern childGuard
    simpa only [d816, d2057, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d816, d2057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15658 pattern childGuard
    simpa only [d816, d2057, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15764 (pattern : Twelve) (guard : d477 pattern = 1) : d824 pattern ≤ (1 : Int) + d2058 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d824, d2058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15659 pattern childGuard
    simpa only [d824, d2058, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d824, d2058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15763 pattern childGuard
    simpa only [d824, d2058, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15765 (pattern : Twelve) (guard : d477 pattern = 1) : d838 pattern ≤ (1 : Int) + d2059 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d838, d2059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15655 pattern childGuard
    simpa only [d838, d2059, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d838, d2059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15764 pattern childGuard
    simpa only [d838, d2059, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15766 (pattern : Twelve) (guard : d477 pattern = 1) : d817 pattern ≤ (1 : Int) + d2649 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d817, d2649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15665 pattern childGuard
    simpa only [d817, d2649, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d817, d2649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15713 pattern childGuard
    simpa only [d817, d2649, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15767 (pattern : Twelve) (guard : d477 pattern = 1) : d825 pattern ≤ (1 : Int) + d2650 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d825, d2650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15766 pattern childGuard
    simpa only [d825, d2650, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d825, d2650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15714 pattern childGuard
    simpa only [d825, d2650, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15768 (pattern : Twelve) (guard : d477 pattern = 1) : d839 pattern ≤ (1 : Int) + d2651 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d839, d2651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15657 pattern childGuard
    simpa only [d839, d2651, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d839, d2651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15767 pattern childGuard
    simpa only [d839, d2651, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15769 (pattern : Twelve) (guard : d477 pattern = 1) : d853 pattern ≤ (1 : Int) + d2652 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d853, d2652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15765 pattern childGuard
    simpa only [d853, d2652, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d853, d2652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15768 pattern childGuard
    simpa only [d853, d2652, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15770 (pattern : Twelve) (guard : d477 pattern = 1) : d818 pattern ≤ (1 : Int) + d2073 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d818, d2073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15762 pattern childGuard
    simpa only [d818, d2073, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d818, d2073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15666 pattern childGuard
    simpa only [d818, d2073, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15771 (pattern : Twelve) (guard : d477 pattern = 1) : d826 pattern ≤ (1 : Int) + d2074 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d826, d2074, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15684 pattern childGuard
    simpa only [d826, d2074, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d826, d2074, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15770 pattern childGuard
    simpa only [d826, d2074, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15772 (pattern : Twelve) (guard : d477 pattern = 1) : d840 pattern ≤ (1 : Int) + d2075 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d840, d2075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15691 pattern childGuard
    simpa only [d840, d2075, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d840, d2075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15771 pattern childGuard
    simpa only [d840, d2075, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15773 (pattern : Twelve) (guard : d477 pattern = 1) : d827 pattern ≤ (1 : Int) + d56 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d827, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15684 pattern childGuard
    simpa only [d827, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d827, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15692 pattern childGuard
    simpa only [d827, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15774 (pattern : Twelve) (guard : d477 pattern = 1) : d841 pattern ≤ (1 : Int) + d2653 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d841, d2653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15773 pattern childGuard
    simpa only [d841, d2653, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d841, d2653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15767 pattern childGuard
    simpa only [d841, d2653, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15775 (pattern : Twelve) (guard : d477 pattern = 1) : d854 pattern ≤ (1 : Int) + d2654 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d854, d2654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15772 pattern childGuard
    simpa only [d854, d2654, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d854, d2654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15774 pattern childGuard
    simpa only [d854, d2654, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15776 (pattern : Twelve) (guard : d477 pattern = 1) : d861 pattern ≤ (1 : Int) + d2655 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d861, d2655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15769 pattern childGuard
    simpa only [d861, d2655, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d861, d2655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15775 pattern childGuard
    simpa only [d861, d2655, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15777 (pattern : Twelve) (guard : d477 pattern = 1) : d819 pattern ≤ (1 : Int) + d2079 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d819, d2079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15762 pattern childGuard
    simpa only [d819, d2079, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d819, d2079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15699 pattern childGuard
    simpa only [d819, d2079, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15778 (pattern : Twelve) (guard : d477 pattern = 1) : d828 pattern ≤ (1 : Int) + d2080 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d828, d2080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15684 pattern childGuard
    simpa only [d828, d2080, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d828, d2080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15777 pattern childGuard
    simpa only [d828, d2080, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15779 (pattern : Twelve) (guard : d477 pattern = 1) : d842 pattern ≤ (1 : Int) + d2081 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d842, d2081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15671 pattern childGuard
    simpa only [d842, d2081, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d842, d2081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15778 pattern childGuard
    simpa only [d842, d2081, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15780 (pattern : Twelve) (guard : d477 pattern = 1) : d843 pattern ≤ (1 : Int) + d2656 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d843, d2656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15684 pattern childGuard
    simpa only [d843, d2656, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d843, d2656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15767 pattern childGuard
    simpa only [d843, d2656, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15781 (pattern : Twelve) (guard : d477 pattern = 1) : d855 pattern ≤ (1 : Int) + d2657 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d855, d2657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15779 pattern childGuard
    simpa only [d855, d2657, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d855, d2657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15780 pattern childGuard
    simpa only [d855, d2657, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15782 (pattern : Twelve) (guard : d477 pattern = 1) : d815 pattern ≤ (1 : Int) + d9 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d477, d815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12682 pattern childGuard
    simpa only [d477, d815, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d477, d815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11191 pattern childGuard
    simpa only [d477, d815, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15783 (pattern : Twelve) (guard : d477 pattern = 1) : d820 pattern ≤ (1 : Int) + d2084 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d820, d2084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15782 pattern childGuard
    simpa only [d820, d2084, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d820, d2084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15666 pattern childGuard
    simpa only [d820, d2084, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15784 (pattern : Twelve) (guard : d477 pattern = 1) : d829 pattern ≤ (1 : Int) + d2085 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d829, d2085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15712 pattern childGuard
    simpa only [d829, d2085, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d829, d2085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15783 pattern childGuard
    simpa only [d829, d2085, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15785 (pattern : Twelve) (guard : d477 pattern = 1) : d844 pattern ≤ (1 : Int) + d2086 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d844, d2086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15705 pattern childGuard
    simpa only [d844, d2086, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d844, d2086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15784 pattern childGuard
    simpa only [d844, d2086, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15786 (pattern : Twelve) (guard : d477 pattern = 1) : d830 pattern ≤ (1 : Int) + d59 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d830, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15712 pattern childGuard
    simpa only [d830, d59, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d830, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15707 pattern childGuard
    simpa only [d830, d59, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15787 (pattern : Twelve) (guard : d477 pattern = 1) : d821 pattern ≤ (1 : Int) + d2236 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d821, d2236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15713 pattern childGuard
    simpa only [d821, d2236, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d821, d2236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15675 pattern childGuard
    simpa only [d821, d2236, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15788 (pattern : Twelve) (guard : d477 pattern = 1) : d822 pattern ≤ (1 : Int) + d2119 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d822, d2119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15675 pattern childGuard
    simpa only [d822, d2119, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d822, d2119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15666 pattern childGuard
    simpa only [d822, d2119, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15789 (pattern : Twelve) (guard : d477 pattern = 1) : d831 pattern ≤ (1 : Int) + d2658 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d831, d2658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15787 pattern childGuard
    simpa only [d831, d2658, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d831, d2658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15788 pattern childGuard
    simpa only [d831, d2658, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15790 (pattern : Twelve) (guard : d477 pattern = 1) : d845 pattern ≤ (1 : Int) + d2659 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d845, d2659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15786 pattern childGuard
    simpa only [d845, d2659, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d845, d2659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15789 pattern childGuard
    simpa only [d845, d2659, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15791 (pattern : Twelve) (guard : d477 pattern = 1) : d856 pattern ≤ (1 : Int) + d2660 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d856, d2660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15785 pattern childGuard
    simpa only [d856, d2660, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d856, d2660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15790 pattern childGuard
    simpa only [d856, d2660, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15792 (pattern : Twelve) (guard : d477 pattern = 1) : d862 pattern ≤ (1 : Int) + d2661 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d862, d2661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15781 pattern childGuard
    simpa only [d862, d2661, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d862, d2661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15791 pattern childGuard
    simpa only [d862, d2661, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15793 (pattern : Twelve) (guard : d477 pattern = 1) : d863 pattern ≤ (1 : Int) + d2662 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d863, d2662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15775 pattern childGuard
    simpa only [d863, d2662, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d863, d2662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15666 pattern childGuard
    simpa only [d863, d2662, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15794 (pattern : Twelve) (guard : d477 pattern = 1) : d867 pattern ≤ (1 : Int) + d2663 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d867, d2663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15792 pattern childGuard
    simpa only [d867, d2663, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d867, d2663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15793 pattern childGuard
    simpa only [d867, d2663, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15795 (pattern : Twelve) (guard : d477 pattern = 1) : d869 pattern ≤ (1 : Int) + d2664 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d869, d2664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15776 pattern childGuard
    simpa only [d869, d2664, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d869, d2664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15794 pattern childGuard
    simpa only [d869, d2664, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15796 (pattern : Twelve) (guard : d1 pattern = 1) : d8 pattern ≤ (1 : Int) + d1 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11212 pattern childGuard
    simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12013 pattern childGuard
    simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15797 (pattern : Twelve) (guard : d477 pattern = 1) : d872 pattern ≤ (1 : Int) + d1 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d477, d872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12785 pattern childGuard
    simpa only [d477, d872, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d477, d872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15796 pattern childGuard
    simpa only [d477, d872, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15798 (pattern : Twelve) (guard : d477 pattern = 1) : d874 pattern ≤ (1 : Int) + d26 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d874, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15657 pattern childGuard
    simpa only [d874, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d874, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15797 pattern childGuard
    simpa only [d874, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15799 (pattern : Twelve) (guard : d477 pattern = 1) : d875 pattern ≤ (1 : Int) + d2057 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d875, d2057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15762 pattern childGuard
    simpa only [d875, d2057, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d875, d2057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15797 pattern childGuard
    simpa only [d875, d2057, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15800 (pattern : Twelve) (guard : d477 pattern = 1) : d882 pattern ≤ (1 : Int) + d2058 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d882, d2058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15798 pattern childGuard
    simpa only [d882, d2058, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d882, d2058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15799 pattern childGuard
    simpa only [d882, d2058, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15801 (pattern : Twelve) (guard : d477 pattern = 1) : d890 pattern ≤ (1 : Int) + d2059 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d890, d2059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15655 pattern childGuard
    simpa only [d890, d2059, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d890, d2059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15800 pattern childGuard
    simpa only [d890, d2059, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15802 (pattern : Twelve) (guard : d477 pattern = 1) : d876 pattern ≤ (1 : Int) + d2665 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d876, d2665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15665 pattern childGuard
    simpa only [d876, d2665, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d876, d2665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15675 pattern childGuard
    simpa only [d876, d2665, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15803 (pattern : Twelve) (guard : d477 pattern = 1) : d883 pattern ≤ (1 : Int) + d2666 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d883, d2666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15802 pattern childGuard
    simpa only [d883, d2666, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d883, d2666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15714 pattern childGuard
    simpa only [d883, d2666, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15804 (pattern : Twelve) (guard : d477 pattern = 1) : d891 pattern ≤ (1 : Int) + d2667 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d891, d2667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15657 pattern childGuard
    simpa only [d891, d2667, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d891, d2667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15803 pattern childGuard
    simpa only [d891, d2667, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15805 (pattern : Twelve) (guard : d477 pattern = 1) : d898 pattern ≤ (1 : Int) + d2668 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d898, d2668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15801 pattern childGuard
    simpa only [d898, d2668, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d898, d2668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15804 pattern childGuard
    simpa only [d898, d2668, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15806 (pattern : Twelve) (guard : d477 pattern = 1) : d877 pattern ≤ (1 : Int) + d2100 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d877, d2100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15657 pattern childGuard
    simpa only [d877, d2100, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d877, d2100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15782 pattern childGuard
    simpa only [d877, d2100, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15807 (pattern : Twelve) (guard : d477 pattern = 1) : d884 pattern ≤ (1 : Int) + d2101 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d884, d2101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15806 pattern childGuard
    simpa only [d884, d2101, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d884, d2101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15770 pattern childGuard
    simpa only [d884, d2101, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15808 (pattern : Twelve) (guard : d477 pattern = 1) : d892 pattern ≤ (1 : Int) + d2106 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d892, d2106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15691 pattern childGuard
    simpa only [d892, d2106, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d892, d2106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15807 pattern childGuard
    simpa only [d892, d2106, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15809 (pattern : Twelve) (guard : d477 pattern = 1) : d893 pattern ≤ (1 : Int) + d2669 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d893, d2669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15773 pattern childGuard
    simpa only [d893, d2669, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d893, d2669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15803 pattern childGuard
    simpa only [d893, d2669, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15810 (pattern : Twelve) (guard : d477 pattern = 1) : d899 pattern ≤ (1 : Int) + d2670 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d899, d2670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15808 pattern childGuard
    simpa only [d899, d2670, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d899, d2670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15809 pattern childGuard
    simpa only [d899, d2670, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15811 (pattern : Twelve) (guard : d477 pattern = 1) : d902 pattern ≤ (1 : Int) + d2671 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d902, d2671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15805 pattern childGuard
    simpa only [d902, d2671, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d902, d2671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15810 pattern childGuard
    simpa only [d902, d2671, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15812 (pattern : Twelve) (guard : d477 pattern = 1) : d878 pattern ≤ (1 : Int) + d2110 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d878, d2110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15762 pattern childGuard
    simpa only [d878, d2110, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d878, d2110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15711 pattern childGuard
    simpa only [d878, d2110, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15813 (pattern : Twelve) (guard : d477 pattern = 1) : d885 pattern ≤ (1 : Int) + d2111 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d885, d2111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15806 pattern childGuard
    simpa only [d885, d2111, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d885, d2111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15812 pattern childGuard
    simpa only [d885, d2111, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15814 (pattern : Twelve) (guard : d477 pattern = 1) : d894 pattern ≤ (1 : Int) + d2112 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d894, d2112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15671 pattern childGuard
    simpa only [d894, d2112, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d894, d2112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15813 pattern childGuard
    simpa only [d894, d2112, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15815 (pattern : Twelve) (guard : d477 pattern = 1) : d879 pattern ≤ (1 : Int) + d123 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d879, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15657 pattern childGuard
    simpa only [d879, d123, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d879, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15747 pattern childGuard
    simpa only [d879, d123, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15816 (pattern : Twelve) (guard : d477 pattern = 1) : d886 pattern ≤ (1 : Int) + d132 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d886, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15684 pattern childGuard
    simpa only [d886, d132, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d886, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15815 pattern childGuard
    simpa only [d886, d132, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15817 (pattern : Twelve) (guard : d477 pattern = 1) : d895 pattern ≤ (1 : Int) + d2672 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d895, d2672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15816 pattern childGuard
    simpa only [d895, d2672, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d895, d2672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15803 pattern childGuard
    simpa only [d895, d2672, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15818 (pattern : Twelve) (guard : d477 pattern = 1) : d900 pattern ≤ (1 : Int) + d2673 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d477 pattern = 1 := by simpa only [d900, d2673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15814 pattern childGuard
    simpa only [d900, d2673, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d477 pattern = 1 := by simpa only [d900, d2673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15817 pattern childGuard
    simpa only [d900, d2673, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15819 (pattern : Twelve) (guard : d477 pattern = 1) : d873 pattern ≤ (1 : Int) + d117 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d477, d873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12769 pattern childGuard
    simpa only [d477, d873, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d477, d873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11310 pattern childGuard
    simpa only [d477, d873, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
