/- Staged soko4-1 certificate. No result until all kernel checks pass. -/
import NetHack.Sokoban41.Comparisons34
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban41.Diagram
theorem c5600 (pattern : Ten) (guard : d782 pattern = 1) : d188 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d781 pattern = 1 := by simpa only [d782, d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5599 pattern childGuard
    simpa only [d782, d188, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d782, d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5477 pattern childGuard
    simpa only [d782, d188, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5601 (pattern : Ten) (guard : d783 pattern = 1) : d190 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d782 pattern = 1 := by simpa only [d783, d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5600 pattern childGuard
    simpa only [d783, d190, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d783, d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5479 pattern childGuard
    simpa only [d783, d190, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5602 (pattern : Ten) (guard : d784 pattern = 1) : d192 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d783 pattern = 1 := by simpa only [d784, d192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5601 pattern childGuard
    simpa only [d784, d192, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d784, d192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5481 pattern childGuard
    simpa only [d784, d192, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5603 (pattern : Ten) (guard : d778 pattern = 1) : d174 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d759 pattern = 1 := by simpa only [d778, d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5595 pattern childGuard
    simpa only [d778, d174, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d778, d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5483 pattern childGuard
    simpa only [d778, d174, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5604 (pattern : Ten) (guard : d779 pattern = 1) : d202 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d778 pattern = 1 := by simpa only [d779, d202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5603 pattern childGuard
    simpa only [d779, d202, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d779, d202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5485 pattern childGuard
    simpa only [d779, d202, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5605 (pattern : Ten) (guard : d780 pattern = 1) : d207 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d779 pattern = 1 := by simpa only [d780, d207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5604 pattern childGuard
    simpa only [d780, d207, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d780, d207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5487 pattern childGuard
    simpa only [d780, d207, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5606 (pattern : Ten) (guard : d781 pattern = 1) : d207 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d780 pattern = 1 := by simpa only [d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5605 pattern childGuard
    simpa only [d781, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5489 pattern childGuard
    simpa only [d781, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5607 (pattern : Ten) (guard : d782 pattern = 1) : d207 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d781 pattern = 1 := by simpa only [d782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5606 pattern childGuard
    simpa only [d782, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5489 pattern childGuard
    simpa only [d782, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5608 (pattern : Ten) (guard : d783 pattern = 1) : d218 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d782 pattern = 1 := by simpa only [d783, d218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5607 pattern childGuard
    simpa only [d783, d218, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d783, d218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5492 pattern childGuard
    simpa only [d783, d218, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5609 (pattern : Ten) (guard : d784 pattern = 1) : d220 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d783 pattern = 1 := by simpa only [d784, d220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5608 pattern childGuard
    simpa only [d784, d220, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d784, d220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5494 pattern childGuard
    simpa only [d784, d220, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5610 (pattern : Ten) (guard : d0 pattern = 1) : d221 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5611 (pattern : Ten) (guard : d358 pattern = 1) : d0 pattern ≤ (0 : Int) + d0 pattern := by
  omega
theorem c5612 (pattern : Ten) (guard : d759 pattern = 1) : d222 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d759, d222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5610 pattern childGuard
    simpa only [d759, d222, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d358 pattern = 1 := by simpa only [d759, d222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5611 pattern childGuard
    simpa only [d759, d222, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5613 (pattern : Ten) (guard : d778 pattern = 1) : d223 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d759 pattern = 1 := by simpa only [d778, d223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5612 pattern childGuard
    simpa only [d778, d223, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d778, d223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4603 pattern childGuard
    simpa only [d778, d223, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5614 (pattern : Ten) (guard : d779 pattern = 1) : d224 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d778 pattern = 1 := by simpa only [d779, d224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5613 pattern childGuard
    simpa only [d779, d224, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d779, d224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2784 pattern childGuard
    simpa only [d779, d224, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5615 (pattern : Ten) (guard : d780 pattern = 1) : d225 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d779 pattern = 1 := by simpa only [d780, d225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5614 pattern childGuard
    simpa only [d780, d225, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d780, d225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4566 pattern childGuard
    simpa only [d780, d225, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5616 (pattern : Ten) (guard : d781 pattern = 1) : d226 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d780 pattern = 1 := by simpa only [d781, d226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5615 pattern childGuard
    simpa only [d781, d226, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d781, d226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5501 pattern childGuard
    simpa only [d781, d226, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5617 (pattern : Ten) (guard : d782 pattern = 1) : d230 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d781 pattern = 1 := by simpa only [d782, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5616 pattern childGuard
    simpa only [d782, d230, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d782, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5503 pattern childGuard
    simpa only [d782, d230, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5618 (pattern : Ten) (guard : d783 pattern = 1) : d232 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d782 pattern = 1 := by simpa only [d783, d232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5617 pattern childGuard
    simpa only [d783, d232, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d783, d232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5505 pattern childGuard
    simpa only [d783, d232, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5619 (pattern : Ten) (guard : d784 pattern = 1) : d234 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d783 pattern = 1 := by simpa only [d784, d234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5618 pattern childGuard
    simpa only [d784, d234, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d784, d234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5507 pattern childGuard
    simpa only [d784, d234, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5620 (pattern : Ten) (guard : d782 pattern = 1) : d235 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d781 pattern = 1 := by simpa only [d782, d235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5606 pattern childGuard
    simpa only [d782, d235, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d782, d235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c356 pattern childGuard
    simpa only [d782, d235, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5621 (pattern : Ten) (guard : d783 pattern = 1) : d236 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d782 pattern = 1 := by simpa only [d783, d236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5620 pattern childGuard
    simpa only [d783, d236, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d783, d236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5510 pattern childGuard
    simpa only [d783, d236, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5622 (pattern : Ten) (guard : d784 pattern = 1) : d238 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d783 pattern = 1 := by simpa only [d784, d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5621 pattern childGuard
    simpa only [d784, d238, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d784, d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5512 pattern childGuard
    simpa only [d784, d238, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5623 (pattern : Ten) (guard : d0 pattern = 1) : d240 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5624 (pattern : Ten) (guard : d759 pattern = 1) : d241 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d759, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5623 pattern childGuard
    simpa only [d759, d241, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d358 pattern = 1 := by simpa only [d759, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c359 pattern childGuard
    simpa only [d759, d241, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5625 (pattern : Ten) (guard : d778 pattern = 1) : d242 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d759 pattern = 1 := by simpa only [d778, d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5624 pattern childGuard
    simpa only [d778, d242, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d778, d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c292 pattern childGuard
    simpa only [d778, d242, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5626 (pattern : Ten) (guard : d779 pattern = 1) : d243 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d778 pattern = 1 := by simpa only [d779, d243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5625 pattern childGuard
    simpa only [d779, d243, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d779, d243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5471 pattern childGuard
    simpa only [d779, d243, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5627 (pattern : Ten) (guard : d780 pattern = 1) : d244 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d779 pattern = 1 := by simpa only [d780, d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5626 pattern childGuard
    simpa only [d780, d244, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d780, d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5473 pattern childGuard
    simpa only [d780, d244, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5628 (pattern : Ten) (guard : d781 pattern = 1) : d245 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d780 pattern = 1 := by simpa only [d781, d245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5627 pattern childGuard
    simpa only [d781, d245, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d781, d245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5475 pattern childGuard
    simpa only [d781, d245, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5629 (pattern : Ten) (guard : d782 pattern = 1) : d246 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d781 pattern = 1 := by simpa only [d782, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5628 pattern childGuard
    simpa only [d782, d246, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d782, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5477 pattern childGuard
    simpa only [d782, d246, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5630 (pattern : Ten) (guard : d783 pattern = 1) : d247 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d782 pattern = 1 := by simpa only [d783, d247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5629 pattern childGuard
    simpa only [d783, d247, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d783, d247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5479 pattern childGuard
    simpa only [d783, d247, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5631 (pattern : Ten) (guard : d784 pattern = 1) : d248 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d783 pattern = 1 := by simpa only [d784, d248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5630 pattern childGuard
    simpa only [d784, d248, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d784, d248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5481 pattern childGuard
    simpa only [d784, d248, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5632 (pattern : Ten) (guard : d778 pattern = 1) : d173 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d759 pattern = 1 := by simpa only [d778, d173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5595 pattern childGuard
    simpa only [d778, d173, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d778, d173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c356 pattern childGuard
    simpa only [d778, d173, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5633 (pattern : Ten) (guard : d779 pattern = 1) : d249 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d778 pattern = 1 := by simpa only [d779, d249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5632 pattern childGuard
    simpa only [d779, d249, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d779, d249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c292 pattern childGuard
    simpa only [d779, d249, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5634 (pattern : Ten) (guard : d780 pattern = 1) : d253 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d779 pattern = 1 := by simpa only [d780, d253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5633 pattern childGuard
    simpa only [d780, d253, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d780, d253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5525 pattern childGuard
    simpa only [d780, d253, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5635 (pattern : Ten) (guard : d781 pattern = 1) : d257 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d780 pattern = 1 := by simpa only [d781, d257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5634 pattern childGuard
    simpa only [d781, d257, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d781, d257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5527 pattern childGuard
    simpa only [d781, d257, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5636 (pattern : Ten) (guard : d782 pattern = 1) : d261 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d781 pattern = 1 := by simpa only [d782, d261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5635 pattern childGuard
    simpa only [d782, d261, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d782, d261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5529 pattern childGuard
    simpa only [d782, d261, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5637 (pattern : Ten) (guard : d783 pattern = 1) : d263 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d782 pattern = 1 := by simpa only [d783, d263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5636 pattern childGuard
    simpa only [d783, d263, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d783, d263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5531 pattern childGuard
    simpa only [d783, d263, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5638 (pattern : Ten) (guard : d784 pattern = 1) : d265 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d783 pattern = 1 := by simpa only [d784, d265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5637 pattern childGuard
    simpa only [d784, d265, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d784, d265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5533 pattern childGuard
    simpa only [d784, d265, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5639 (pattern : Ten) (guard : d779 pattern = 1) : d266 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d778 pattern = 1 := by simpa only [d779, d266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5603 pattern childGuard
    simpa only [d779, d266, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d779, d266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c356 pattern childGuard
    simpa only [d779, d266, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5640 (pattern : Ten) (guard : d780 pattern = 1) : d267 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d779 pattern = 1 := by simpa only [d780, d267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5639 pattern childGuard
    simpa only [d780, d267, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d780, d267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5536 pattern childGuard
    simpa only [d780, d267, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5641 (pattern : Ten) (guard : d781 pattern = 1) : d271 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d780 pattern = 1 := by simpa only [d781, d271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5640 pattern childGuard
    simpa only [d781, d271, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d781, d271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5538 pattern childGuard
    simpa only [d781, d271, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5642 (pattern : Ten) (guard : d782 pattern = 1) : d275 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d781 pattern = 1 := by simpa only [d782, d275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5641 pattern childGuard
    simpa only [d782, d275, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d782, d275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5540 pattern childGuard
    simpa only [d782, d275, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5643 (pattern : Ten) (guard : d783 pattern = 1) : d277 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d782 pattern = 1 := by simpa only [d783, d277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5642 pattern childGuard
    simpa only [d783, d277, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d783, d277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5542 pattern childGuard
    simpa only [d783, d277, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5644 (pattern : Ten) (guard : d784 pattern = 1) : d279 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d783 pattern = 1 := by simpa only [d784, d279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5643 pattern childGuard
    simpa only [d784, d279, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d784, d279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5544 pattern childGuard
    simpa only [d784, d279, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5645 (pattern : Ten) (guard : d780 pattern = 1) : d280 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d779 pattern = 1 := by simpa only [d780, d280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5604 pattern childGuard
    simpa only [d780, d280, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d780, d280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c356 pattern childGuard
    simpa only [d780, d280, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5646 (pattern : Ten) (guard : d781 pattern = 1) : d281 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d780 pattern = 1 := by simpa only [d781, d281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5645 pattern childGuard
    simpa only [d781, d281, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d781, d281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5547 pattern childGuard
    simpa only [d781, d281, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5647 (pattern : Ten) (guard : d782 pattern = 1) : d284 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d781 pattern = 1 := by simpa only [d782, d284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5646 pattern childGuard
    simpa only [d782, d284, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d782, d284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5547 pattern childGuard
    simpa only [d782, d284, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5648 (pattern : Ten) (guard : d783 pattern = 1) : d286 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d782 pattern = 1 := by simpa only [d783, d286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5647 pattern childGuard
    simpa only [d783, d286, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d783, d286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5550 pattern childGuard
    simpa only [d783, d286, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5649 (pattern : Ten) (guard : d784 pattern = 1) : d288 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d783 pattern = 1 := by simpa only [d784, d288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5648 pattern childGuard
    simpa only [d784, d288, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d784, d288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5552 pattern childGuard
    simpa only [d784, d288, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5650 (pattern : Ten) (guard : d784 pattern = 1) : d289 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d783 pattern = 1 := by simpa only [d784, d289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5608 pattern childGuard
    simpa only [d784, d289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d784, d289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c356 pattern childGuard
    simpa only [d784, d289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5651 (pattern : Ten) (guard : d783 pattern = 1) : d290 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d782 pattern = 1 := by simpa only [d783, d290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5607 pattern childGuard
    simpa only [d783, d290, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d783, d290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c356 pattern childGuard
    simpa only [d783, d290, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5652 (pattern : Ten) (guard : d784 pattern = 1) : d291 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d783 pattern = 1 := by simpa only [d784, d291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5651 pattern childGuard
    simpa only [d784, d291, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d784, d291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5556 pattern childGuard
    simpa only [d784, d291, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5653 (pattern : Ten) (guard : d759 pattern = 1) : d292 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d759, d292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c292 pattern childGuard
    simpa only [d759, d292, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d358 pattern = 1 := by simpa only [d759, d292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5611 pattern childGuard
    simpa only [d759, d292, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5654 (pattern : Ten) (guard : d778 pattern = 1) : d293 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d759 pattern = 1 := by simpa only [d778, d293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5653 pattern childGuard
    simpa only [d778, d293, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d778, d293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5483 pattern childGuard
    simpa only [d778, d293, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5655 (pattern : Ten) (guard : d779 pattern = 1) : d294 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d778 pattern = 1 := by simpa only [d779, d294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5654 pattern childGuard
    simpa only [d779, d294, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d779, d294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5485 pattern childGuard
    simpa only [d779, d294, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5656 (pattern : Ten) (guard : d780 pattern = 1) : d295 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d779 pattern = 1 := by simpa only [d780, d295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5655 pattern childGuard
    simpa only [d780, d295, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d780, d295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5487 pattern childGuard
    simpa only [d780, d295, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5657 (pattern : Ten) (guard : d781 pattern = 1) : d296 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d780 pattern = 1 := by simpa only [d781, d296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5656 pattern childGuard
    simpa only [d781, d296, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d781, d296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5489 pattern childGuard
    simpa only [d781, d296, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5658 (pattern : Ten) (guard : d782 pattern = 1) : d297 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d781 pattern = 1 := by simpa only [d782, d297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5657 pattern childGuard
    simpa only [d782, d297, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d782, d297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5489 pattern childGuard
    simpa only [d782, d297, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5659 (pattern : Ten) (guard : d783 pattern = 1) : d298 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d782 pattern = 1 := by simpa only [d783, d298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5658 pattern childGuard
    simpa only [d783, d298, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d783, d298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5492 pattern childGuard
    simpa only [d783, d298, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5660 (pattern : Ten) (guard : d784 pattern = 1) : d300 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d783 pattern = 1 := by simpa only [d784, d300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5659 pattern childGuard
    simpa only [d784, d300, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d784, d300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5565 pattern childGuard
    simpa only [d784, d300, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5661 (pattern : Ten) (guard : d779 pattern = 1) : d173 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d778 pattern = 1 := by simpa only [d779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5632 pattern childGuard
    simpa only [d779, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5471 pattern childGuard
    simpa only [d779, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5662 (pattern : Ten) (guard : d780 pattern = 1) : d302 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d779 pattern = 1 := by simpa only [d780, d302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5661 pattern childGuard
    simpa only [d780, d302, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d780, d302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5473 pattern childGuard
    simpa only [d780, d302, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5663 (pattern : Ten) (guard : d781 pattern = 1) : d304 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d780 pattern = 1 := by simpa only [d781, d304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5662 pattern childGuard
    simpa only [d781, d304, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d781, d304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5475 pattern childGuard
    simpa only [d781, d304, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5664 (pattern : Ten) (guard : d782 pattern = 1) : d306 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d781 pattern = 1 := by simpa only [d782, d306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5663 pattern childGuard
    simpa only [d782, d306, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d782, d306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5570 pattern childGuard
    simpa only [d782, d306, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5665 (pattern : Ten) (guard : d783 pattern = 1) : d307 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d782 pattern = 1 := by simpa only [d783, d307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5664 pattern childGuard
    simpa only [d783, d307, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d783, d307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5479 pattern childGuard
    simpa only [d783, d307, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5666 (pattern : Ten) (guard : d784 pattern = 1) : d308 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d783 pattern = 1 := by simpa only [d784, d308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5665 pattern childGuard
    simpa only [d784, d308, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d784, d308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5481 pattern childGuard
    simpa only [d784, d308, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5667 (pattern : Ten) (guard : d781 pattern = 1) : d211 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d780 pattern = 1 := by simpa only [d781, d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5605 pattern childGuard
    simpa only [d781, d211, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d781, d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c356 pattern childGuard
    simpa only [d781, d211, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5668 (pattern : Ten) (guard : d782 pattern = 1) : d326 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d781 pattern = 1 := by simpa only [d782, d326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5667 pattern childGuard
    simpa only [d782, d326, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d782, d326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5489 pattern childGuard
    simpa only [d782, d326, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5669 (pattern : Ten) (guard : d783 pattern = 1) : d329 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d782 pattern = 1 := by simpa only [d783, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5668 pattern childGuard
    simpa only [d783, d329, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d783, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5576 pattern childGuard
    simpa only [d783, d329, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5670 (pattern : Ten) (guard : d784 pattern = 1) : d331 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d783 pattern = 1 := by simpa only [d784, d331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5669 pattern childGuard
    simpa only [d784, d331, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d784, d331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5578 pattern childGuard
    simpa only [d784, d331, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5671 (pattern : Ten) (guard : d781 pattern = 1) : d332 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d780 pattern = 1 := by simpa only [d781, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5605 pattern childGuard
    simpa only [d781, d332, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d781, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5580 pattern childGuard
    simpa only [d781, d332, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5672 (pattern : Ten) (guard : d782 pattern = 1) : d332 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d781 pattern = 1 := by simpa only [d782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5671 pattern childGuard
    simpa only [d782, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5582 pattern childGuard
    simpa only [d782, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5673 (pattern : Ten) (guard : d783 pattern = 1) : d338 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d782 pattern = 1 := by simpa only [d783, d338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5672 pattern childGuard
    simpa only [d783, d338, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d783, d338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5584 pattern childGuard
    simpa only [d783, d338, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5674 (pattern : Ten) (guard : d784 pattern = 1) : d340 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d783 pattern = 1 := by simpa only [d784, d340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5673 pattern childGuard
    simpa only [d784, d340, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d784, d340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5586 pattern childGuard
    simpa only [d784, d340, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5675 (pattern : Ten) (guard : d781 pattern = 1) : d344 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d780 pattern = 1 := by simpa only [d781, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5605 pattern childGuard
    simpa only [d781, d344, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d781, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5588 pattern childGuard
    simpa only [d781, d344, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5676 (pattern : Ten) (guard : d782 pattern = 1) : d346 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d781 pattern = 1 := by simpa only [d782, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5675 pattern childGuard
    simpa only [d782, d346, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d782, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5590 pattern childGuard
    simpa only [d782, d346, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5677 (pattern : Ten) (guard : d783 pattern = 1) : d347 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d782 pattern = 1 := by simpa only [d783, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5676 pattern childGuard
    simpa only [d783, d347, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d783, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5584 pattern childGuard
    simpa only [d783, d347, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5678 (pattern : Ten) (guard : d784 pattern = 1) : d349 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d783 pattern = 1 := by simpa only [d784, d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5677 pattern childGuard
    simpa only [d784, d349, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d784, d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5593 pattern childGuard
    simpa only [d784, d349, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban41.Diagram
