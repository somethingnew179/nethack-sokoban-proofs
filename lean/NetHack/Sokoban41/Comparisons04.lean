/- Staged soko4-1 certificate. No result until all kernel checks pass. -/
import NetHack.Sokoban41.Comparisons03
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban41.Diagram
theorem c640 (pattern : Ten) (guard : d390 pattern = 1) : d119 pattern ≤ (0 : Int) + d128 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d390 pattern = 1 := by simpa only [d119, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c636 pattern childGuard
    simpa only [d119, d128, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d390 pattern = 1 := by simpa only [d119, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c639 pattern childGuard
    simpa only [d119, d128, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c641 (pattern : Ten) (guard : d0 pattern = 1) : d10 pattern ≤ (0 : Int) + d48 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c642 (pattern : Ten) (guard : d390 pattern = 1) : d112 pattern ≤ (0 : Int) + d48 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d389 pattern = 1 := by simpa only [d390, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c633 pattern childGuard
    simpa only [d390, d112, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d390, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c641 pattern childGuard
    simpa only [d390, d112, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c643 (pattern : Ten) (guard : d350 pattern = 1) : d14 pattern ≤ (0 : Int) + d14 pattern := by
  omega
theorem c644 (pattern : Ten) (guard : d0 pattern = 1) : d14 pattern ≤ (0 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c645 (pattern : Ten) (guard : d389 pattern = 1) : d14 pattern ≤ (0 : Int) + d20 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d389, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c643 pattern childGuard
    simpa only [d389, d20, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d389, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c644 pattern childGuard
    simpa only [d389, d20, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c646 (pattern : Ten) (guard : d390 pattern = 1) : d113 pattern ≤ (0 : Int) + d20 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d389 pattern = 1 := by simpa only [d390, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c645 pattern childGuard
    simpa only [d390, d113, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d390, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c232 pattern childGuard
    simpa only [d390, d113, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c647 (pattern : Ten) (guard : d390 pattern = 1) : d117 pattern ≤ (0 : Int) + d126 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d390 pattern = 1 := by simpa only [d117, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c642 pattern childGuard
    simpa only [d117, d126, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d390 pattern = 1 := by simpa only [d117, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c646 pattern childGuard
    simpa only [d117, d126, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c648 (pattern : Ten) (guard : d350 pattern = 1) : d44 pattern ≤ (0 : Int) + d44 pattern := by
  omega
theorem c649 (pattern : Ten) (guard : d0 pattern = 1) : d44 pattern ≤ (0 : Int) + d43 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c650 (pattern : Ten) (guard : d389 pattern = 1) : d44 pattern ≤ (0 : Int) + d50 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d389, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c648 pattern childGuard
    simpa only [d389, d50, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d389, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c649 pattern childGuard
    simpa only [d389, d50, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c651 (pattern : Ten) (guard : d0 pattern = 1) : d10 pattern ≤ (0 : Int) + d50 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c652 (pattern : Ten) (guard : d390 pattern = 1) : d114 pattern ≤ (0 : Int) + d50 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d389 pattern = 1 := by simpa only [d390, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c650 pattern childGuard
    simpa only [d390, d114, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d390, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c651 pattern childGuard
    simpa only [d390, d114, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c653 (pattern : Ten) (guard : d390 pattern = 1) : d118 pattern ≤ (0 : Int) + d127 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d390 pattern = 1 := by simpa only [d118, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c652 pattern childGuard
    simpa only [d118, d127, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d390 pattern = 1 := by simpa only [d118, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c646 pattern childGuard
    simpa only [d118, d127, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c654 (pattern : Ten) (guard : d390 pattern = 1) : d120 pattern ≤ (0 : Int) + d129 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d390 pattern = 1 := by simpa only [d120, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c647 pattern childGuard
    simpa only [d120, d129, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d390 pattern = 1 := by simpa only [d120, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c653 pattern childGuard
    simpa only [d120, d129, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c655 (pattern : Ten) (guard : d390 pattern = 1) : d121 pattern ≤ (0 : Int) + d130 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d390 pattern = 1 := by simpa only [d121, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c640 pattern childGuard
    simpa only [d121, d130, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d390 pattern = 1 := by simpa only [d121, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c654 pattern childGuard
    simpa only [d121, d130, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c656 (pattern : Ten) (guard : d390 pattern = 1) : d10 pattern ≤ (0 : Int) + d10 pattern := by
  omega
theorem c657 (pattern : Ten) (guard : d390 pattern = 1) : d122 pattern ≤ (0 : Int) + d131 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d390 pattern = 1 := by simpa only [d122, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c654 pattern childGuard
    simpa only [d122, d131, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d390 pattern = 1 := by simpa only [d122, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c656 pattern childGuard
    simpa only [d122, d131, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c658 (pattern : Ten) (guard : d390 pattern = 1) : d123 pattern ≤ (0 : Int) + d132 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d390 pattern = 1 := by simpa only [d123, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c655 pattern childGuard
    simpa only [d123, d132, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d390 pattern = 1 := by simpa only [d123, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c657 pattern childGuard
    simpa only [d123, d132, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c659 (pattern : Ten) (guard : d1 pattern = 1) : d174 pattern ≤ (0 : Int) + d174 pattern := by
  omega
theorem c660 (pattern : Ten) (guard : d0 pattern = 1) : d10 pattern ≤ (0 : Int) + d197 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c661 (pattern : Ten) (guard : d386 pattern = 1) : d266 pattern ≤ (0 : Int) + d202 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d386, d266, d202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c659 pattern childGuard
    simpa only [d386, d266, d202, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d386, d266, d202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c660 pattern childGuard
    simpa only [d386, d266, d202, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c662 (pattern : Ten) (guard : d0 pattern = 1) : d174 pattern ≤ (0 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c663 (pattern : Ten) (guard : d391 pattern = 1) : d267 pattern ≤ (0 : Int) + d280 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d386 pattern = 1 := by simpa only [d391, d267, d280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c661 pattern childGuard
    simpa only [d391, d267, d280, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d391, d267, d280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c662 pattern childGuard
    simpa only [d391, d267, d280, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c664 (pattern : Ten) (guard : d0 pattern = 1) : d174 pattern ≤ (0 : Int) + d197 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c665 (pattern : Ten) (guard : d386 pattern = 1) : d174 pattern ≤ (0 : Int) + d202 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d386, d202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c659 pattern childGuard
    simpa only [d386, d202, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d386, d202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c664 pattern childGuard
    simpa only [d386, d202, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c666 (pattern : Ten) (guard : d0 pattern = 1) : d10 pattern ≤ (0 : Int) + d202 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c667 (pattern : Ten) (guard : d391 pattern = 1) : d268 pattern ≤ (0 : Int) + d202 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d386 pattern = 1 := by simpa only [d391, d268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c665 pattern childGuard
    simpa only [d391, d268, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d391, d268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c666 pattern childGuard
    simpa only [d391, d268, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c668 (pattern : Ten) (guard : d391 pattern = 1) : d271 pattern ≤ (0 : Int) + d281 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d391 pattern = 1 := by simpa only [d271, d281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c663 pattern childGuard
    simpa only [d271, d281, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d391 pattern = 1 := by simpa only [d271, d281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c667 pattern childGuard
    simpa only [d271, d281, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c669 (pattern : Ten) (guard : d0 pattern = 1) : d199 pattern ≤ (0 : Int) + d202 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c670 (pattern : Ten) (guard : d391 pattern = 1) : d269 pattern ≤ (0 : Int) + d202 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d386 pattern = 1 := by simpa only [d391, d269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c665 pattern childGuard
    simpa only [d391, d269, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d391, d269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c669 pattern childGuard
    simpa only [d391, d269, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c671 (pattern : Ten) (guard : d391 pattern = 1) : d272 pattern ≤ (0 : Int) + d202 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d391 pattern = 1 := by simpa only [d272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c670 pattern childGuard
    simpa only [d272, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d391 pattern = 1 := by simpa only [d272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c667 pattern childGuard
    simpa only [d272, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c672 (pattern : Ten) (guard : d391 pattern = 1) : d275 pattern ≤ (0 : Int) + d284 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d391 pattern = 1 := by simpa only [d275, d284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c668 pattern childGuard
    simpa only [d275, d284, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d391 pattern = 1 := by simpa only [d275, d284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c671 pattern childGuard
    simpa only [d275, d284, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c673 (pattern : Ten) (guard : d391 pattern = 1) : d10 pattern ≤ (0 : Int) + d10 pattern := by
  omega
theorem c674 (pattern : Ten) (guard : d391 pattern = 1) : d273 pattern ≤ (0 : Int) + d282 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d391 pattern = 1 := by simpa only [d273, d282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c667 pattern childGuard
    simpa only [d273, d282, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d391 pattern = 1 := by simpa only [d273, d282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c673 pattern childGuard
    simpa only [d273, d282, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c675 (pattern : Ten) (guard : d1 pattern = 1) : d199 pattern ≤ (0 : Int) + d199 pattern := by
  omega
theorem c676 (pattern : Ten) (guard : d0 pattern = 1) : d199 pattern ≤ (0 : Int) + d198 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c677 (pattern : Ten) (guard : d386 pattern = 1) : d199 pattern ≤ (0 : Int) + d204 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d386, d204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c675 pattern childGuard
    simpa only [d386, d204, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d386, d204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c676 pattern childGuard
    simpa only [d386, d204, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c678 (pattern : Ten) (guard : d0 pattern = 1) : d10 pattern ≤ (0 : Int) + d204 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c679 (pattern : Ten) (guard : d391 pattern = 1) : d270 pattern ≤ (0 : Int) + d204 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d386 pattern = 1 := by simpa only [d391, d270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c677 pattern childGuard
    simpa only [d391, d270, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d391, d270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c678 pattern childGuard
    simpa only [d391, d270, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c680 (pattern : Ten) (guard : d391 pattern = 1) : d274 pattern ≤ (0 : Int) + d283 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d391 pattern = 1 := by simpa only [d274, d283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c679 pattern childGuard
    simpa only [d274, d283, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d391 pattern = 1 := by simpa only [d274, d283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c673 pattern childGuard
    simpa only [d274, d283, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c681 (pattern : Ten) (guard : d391 pattern = 1) : d276 pattern ≤ (0 : Int) + d285 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d391 pattern = 1 := by simpa only [d276, d285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c674 pattern childGuard
    simpa only [d276, d285, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d391 pattern = 1 := by simpa only [d276, d285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c680 pattern childGuard
    simpa only [d276, d285, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c682 (pattern : Ten) (guard : d391 pattern = 1) : d277 pattern ≤ (0 : Int) + d286 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d391 pattern = 1 := by simpa only [d277, d286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c672 pattern childGuard
    simpa only [d277, d286, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d391 pattern = 1 := by simpa only [d277, d286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c681 pattern childGuard
    simpa only [d277, d286, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c683 (pattern : Ten) (guard : d391 pattern = 1) : d278 pattern ≤ (0 : Int) + d287 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d391 pattern = 1 := by simpa only [d278, d287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c681 pattern childGuard
    simpa only [d278, d287, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d391 pattern = 1 := by simpa only [d278, d287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c673 pattern childGuard
    simpa only [d278, d287, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c684 (pattern : Ten) (guard : d391 pattern = 1) : d279 pattern ≤ (0 : Int) + d288 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d391 pattern = 1 := by simpa only [d279, d288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c682 pattern childGuard
    simpa only [d279, d288, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d391 pattern = 1 := by simpa only [d279, d288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c683 pattern childGuard
    simpa only [d279, d288, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c685 (pattern : Ten) (guard : d384 pattern = 1) : d15 pattern ≤ (0 : Int) + d86 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d384, d15, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c393 pattern childGuard
    simpa only [d384, d15, d86, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d384, d15, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c517 pattern childGuard
    simpa only [d384, d15, d86, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c686 (pattern : Ten) (guard : d0 pattern = 1) : d5 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c687 (pattern : Ten) (guard : d387 pattern = 1) : d108 pattern ≤ (0 : Int) + d87 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d387, d108, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c685 pattern childGuard
    simpa only [d387, d108, d87, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d387, d108, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c686 pattern childGuard
    simpa only [d387, d108, d87, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c688 (pattern : Ten) (guard : d0 pattern = 1) : d15 pattern ≤ (0 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c689 (pattern : Ten) (guard : d387 pattern = 1) : d15 pattern ≤ (0 : Int) + d88 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d387, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c411 pattern childGuard
    simpa only [d387, d88, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d387, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c688 pattern childGuard
    simpa only [d387, d88, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c690 (pattern : Ten) (guard : d387 pattern = 1) : d109 pattern ≤ (0 : Int) + d93 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d387 pattern = 1 := by simpa only [d109, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c687 pattern childGuard
    simpa only [d109, d93, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d387 pattern = 1 := by simpa only [d109, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c689 pattern childGuard
    simpa only [d109, d93, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c691 (pattern : Ten) (guard : d0 pattern = 1) : d15 pattern ≤ (0 : Int) + d11 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c692 (pattern : Ten) (guard : d387 pattern = 1) : d15 pattern ≤ (0 : Int) + d89 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d387, d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c411 pattern childGuard
    simpa only [d387, d89, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d387, d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c691 pattern childGuard
    simpa only [d387, d89, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c693 (pattern : Ten) (guard : d387 pattern = 1) : d14 pattern ≤ (0 : Int) + d90 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d387, d90, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c405 pattern childGuard
    simpa only [d387, d90, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d387, d90, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c644 pattern childGuard
    simpa only [d387, d90, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c694 (pattern : Ten) (guard : d387 pattern = 1) : d110 pattern ≤ (0 : Int) + d94 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d387 pattern = 1 := by simpa only [d110, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c692 pattern childGuard
    simpa only [d110, d94, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d387 pattern = 1 := by simpa only [d110, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c693 pattern childGuard
    simpa only [d110, d94, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c695 (pattern : Ten) (guard : d387 pattern = 1) : d115 pattern ≤ (0 : Int) + d99 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d387 pattern = 1 := by simpa only [d115, d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c690 pattern childGuard
    simpa only [d115, d99, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d387 pattern = 1 := by simpa only [d115, d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c694 pattern childGuard
    simpa only [d115, d99, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c696 (pattern : Ten) (guard : d0 pattern = 1) : d15 pattern ≤ (0 : Int) + d2 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c697 (pattern : Ten) (guard : d387 pattern = 1) : d15 pattern ≤ (0 : Int) + d91 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d387, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c411 pattern childGuard
    simpa only [d387, d91, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d387, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c696 pattern childGuard
    simpa only [d387, d91, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c698 (pattern : Ten) (guard : d384 pattern = 1) : d44 pattern ≤ (0 : Int) + d2 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d384, d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c412 pattern childGuard
    simpa only [d384, d44, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d384, d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c499 pattern childGuard
    simpa only [d384, d44, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c699 (pattern : Ten) (guard : d0 pattern = 1) : d44 pattern ≤ (0 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c700 (pattern : Ten) (guard : d387 pattern = 1) : d44 pattern ≤ (0 : Int) + d92 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d387, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c698 pattern childGuard
    simpa only [d387, d92, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d387, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c699 pattern childGuard
    simpa only [d387, d92, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c701 (pattern : Ten) (guard : d387 pattern = 1) : d111 pattern ≤ (0 : Int) + d95 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d387 pattern = 1 := by simpa only [d111, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c697 pattern childGuard
    simpa only [d111, d95, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d387 pattern = 1 := by simpa only [d111, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c700 pattern childGuard
    simpa only [d111, d95, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c702 (pattern : Ten) (guard : d387 pattern = 1) : d116 pattern ≤ (0 : Int) + d100 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d387 pattern = 1 := by simpa only [d116, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c701 pattern childGuard
    simpa only [d116, d100, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d387 pattern = 1 := by simpa only [d116, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c694 pattern childGuard
    simpa only [d116, d100, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c703 (pattern : Ten) (guard : d387 pattern = 1) : d119 pattern ≤ (0 : Int) + d103 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d387 pattern = 1 := by simpa only [d119, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c695 pattern childGuard
    simpa only [d119, d103, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d387 pattern = 1 := by simpa only [d119, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c702 pattern childGuard
    simpa only [d119, d103, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c704 (pattern : Ten) (guard : d387 pattern = 1) : d112 pattern ≤ (0 : Int) + d96 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d387 pattern = 1 := by simpa only [d112, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c689 pattern childGuard
    simpa only [d112, d96, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d387 pattern = 1 := by simpa only [d112, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c524 pattern childGuard
    simpa only [d112, d96, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c705 (pattern : Ten) (guard : d387 pattern = 1) : d113 pattern ≤ (0 : Int) + d97 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d387 pattern = 1 := by simpa only [d113, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c693 pattern childGuard
    simpa only [d113, d97, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d387 pattern = 1 := by simpa only [d113, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c524 pattern childGuard
    simpa only [d113, d97, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c706 (pattern : Ten) (guard : d387 pattern = 1) : d117 pattern ≤ (0 : Int) + d101 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d387 pattern = 1 := by simpa only [d117, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c704 pattern childGuard
    simpa only [d117, d101, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d387 pattern = 1 := by simpa only [d117, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c705 pattern childGuard
    simpa only [d117, d101, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c707 (pattern : Ten) (guard : d387 pattern = 1) : d114 pattern ≤ (0 : Int) + d98 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d387 pattern = 1 := by simpa only [d114, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c700 pattern childGuard
    simpa only [d114, d98, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d387 pattern = 1 := by simpa only [d114, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c524 pattern childGuard
    simpa only [d114, d98, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c708 (pattern : Ten) (guard : d387 pattern = 1) : d118 pattern ≤ (0 : Int) + d102 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d387 pattern = 1 := by simpa only [d118, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c707 pattern childGuard
    simpa only [d118, d102, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d387 pattern = 1 := by simpa only [d118, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c705 pattern childGuard
    simpa only [d118, d102, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c709 (pattern : Ten) (guard : d387 pattern = 1) : d120 pattern ≤ (0 : Int) + d104 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d387 pattern = 1 := by simpa only [d120, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c706 pattern childGuard
    simpa only [d120, d104, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d387 pattern = 1 := by simpa only [d120, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c708 pattern childGuard
    simpa only [d120, d104, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c710 (pattern : Ten) (guard : d387 pattern = 1) : d121 pattern ≤ (0 : Int) + d105 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d387 pattern = 1 := by simpa only [d121, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c703 pattern childGuard
    simpa only [d121, d105, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d387 pattern = 1 := by simpa only [d121, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c709 pattern childGuard
    simpa only [d121, d105, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c711 (pattern : Ten) (guard : d387 pattern = 1) : d122 pattern ≤ (0 : Int) + d106 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d387 pattern = 1 := by simpa only [d122, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c709 pattern childGuard
    simpa only [d122, d106, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d387 pattern = 1 := by simpa only [d122, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c524 pattern childGuard
    simpa only [d122, d106, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c712 (pattern : Ten) (guard : d387 pattern = 1) : d123 pattern ≤ (0 : Int) + d107 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d387 pattern = 1 := by simpa only [d123, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c710 pattern childGuard
    simpa only [d123, d107, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d387 pattern = 1 := by simpa only [d123, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c711 pattern childGuard
    simpa only [d123, d107, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c713 (pattern : Ten) (guard : d388 pattern = 1) : d266 pattern ≤ (0 : Int) + d249 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d383 pattern = 1 := by simpa only [d388, d266, d249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c488 pattern childGuard
    simpa only [d388, d266, d249, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d388, d266, d249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c431 pattern childGuard
    simpa only [d388, d266, d249, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c714 (pattern : Ten) (guard : d388 pattern = 1) : d174 pattern ≤ (0 : Int) + d250 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d383 pattern = 1 := by simpa only [d388, d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c440 pattern childGuard
    simpa only [d388, d250, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d388, d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c662 pattern childGuard
    simpa only [d388, d250, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c715 (pattern : Ten) (guard : d388 pattern = 1) : d267 pattern ≤ (0 : Int) + d253 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d388 pattern = 1 := by simpa only [d267, d253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c713 pattern childGuard
    simpa only [d267, d253, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d388 pattern = 1 := by simpa only [d267, d253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c714 pattern childGuard
    simpa only [d267, d253, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c716 (pattern : Ten) (guard : d388 pattern = 1) : d268 pattern ≤ (0 : Int) + d254 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d388 pattern = 1 := by simpa only [d268, d254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c714 pattern childGuard
    simpa only [d268, d254, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d388 pattern = 1 := by simpa only [d268, d254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c541 pattern childGuard
    simpa only [d268, d254, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c717 (pattern : Ten) (guard : d388 pattern = 1) : d271 pattern ≤ (0 : Int) + d257 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d388 pattern = 1 := by simpa only [d271, d257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c715 pattern childGuard
    simpa only [d271, d257, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d388 pattern = 1 := by simpa only [d271, d257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c716 pattern childGuard
    simpa only [d271, d257, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c718 (pattern : Ten) (guard : d0 pattern = 1) : d174 pattern ≤ (0 : Int) + d172 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c719 (pattern : Ten) (guard : d388 pattern = 1) : d174 pattern ≤ (0 : Int) + d251 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d383 pattern = 1 := by simpa only [d388, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c440 pattern childGuard
    simpa only [d388, d251, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d388, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c718 pattern childGuard
    simpa only [d388, d251, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c720 (pattern : Ten) (guard : d0 pattern = 1) : d193 pattern ≤ (0 : Int) + d172 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c721 (pattern : Ten) (guard : d383 pattern = 1) : d199 pattern ≤ (0 : Int) + d172 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d383, d199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c441 pattern childGuard
    simpa only [d383, d199, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d383, d199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c720 pattern childGuard
    simpa only [d383, d199, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c722 (pattern : Ten) (guard : d0 pattern = 1) : d199 pattern ≤ (0 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c723 (pattern : Ten) (guard : d388 pattern = 1) : d199 pattern ≤ (0 : Int) + d252 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d383 pattern = 1 := by simpa only [d388, d252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c721 pattern childGuard
    simpa only [d388, d252, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d388, d252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c722 pattern childGuard
    simpa only [d388, d252, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c724 (pattern : Ten) (guard : d388 pattern = 1) : d269 pattern ≤ (0 : Int) + d255 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d388 pattern = 1 := by simpa only [d269, d255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c719 pattern childGuard
    simpa only [d269, d255, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d388 pattern = 1 := by simpa only [d269, d255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c723 pattern childGuard
    simpa only [d269, d255, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c725 (pattern : Ten) (guard : d388 pattern = 1) : d272 pattern ≤ (0 : Int) + d258 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d388 pattern = 1 := by simpa only [d272, d258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c724 pattern childGuard
    simpa only [d272, d258, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d388 pattern = 1 := by simpa only [d272, d258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c716 pattern childGuard
    simpa only [d272, d258, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c726 (pattern : Ten) (guard : d388 pattern = 1) : d275 pattern ≤ (0 : Int) + d261 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d388 pattern = 1 := by simpa only [d275, d261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c717 pattern childGuard
    simpa only [d275, d261, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d388 pattern = 1 := by simpa only [d275, d261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c725 pattern childGuard
    simpa only [d275, d261, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c727 (pattern : Ten) (guard : d388 pattern = 1) : d273 pattern ≤ (0 : Int) + d259 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d388 pattern = 1 := by simpa only [d273, d259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c716 pattern childGuard
    simpa only [d273, d259, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d388 pattern = 1 := by simpa only [d273, d259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c541 pattern childGuard
    simpa only [d273, d259, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c728 (pattern : Ten) (guard : d388 pattern = 1) : d270 pattern ≤ (0 : Int) + d256 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d388 pattern = 1 := by simpa only [d270, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c723 pattern childGuard
    simpa only [d270, d256, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d388 pattern = 1 := by simpa only [d270, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c541 pattern childGuard
    simpa only [d270, d256, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c729 (pattern : Ten) (guard : d388 pattern = 1) : d274 pattern ≤ (0 : Int) + d260 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d388 pattern = 1 := by simpa only [d274, d260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c728 pattern childGuard
    simpa only [d274, d260, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d388 pattern = 1 := by simpa only [d274, d260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c541 pattern childGuard
    simpa only [d274, d260, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c730 (pattern : Ten) (guard : d388 pattern = 1) : d276 pattern ≤ (0 : Int) + d262 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d388 pattern = 1 := by simpa only [d276, d262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c727 pattern childGuard
    simpa only [d276, d262, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d388 pattern = 1 := by simpa only [d276, d262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c729 pattern childGuard
    simpa only [d276, d262, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c731 (pattern : Ten) (guard : d388 pattern = 1) : d277 pattern ≤ (0 : Int) + d263 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d388 pattern = 1 := by simpa only [d277, d263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c726 pattern childGuard
    simpa only [d277, d263, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d388 pattern = 1 := by simpa only [d277, d263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c730 pattern childGuard
    simpa only [d277, d263, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c732 (pattern : Ten) (guard : d388 pattern = 1) : d278 pattern ≤ (0 : Int) + d264 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d388 pattern = 1 := by simpa only [d278, d264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c730 pattern childGuard
    simpa only [d278, d264, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d388 pattern = 1 := by simpa only [d278, d264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c541 pattern childGuard
    simpa only [d278, d264, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c733 (pattern : Ten) (guard : d388 pattern = 1) : d279 pattern ≤ (0 : Int) + d265 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d388 pattern = 1 := by simpa only [d279, d265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c731 pattern childGuard
    simpa only [d279, d265, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d388 pattern = 1 := by simpa only [d279, d265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c732 pattern childGuard
    simpa only [d279, d265, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c734 (pattern : Ten) (guard : d0 pattern = 1) : d2 pattern ≤ (0 : Int) + d137 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c735 (pattern : Ten) (guard : d384 pattern = 1) : d15 pattern ≤ (0 : Int) + d138 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d384, d15, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c393 pattern childGuard
    simpa only [d384, d15, d138, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d384, d15, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c734 pattern childGuard
    simpa only [d384, d15, d138, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c736 (pattern : Ten) (guard : d0 pattern = 1) : d5 pattern ≤ (0 : Int) + d12 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c737 (pattern : Ten) (guard : d387 pattern = 1) : d108 pattern ≤ (0 : Int) + d139 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d387, d108, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c735 pattern childGuard
    simpa only [d387, d108, d139, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d387, d108, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c736 pattern childGuard
    simpa only [d387, d108, d139, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c738 (pattern : Ten) (guard : d387 pattern = 1) : d15 pattern ≤ (0 : Int) + d18 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d387, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c470 pattern childGuard
    simpa only [d387, d18, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d387, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c688 pattern childGuard
    simpa only [d387, d18, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c739 (pattern : Ten) (guard : d387 pattern = 1) : d109 pattern ≤ (0 : Int) + d142 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d387 pattern = 1 := by simpa only [d109, d142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c737 pattern childGuard
    simpa only [d109, d142, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d387 pattern = 1 := by simpa only [d109, d142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c738 pattern childGuard
    simpa only [d109, d142, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c740 (pattern : Ten) (guard : d0 pattern = 1) : d15 pattern ≤ (0 : Int) + d14 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c741 (pattern : Ten) (guard : d387 pattern = 1) : d15 pattern ≤ (0 : Int) + d140 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d387, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c470 pattern childGuard
    simpa only [d387, d140, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d387, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c740 pattern childGuard
    simpa only [d387, d140, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c742 (pattern : Ten) (guard : d387 pattern = 1) : d14 pattern ≤ (0 : Int) + d20 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d387, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c464 pattern childGuard
    simpa only [d387, d20, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d387, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c644 pattern childGuard
    simpa only [d387, d20, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c743 (pattern : Ten) (guard : d387 pattern = 1) : d110 pattern ≤ (0 : Int) + d143 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d387 pattern = 1 := by simpa only [d110, d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c741 pattern childGuard
    simpa only [d110, d143, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d387 pattern = 1 := by simpa only [d110, d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c742 pattern childGuard
    simpa only [d110, d143, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c744 (pattern : Ten) (guard : d387 pattern = 1) : d115 pattern ≤ (0 : Int) + d145 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d387 pattern = 1 := by simpa only [d115, d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c739 pattern childGuard
    simpa only [d115, d145, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d387 pattern = 1 := by simpa only [d115, d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c743 pattern childGuard
    simpa only [d115, d145, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c745 (pattern : Ten) (guard : d0 pattern = 1) : d15 pattern ≤ (0 : Int) + d16 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c746 (pattern : Ten) (guard : d387 pattern = 1) : d15 pattern ≤ (0 : Int) + d141 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d387, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c470 pattern childGuard
    simpa only [d387, d141, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d387, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c745 pattern childGuard
    simpa only [d387, d141, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c747 (pattern : Ten) (guard : d0 pattern = 1) : d4 pattern ≤ (0 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c748 (pattern : Ten) (guard : d384 pattern = 1) : d44 pattern ≤ (0 : Int) + d16 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d384, d44, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c412 pattern childGuard
    simpa only [d384, d44, d16, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d384, d44, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c747 pattern childGuard
    simpa only [d384, d44, d16, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c749 (pattern : Ten) (guard : d387 pattern = 1) : d44 pattern ≤ (0 : Int) + d22 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d387, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c748 pattern childGuard
    simpa only [d387, d22, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d387, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c699 pattern childGuard
    simpa only [d387, d22, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c750 (pattern : Ten) (guard : d387 pattern = 1) : d111 pattern ≤ (0 : Int) + d144 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d387 pattern = 1 := by simpa only [d111, d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c746 pattern childGuard
    simpa only [d111, d144, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d387 pattern = 1 := by simpa only [d111, d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c749 pattern childGuard
    simpa only [d111, d144, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c751 (pattern : Ten) (guard : d387 pattern = 1) : d116 pattern ≤ (0 : Int) + d146 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d387 pattern = 1 := by simpa only [d116, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c750 pattern childGuard
    simpa only [d116, d146, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d387 pattern = 1 := by simpa only [d116, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c743 pattern childGuard
    simpa only [d116, d146, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c752 (pattern : Ten) (guard : d387 pattern = 1) : d119 pattern ≤ (0 : Int) + d147 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d387 pattern = 1 := by simpa only [d119, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c744 pattern childGuard
    simpa only [d119, d147, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d387 pattern = 1 := by simpa only [d119, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c751 pattern childGuard
    simpa only [d119, d147, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c753 (pattern : Ten) (guard : d387 pattern = 1) : d112 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d387 pattern = 1 := by simpa only [d112, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c738 pattern childGuard
    simpa only [d112, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d387 pattern = 1 := by simpa only [d112, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c524 pattern childGuard
    simpa only [d112, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c754 (pattern : Ten) (guard : d387 pattern = 1) : d113 pattern ≤ (0 : Int) + d27 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d387 pattern = 1 := by simpa only [d113, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c742 pattern childGuard
    simpa only [d113, d27, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d387 pattern = 1 := by simpa only [d113, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c524 pattern childGuard
    simpa only [d113, d27, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c755 (pattern : Ten) (guard : d387 pattern = 1) : d117 pattern ≤ (0 : Int) + d31 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d387 pattern = 1 := by simpa only [d117, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c753 pattern childGuard
    simpa only [d117, d31, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d387 pattern = 1 := by simpa only [d117, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c754 pattern childGuard
    simpa only [d117, d31, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c756 (pattern : Ten) (guard : d387 pattern = 1) : d114 pattern ≤ (0 : Int) + d28 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d387 pattern = 1 := by simpa only [d114, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c749 pattern childGuard
    simpa only [d114, d28, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d387 pattern = 1 := by simpa only [d114, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c524 pattern childGuard
    simpa only [d114, d28, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c757 (pattern : Ten) (guard : d387 pattern = 1) : d118 pattern ≤ (0 : Int) + d32 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d387 pattern = 1 := by simpa only [d118, d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c756 pattern childGuard
    simpa only [d118, d32, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d387 pattern = 1 := by simpa only [d118, d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c754 pattern childGuard
    simpa only [d118, d32, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c758 (pattern : Ten) (guard : d387 pattern = 1) : d120 pattern ≤ (0 : Int) + d34 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d387 pattern = 1 := by simpa only [d120, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c755 pattern childGuard
    simpa only [d120, d34, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d387 pattern = 1 := by simpa only [d120, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c757 pattern childGuard
    simpa only [d120, d34, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c759 (pattern : Ten) (guard : d387 pattern = 1) : d121 pattern ≤ (0 : Int) + d148 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d387 pattern = 1 := by simpa only [d121, d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c752 pattern childGuard
    simpa only [d121, d148, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d387 pattern = 1 := by simpa only [d121, d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c758 pattern childGuard
    simpa only [d121, d148, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c760 (pattern : Ten) (guard : d387 pattern = 1) : d122 pattern ≤ (0 : Int) + d36 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d387 pattern = 1 := by simpa only [d122, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c758 pattern childGuard
    simpa only [d122, d36, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d387 pattern = 1 := by simpa only [d122, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c524 pattern childGuard
    simpa only [d122, d36, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c761 (pattern : Ten) (guard : d387 pattern = 1) : d123 pattern ≤ (0 : Int) + d149 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d387 pattern = 1 := by simpa only [d123, d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c759 pattern childGuard
    simpa only [d123, d149, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d387 pattern = 1 := by simpa only [d123, d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c760 pattern childGuard
    simpa only [d123, d149, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c762 (pattern : Ten) (guard : d0 pattern = 1) : d10 pattern ≤ (0 : Int) + d173 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c763 (pattern : Ten) (guard : d388 pattern = 1) : d266 pattern ≤ (0 : Int) + d173 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d383 pattern = 1 := by simpa only [d388, d266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c488 pattern childGuard
    simpa only [d388, d266, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d388, d266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c762 pattern childGuard
    simpa only [d388, d266, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c764 (pattern : Ten) (guard : d388 pattern = 1) : d174 pattern ≤ (0 : Int) + d177 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d383 pattern = 1 := by simpa only [d388, d177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c488 pattern childGuard
    simpa only [d388, d177, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d388, d177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c662 pattern childGuard
    simpa only [d388, d177, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c765 (pattern : Ten) (guard : d388 pattern = 1) : d267 pattern ≤ (0 : Int) + d302 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d388 pattern = 1 := by simpa only [d267, d302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c763 pattern childGuard
    simpa only [d267, d302, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d388 pattern = 1 := by simpa only [d267, d302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c764 pattern childGuard
    simpa only [d267, d302, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c766 (pattern : Ten) (guard : d388 pattern = 1) : d268 pattern ≤ (0 : Int) + d181 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d388 pattern = 1 := by simpa only [d268, d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c764 pattern childGuard
    simpa only [d268, d181, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d388 pattern = 1 := by simpa only [d268, d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c541 pattern childGuard
    simpa only [d268, d181, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c767 (pattern : Ten) (guard : d388 pattern = 1) : d271 pattern ≤ (0 : Int) + d304 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d388 pattern = 1 := by simpa only [d271, d304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c765 pattern childGuard
    simpa only [d271, d304, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d388 pattern = 1 := by simpa only [d271, d304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c766 pattern childGuard
    simpa only [d271, d304, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c768 (pattern : Ten) (guard : d0 pattern = 1) : d174 pattern ≤ (0 : Int) + d175 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c769 (pattern : Ten) (guard : d388 pattern = 1) : d174 pattern ≤ (0 : Int) + d301 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d383 pattern = 1 := by simpa only [d388, d301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c488 pattern childGuard
    simpa only [d388, d301, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d388, d301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c768 pattern childGuard
    simpa only [d388, d301, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c770 (pattern : Ten) (guard : d0 pattern = 1) : d193 pattern ≤ (0 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c771 (pattern : Ten) (guard : d383 pattern = 1) : d199 pattern ≤ (0 : Int) + d175 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d383, d199, d175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c441 pattern childGuard
    simpa only [d383, d199, d175, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d383, d199, d175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c770 pattern childGuard
    simpa only [d383, d199, d175, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c772 (pattern : Ten) (guard : d388 pattern = 1) : d199 pattern ≤ (0 : Int) + d179 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d383 pattern = 1 := by simpa only [d388, d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c771 pattern childGuard
    simpa only [d388, d179, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d388, d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c722 pattern childGuard
    simpa only [d388, d179, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c773 (pattern : Ten) (guard : d388 pattern = 1) : d269 pattern ≤ (0 : Int) + d303 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d388 pattern = 1 := by simpa only [d269, d303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c769 pattern childGuard
    simpa only [d269, d303, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d388 pattern = 1 := by simpa only [d269, d303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c772 pattern childGuard
    simpa only [d269, d303, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c774 (pattern : Ten) (guard : d388 pattern = 1) : d272 pattern ≤ (0 : Int) + d305 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d388 pattern = 1 := by simpa only [d272, d305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c773 pattern childGuard
    simpa only [d272, d305, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d388 pattern = 1 := by simpa only [d272, d305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c766 pattern childGuard
    simpa only [d272, d305, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c775 (pattern : Ten) (guard : d388 pattern = 1) : d275 pattern ≤ (0 : Int) + d306 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d388 pattern = 1 := by simpa only [d275, d306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c767 pattern childGuard
    simpa only [d275, d306, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d388 pattern = 1 := by simpa only [d275, d306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c774 pattern childGuard
    simpa only [d275, d306, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c776 (pattern : Ten) (guard : d388 pattern = 1) : d273 pattern ≤ (0 : Int) + d186 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d388 pattern = 1 := by simpa only [d273, d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c766 pattern childGuard
    simpa only [d273, d186, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d388 pattern = 1 := by simpa only [d273, d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c541 pattern childGuard
    simpa only [d273, d186, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c777 (pattern : Ten) (guard : d388 pattern = 1) : d270 pattern ≤ (0 : Int) + d183 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d388 pattern = 1 := by simpa only [d270, d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c772 pattern childGuard
    simpa only [d270, d183, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d388 pattern = 1 := by simpa only [d270, d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c541 pattern childGuard
    simpa only [d270, d183, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c778 (pattern : Ten) (guard : d388 pattern = 1) : d274 pattern ≤ (0 : Int) + d187 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d388 pattern = 1 := by simpa only [d274, d187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c777 pattern childGuard
    simpa only [d274, d187, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d388 pattern = 1 := by simpa only [d274, d187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c541 pattern childGuard
    simpa only [d274, d187, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c779 (pattern : Ten) (guard : d388 pattern = 1) : d276 pattern ≤ (0 : Int) + d189 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d388 pattern = 1 := by simpa only [d276, d189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c776 pattern childGuard
    simpa only [d276, d189, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d388 pattern = 1 := by simpa only [d276, d189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c778 pattern childGuard
    simpa only [d276, d189, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c780 (pattern : Ten) (guard : d388 pattern = 1) : d277 pattern ≤ (0 : Int) + d307 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d388 pattern = 1 := by simpa only [d277, d307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c775 pattern childGuard
    simpa only [d277, d307, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d388 pattern = 1 := by simpa only [d277, d307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c779 pattern childGuard
    simpa only [d277, d307, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c781 (pattern : Ten) (guard : d388 pattern = 1) : d278 pattern ≤ (0 : Int) + d191 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d388 pattern = 1 := by simpa only [d278, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c779 pattern childGuard
    simpa only [d278, d191, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d388 pattern = 1 := by simpa only [d278, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c541 pattern childGuard
    simpa only [d278, d191, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c782 (pattern : Ten) (guard : d388 pattern = 1) : d279 pattern ≤ (0 : Int) + d308 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d388 pattern = 1 := by simpa only [d279, d308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c780 pattern childGuard
    simpa only [d279, d308, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d388 pattern = 1 := by simpa only [d279, d308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c781 pattern childGuard
    simpa only [d279, d308, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c783 (pattern : Ten) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d49 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c784 (pattern : Ten) (guard : d373 pattern = 1) : d124 pattern ≤ (0 : Int) + d54 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d373, d124, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c224 pattern childGuard
    simpa only [d373, d124, d54, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d373, d124, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c783 pattern childGuard
    simpa only [d373, d124, d54, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c785 (pattern : Ten) (guard : d0 pattern = 1) : d48 pattern ≤ (0 : Int) + d49 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c786 (pattern : Ten) (guard : d373 pattern = 1) : d48 pattern ≤ (0 : Int) + d54 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d373, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c224 pattern childGuard
    simpa only [d373, d54, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d373, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c785 pattern childGuard
    simpa only [d373, d54, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c787 (pattern : Ten) (guard : d373 pattern = 1) : d125 pattern ≤ (0 : Int) + d54 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d373 pattern = 1 := by simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c784 pattern childGuard
    simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d373 pattern = 1 := by simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c786 pattern childGuard
    simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c788 (pattern : Ten) (guard : d373 pattern = 1) : d128 pattern ≤ (0 : Int) + d54 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d373 pattern = 1 := by simpa only [d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c787 pattern childGuard
    simpa only [d128, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d373 pattern = 1 := by simpa only [d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c786 pattern childGuard
    simpa only [d128, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c789 (pattern : Ten) (guard : d0 pattern = 1) : d20 pattern ≤ (0 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c790 (pattern : Ten) (guard : d373 pattern = 1) : d20 pattern ≤ (0 : Int) + d27 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d373, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c231 pattern childGuard
    simpa only [d373, d27, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d373, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c789 pattern childGuard
    simpa only [d373, d27, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c791 (pattern : Ten) (guard : d373 pattern = 1) : d126 pattern ≤ (0 : Int) + d58 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d373 pattern = 1 := by simpa only [d126, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c786 pattern childGuard
    simpa only [d126, d58, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d373 pattern = 1 := by simpa only [d126, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c790 pattern childGuard
    simpa only [d126, d58, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c792 (pattern : Ten) (guard : d0 pattern = 1) : d50 pattern ≤ (0 : Int) + d51 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c793 (pattern : Ten) (guard : d373 pattern = 1) : d50 pattern ≤ (0 : Int) + d55 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d373, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c235 pattern childGuard
    simpa only [d373, d55, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d373, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c792 pattern childGuard
    simpa only [d373, d55, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c794 (pattern : Ten) (guard : d373 pattern = 1) : d127 pattern ≤ (0 : Int) + d59 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d373 pattern = 1 := by simpa only [d127, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c793 pattern childGuard
    simpa only [d127, d59, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d373 pattern = 1 := by simpa only [d127, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c790 pattern childGuard
    simpa only [d127, d59, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c795 (pattern : Ten) (guard : d373 pattern = 1) : d129 pattern ≤ (0 : Int) + d62 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d373 pattern = 1 := by simpa only [d129, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c791 pattern childGuard
    simpa only [d129, d62, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d373 pattern = 1 := by simpa only [d129, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c794 pattern childGuard
    simpa only [d129, d62, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c796 (pattern : Ten) (guard : d373 pattern = 1) : d130 pattern ≤ (0 : Int) + d64 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d373 pattern = 1 := by simpa only [d130, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c788 pattern childGuard
    simpa only [d130, d64, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d373 pattern = 1 := by simpa only [d130, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c795 pattern childGuard
    simpa only [d130, d64, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c797 (pattern : Ten) (guard : d0 pattern = 1) : d131 pattern ≤ (0 : Int) + d7 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c798 (pattern : Ten) (guard : d374 pattern = 1) : d132 pattern ≤ (0 : Int) + d133 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d373 pattern = 1 := by simpa only [d374, d132, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c796 pattern childGuard
    simpa only [d374, d132, d133, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d374, d132, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c797 pattern childGuard
    simpa only [d374, d132, d133, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c799 (pattern : Ten) (guard : d0 pattern = 1) : d10 pattern ≤ (0 : Int) + d203 pattern := by
  change (0 : Int) = 1 at guard
  omega
end NetHack.Sokoban41.Diagram
