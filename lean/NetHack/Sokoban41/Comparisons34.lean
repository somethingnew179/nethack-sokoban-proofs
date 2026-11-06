/- Staged soko4-1 certificate. No result until all kernel checks pass. -/
import NetHack.Sokoban41.Comparisons33
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban41.Diagram
theorem c5440 (pattern : Ten) (guard : d758 pattern = 1) : d135 pattern ≤ (0 : Int) + d4 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d757 pattern = 1 := by simpa only [d758, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5438 pattern childGuard
    simpa only [d758, d135, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d758, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5439 pattern childGuard
    simpa only [d758, d135, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5441 (pattern : Ten) (guard : d1 pattern = 1) : d4 pattern ≤ (0 : Int) + d4 pattern := by
  omega
theorem c5442 (pattern : Ten) (guard : d356 pattern = 1) : d136 pattern ≤ (0 : Int) + d4 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d356, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5441 pattern childGuard
    simpa only [d356, d136, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d356, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1072 pattern childGuard
    simpa only [d356, d136, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5443 (pattern : Ten) (guard : d358 pattern = 1) : d137 pattern ≤ (0 : Int) + d4 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d356 pattern = 1 := by simpa only [d358, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5442 pattern childGuard
    simpa only [d358, d137, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d358, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1072 pattern childGuard
    simpa only [d358, d137, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5444 (pattern : Ten) (guard : d359 pattern = 1) : d137 pattern ≤ (0 : Int) + d4 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d358 pattern = 1 := by simpa only [d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5443 pattern childGuard
    simpa only [d359, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1036 pattern childGuard
    simpa only [d359, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5445 (pattern : Ten) (guard : d752 pattern = 1) : d138 pattern ≤ (0 : Int) + d4 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d752, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c394 pattern childGuard
    simpa only [d752, d138, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d359 pattern = 1 := by simpa only [d752, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5444 pattern childGuard
    simpa only [d752, d138, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5446 (pattern : Ten) (guard : d753 pattern = 1) : d139 pattern ≤ (0 : Int) + d4 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d752 pattern = 1 := by simpa only [d753, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5445 pattern childGuard
    simpa only [d753, d139, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d753, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5363 pattern childGuard
    simpa only [d753, d139, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5447 (pattern : Ten) (guard : d754 pattern = 1) : d142 pattern ≤ (0 : Int) + d4 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d753 pattern = 1 := by simpa only [d754, d142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5446 pattern childGuard
    simpa only [d754, d142, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d754, d142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5365 pattern childGuard
    simpa only [d754, d142, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5448 (pattern : Ten) (guard : d0 pattern = 1) : d143 pattern ≤ (0 : Int) + d4 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5449 (pattern : Ten) (guard : d755 pattern = 1) : d145 pattern ≤ (0 : Int) + d4 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d754 pattern = 1 := by simpa only [d755, d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5447 pattern childGuard
    simpa only [d755, d145, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d755, d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5448 pattern childGuard
    simpa only [d755, d145, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5450 (pattern : Ten) (guard : d0 pattern = 1) : d146 pattern ≤ (0 : Int) + d4 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5451 (pattern : Ten) (guard : d756 pattern = 1) : d147 pattern ≤ (0 : Int) + d4 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d755 pattern = 1 := by simpa only [d756, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5449 pattern childGuard
    simpa only [d756, d147, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d756, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5450 pattern childGuard
    simpa only [d756, d147, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5452 (pattern : Ten) (guard : d757 pattern = 1) : d148 pattern ≤ (0 : Int) + d4 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d756 pattern = 1 := by simpa only [d757, d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5451 pattern childGuard
    simpa only [d757, d148, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d757, d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5371 pattern childGuard
    simpa only [d757, d148, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5453 (pattern : Ten) (guard : d758 pattern = 1) : d149 pattern ≤ (0 : Int) + d4 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d757 pattern = 1 := by simpa only [d758, d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5452 pattern childGuard
    simpa only [d758, d149, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d758, d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5373 pattern childGuard
    simpa only [d758, d149, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5454 (pattern : Ten) (guard : d0 pattern = 1) : d9 pattern ≤ (0 : Int) + d4 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5455 (pattern : Ten) (guard : d755 pattern = 1) : d150 pattern ≤ (0 : Int) + d4 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d754 pattern = 1 := by simpa only [d755, d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5380 pattern childGuard
    simpa only [d755, d150, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d755, d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5454 pattern childGuard
    simpa only [d755, d150, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5456 (pattern : Ten) (guard : d756 pattern = 1) : d151 pattern ≤ (0 : Int) + d4 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d755 pattern = 1 := by simpa only [d756, d151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5455 pattern childGuard
    simpa only [d756, d151, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d756, d151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5381 pattern childGuard
    simpa only [d756, d151, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5457 (pattern : Ten) (guard : d0 pattern = 1) : d152 pattern ≤ (0 : Int) + d4 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5458 (pattern : Ten) (guard : d757 pattern = 1) : d154 pattern ≤ (0 : Int) + d4 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d756 pattern = 1 := by simpa only [d757, d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5456 pattern childGuard
    simpa only [d757, d154, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d757, d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5457 pattern childGuard
    simpa only [d757, d154, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5459 (pattern : Ten) (guard : d0 pattern = 1) : d155 pattern ≤ (0 : Int) + d4 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5460 (pattern : Ten) (guard : d758 pattern = 1) : d156 pattern ≤ (0 : Int) + d4 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d757 pattern = 1 := by simpa only [d758, d156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5458 pattern childGuard
    simpa only [d758, d156, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d758, d156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5459 pattern childGuard
    simpa only [d758, d156, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5461 (pattern : Ten) (guard : d0 pattern = 1) : d55 pattern ≤ (0 : Int) + d4 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5462 (pattern : Ten) (guard : d755 pattern = 1) : d160 pattern ≤ (0 : Int) + d4 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d754 pattern = 1 := by simpa only [d755, d160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5380 pattern childGuard
    simpa only [d755, d160, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d755, d160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5461 pattern childGuard
    simpa only [d755, d160, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5463 (pattern : Ten) (guard : d0 pattern = 1) : d161 pattern ≤ (0 : Int) + d4 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5464 (pattern : Ten) (guard : d756 pattern = 1) : d165 pattern ≤ (0 : Int) + d4 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d755 pattern = 1 := by simpa only [d756, d165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5462 pattern childGuard
    simpa only [d756, d165, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d756, d165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5463 pattern childGuard
    simpa only [d756, d165, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5465 (pattern : Ten) (guard : d0 pattern = 1) : d166 pattern ≤ (0 : Int) + d4 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5466 (pattern : Ten) (guard : d757 pattern = 1) : d168 pattern ≤ (0 : Int) + d4 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d756 pattern = 1 := by simpa only [d757, d168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5464 pattern childGuard
    simpa only [d757, d168, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d757, d168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5465 pattern childGuard
    simpa only [d757, d168, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5467 (pattern : Ten) (guard : d0 pattern = 1) : d169 pattern ≤ (0 : Int) + d4 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5468 (pattern : Ten) (guard : d758 pattern = 1) : d170 pattern ≤ (0 : Int) + d4 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d757 pattern = 1 := by simpa only [d758, d170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5466 pattern childGuard
    simpa only [d758, d170, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d758, d170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5467 pattern childGuard
    simpa only [d758, d170, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5469 (pattern : Ten) (guard : d359 pattern = 1) : d171 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d358 pattern = 1 := by simpa only [d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c359 pattern childGuard
    simpa only [d359, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c292 pattern childGuard
    simpa only [d359, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5470 (pattern : Ten) (guard : d606 pattern = 1) : d171 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d359 pattern = 1 := by simpa only [d606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5469 pattern childGuard
    simpa only [d606, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c292 pattern childGuard
    simpa only [d606, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5471 (pattern : Ten) (guard : d0 pattern = 1) : d173 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5472 (pattern : Ten) (guard : d607 pattern = 1) : d176 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d606 pattern = 1 := by simpa only [d607, d176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5470 pattern childGuard
    simpa only [d607, d176, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d607, d176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5471 pattern childGuard
    simpa only [d607, d176, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5473 (pattern : Ten) (guard : d0 pattern = 1) : d177 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5474 (pattern : Ten) (guard : d608 pattern = 1) : d180 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d607 pattern = 1 := by simpa only [d608, d180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5472 pattern childGuard
    simpa only [d608, d180, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d608, d180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5473 pattern childGuard
    simpa only [d608, d180, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5475 (pattern : Ten) (guard : d0 pattern = 1) : d181 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5476 (pattern : Ten) (guard : d609 pattern = 1) : d184 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d608 pattern = 1 := by simpa only [d609, d184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5474 pattern childGuard
    simpa only [d609, d184, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d609, d184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5475 pattern childGuard
    simpa only [d609, d184, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5477 (pattern : Ten) (guard : d0 pattern = 1) : d185 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5478 (pattern : Ten) (guard : d610 pattern = 1) : d188 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d609 pattern = 1 := by simpa only [d610, d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5476 pattern childGuard
    simpa only [d610, d188, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d610, d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5477 pattern childGuard
    simpa only [d610, d188, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5479 (pattern : Ten) (guard : d0 pattern = 1) : d189 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5480 (pattern : Ten) (guard : d611 pattern = 1) : d190 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d610 pattern = 1 := by simpa only [d611, d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5478 pattern childGuard
    simpa only [d611, d190, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d611, d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5479 pattern childGuard
    simpa only [d611, d190, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5481 (pattern : Ten) (guard : d0 pattern = 1) : d191 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5482 (pattern : Ten) (guard : d612 pattern = 1) : d192 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d611 pattern = 1 := by simpa only [d612, d192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5480 pattern childGuard
    simpa only [d612, d192, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d612, d192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5481 pattern childGuard
    simpa only [d612, d192, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5483 (pattern : Ten) (guard : d0 pattern = 1) : d172 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5484 (pattern : Ten) (guard : d606 pattern = 1) : d174 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d359 pattern = 1 := by simpa only [d606, d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5469 pattern childGuard
    simpa only [d606, d174, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d606, d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5483 pattern childGuard
    simpa only [d606, d174, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5485 (pattern : Ten) (guard : d0 pattern = 1) : d197 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5486 (pattern : Ten) (guard : d607 pattern = 1) : d202 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d606 pattern = 1 := by simpa only [d607, d202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5484 pattern childGuard
    simpa only [d607, d202, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d607, d202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5485 pattern childGuard
    simpa only [d607, d202, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5487 (pattern : Ten) (guard : d0 pattern = 1) : d203 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5488 (pattern : Ten) (guard : d608 pattern = 1) : d207 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d607 pattern = 1 := by simpa only [d608, d207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5486 pattern childGuard
    simpa only [d608, d207, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d608, d207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5487 pattern childGuard
    simpa only [d608, d207, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5489 (pattern : Ten) (guard : d0 pattern = 1) : d207 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5490 (pattern : Ten) (guard : d609 pattern = 1) : d207 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d608 pattern = 1 := by simpa only [d609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5488 pattern childGuard
    simpa only [d609, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5489 pattern childGuard
    simpa only [d609, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5491 (pattern : Ten) (guard : d610 pattern = 1) : d207 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d609 pattern = 1 := by simpa only [d610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5490 pattern childGuard
    simpa only [d610, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5489 pattern childGuard
    simpa only [d610, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5492 (pattern : Ten) (guard : d0 pattern = 1) : d215 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5493 (pattern : Ten) (guard : d611 pattern = 1) : d218 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d610 pattern = 1 := by simpa only [d611, d218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5491 pattern childGuard
    simpa only [d611, d218, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d611, d218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5492 pattern childGuard
    simpa only [d611, d218, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5494 (pattern : Ten) (guard : d0 pattern = 1) : d219 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5495 (pattern : Ten) (guard : d612 pattern = 1) : d220 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d611 pattern = 1 := by simpa only [d612, d220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5493 pattern childGuard
    simpa only [d612, d220, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d612, d220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5494 pattern childGuard
    simpa only [d612, d220, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5496 (pattern : Ten) (guard : d358 pattern = 1) : d221 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d356 pattern = 1 := by simpa only [d358, d221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c181 pattern childGuard
    simpa only [d358, d221, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d358, d221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c356 pattern childGuard
    simpa only [d358, d221, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5497 (pattern : Ten) (guard : d359 pattern = 1) : d222 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d358 pattern = 1 := by simpa only [d359, d222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5496 pattern childGuard
    simpa only [d359, d222, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d359, d222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4603 pattern childGuard
    simpa only [d359, d222, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5498 (pattern : Ten) (guard : d606 pattern = 1) : d223 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d359 pattern = 1 := by simpa only [d606, d223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5497 pattern childGuard
    simpa only [d606, d223, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d606, d223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4603 pattern childGuard
    simpa only [d606, d223, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5499 (pattern : Ten) (guard : d607 pattern = 1) : d224 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d606 pattern = 1 := by simpa only [d607, d224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5498 pattern childGuard
    simpa only [d607, d224, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d607, d224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2784 pattern childGuard
    simpa only [d607, d224, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5500 (pattern : Ten) (guard : d608 pattern = 1) : d225 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d607 pattern = 1 := by simpa only [d608, d225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5499 pattern childGuard
    simpa only [d608, d225, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d608, d225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4566 pattern childGuard
    simpa only [d608, d225, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5501 (pattern : Ten) (guard : d0 pattern = 1) : d26 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5502 (pattern : Ten) (guard : d609 pattern = 1) : d226 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d608 pattern = 1 := by simpa only [d609, d226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5500 pattern childGuard
    simpa only [d609, d226, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d609, d226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5501 pattern childGuard
    simpa only [d609, d226, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5503 (pattern : Ten) (guard : d0 pattern = 1) : d227 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5504 (pattern : Ten) (guard : d610 pattern = 1) : d230 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d609 pattern = 1 := by simpa only [d610, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5502 pattern childGuard
    simpa only [d610, d230, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d610, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5503 pattern childGuard
    simpa only [d610, d230, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5505 (pattern : Ten) (guard : d0 pattern = 1) : d231 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5506 (pattern : Ten) (guard : d611 pattern = 1) : d232 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d610 pattern = 1 := by simpa only [d611, d232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5504 pattern childGuard
    simpa only [d611, d232, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d611, d232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5505 pattern childGuard
    simpa only [d611, d232, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5507 (pattern : Ten) (guard : d0 pattern = 1) : d233 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5508 (pattern : Ten) (guard : d612 pattern = 1) : d234 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d611 pattern = 1 := by simpa only [d612, d234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5506 pattern childGuard
    simpa only [d612, d234, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d612, d234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5507 pattern childGuard
    simpa only [d612, d234, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5509 (pattern : Ten) (guard : d610 pattern = 1) : d235 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d609 pattern = 1 := by simpa only [d610, d235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5490 pattern childGuard
    simpa only [d610, d235, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d610, d235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c356 pattern childGuard
    simpa only [d610, d235, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5510 (pattern : Ten) (guard : d0 pattern = 1) : d211 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5511 (pattern : Ten) (guard : d611 pattern = 1) : d236 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d610 pattern = 1 := by simpa only [d611, d236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5509 pattern childGuard
    simpa only [d611, d236, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d611, d236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5510 pattern childGuard
    simpa only [d611, d236, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5512 (pattern : Ten) (guard : d0 pattern = 1) : d237 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5513 (pattern : Ten) (guard : d612 pattern = 1) : d238 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d611 pattern = 1 := by simpa only [d612, d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5511 pattern childGuard
    simpa only [d612, d238, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d612, d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5512 pattern childGuard
    simpa only [d612, d238, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5514 (pattern : Ten) (guard : d358 pattern = 1) : d240 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d356 pattern = 1 := by simpa only [d358, d240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c357 pattern childGuard
    simpa only [d358, d240, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d358, d240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c31 pattern childGuard
    simpa only [d358, d240, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5515 (pattern : Ten) (guard : d359 pattern = 1) : d241 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d358 pattern = 1 := by simpa only [d359, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5514 pattern childGuard
    simpa only [d359, d241, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d359, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c292 pattern childGuard
    simpa only [d359, d241, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5516 (pattern : Ten) (guard : d606 pattern = 1) : d242 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d359 pattern = 1 := by simpa only [d606, d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5515 pattern childGuard
    simpa only [d606, d242, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d606, d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c292 pattern childGuard
    simpa only [d606, d242, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5517 (pattern : Ten) (guard : d607 pattern = 1) : d243 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d606 pattern = 1 := by simpa only [d607, d243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5516 pattern childGuard
    simpa only [d607, d243, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d607, d243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5471 pattern childGuard
    simpa only [d607, d243, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5518 (pattern : Ten) (guard : d608 pattern = 1) : d244 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d607 pattern = 1 := by simpa only [d608, d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5517 pattern childGuard
    simpa only [d608, d244, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d608, d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5473 pattern childGuard
    simpa only [d608, d244, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5519 (pattern : Ten) (guard : d609 pattern = 1) : d245 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d608 pattern = 1 := by simpa only [d609, d245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5518 pattern childGuard
    simpa only [d609, d245, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d609, d245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5475 pattern childGuard
    simpa only [d609, d245, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5520 (pattern : Ten) (guard : d610 pattern = 1) : d246 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d609 pattern = 1 := by simpa only [d610, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5519 pattern childGuard
    simpa only [d610, d246, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d610, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5477 pattern childGuard
    simpa only [d610, d246, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5521 (pattern : Ten) (guard : d611 pattern = 1) : d247 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d610 pattern = 1 := by simpa only [d611, d247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5520 pattern childGuard
    simpa only [d611, d247, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d611, d247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5479 pattern childGuard
    simpa only [d611, d247, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5522 (pattern : Ten) (guard : d612 pattern = 1) : d248 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d611 pattern = 1 := by simpa only [d612, d248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5521 pattern childGuard
    simpa only [d612, d248, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d612, d248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5481 pattern childGuard
    simpa only [d612, d248, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5523 (pattern : Ten) (guard : d606 pattern = 1) : d173 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d359 pattern = 1 := by simpa only [d606, d173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5469 pattern childGuard
    simpa only [d606, d173, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d606, d173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c356 pattern childGuard
    simpa only [d606, d173, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5524 (pattern : Ten) (guard : d607 pattern = 1) : d249 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d606 pattern = 1 := by simpa only [d607, d249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5523 pattern childGuard
    simpa only [d607, d249, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d607, d249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c292 pattern childGuard
    simpa only [d607, d249, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5525 (pattern : Ten) (guard : d0 pattern = 1) : d250 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5526 (pattern : Ten) (guard : d608 pattern = 1) : d253 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d607 pattern = 1 := by simpa only [d608, d253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5524 pattern childGuard
    simpa only [d608, d253, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d608, d253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5525 pattern childGuard
    simpa only [d608, d253, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5527 (pattern : Ten) (guard : d0 pattern = 1) : d254 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5528 (pattern : Ten) (guard : d609 pattern = 1) : d257 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d608 pattern = 1 := by simpa only [d609, d257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5526 pattern childGuard
    simpa only [d609, d257, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d609, d257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5527 pattern childGuard
    simpa only [d609, d257, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5529 (pattern : Ten) (guard : d0 pattern = 1) : d258 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5530 (pattern : Ten) (guard : d610 pattern = 1) : d261 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d609 pattern = 1 := by simpa only [d610, d261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5528 pattern childGuard
    simpa only [d610, d261, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d610, d261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5529 pattern childGuard
    simpa only [d610, d261, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5531 (pattern : Ten) (guard : d0 pattern = 1) : d262 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5532 (pattern : Ten) (guard : d611 pattern = 1) : d263 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d610 pattern = 1 := by simpa only [d611, d263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5530 pattern childGuard
    simpa only [d611, d263, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d611, d263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5531 pattern childGuard
    simpa only [d611, d263, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5533 (pattern : Ten) (guard : d0 pattern = 1) : d264 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5534 (pattern : Ten) (guard : d612 pattern = 1) : d265 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d611 pattern = 1 := by simpa only [d612, d265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5532 pattern childGuard
    simpa only [d612, d265, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d612, d265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5533 pattern childGuard
    simpa only [d612, d265, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5535 (pattern : Ten) (guard : d607 pattern = 1) : d266 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d606 pattern = 1 := by simpa only [d607, d266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5484 pattern childGuard
    simpa only [d607, d266, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d607, d266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c356 pattern childGuard
    simpa only [d607, d266, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5536 (pattern : Ten) (guard : d0 pattern = 1) : d174 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5537 (pattern : Ten) (guard : d608 pattern = 1) : d267 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d607 pattern = 1 := by simpa only [d608, d267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5535 pattern childGuard
    simpa only [d608, d267, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d608, d267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5536 pattern childGuard
    simpa only [d608, d267, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5538 (pattern : Ten) (guard : d0 pattern = 1) : d268 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5539 (pattern : Ten) (guard : d609 pattern = 1) : d271 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d608 pattern = 1 := by simpa only [d609, d271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5537 pattern childGuard
    simpa only [d609, d271, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d609, d271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5538 pattern childGuard
    simpa only [d609, d271, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5540 (pattern : Ten) (guard : d0 pattern = 1) : d272 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5541 (pattern : Ten) (guard : d610 pattern = 1) : d275 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d609 pattern = 1 := by simpa only [d610, d275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5539 pattern childGuard
    simpa only [d610, d275, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d610, d275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5540 pattern childGuard
    simpa only [d610, d275, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5542 (pattern : Ten) (guard : d0 pattern = 1) : d276 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5543 (pattern : Ten) (guard : d611 pattern = 1) : d277 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d610 pattern = 1 := by simpa only [d611, d277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5541 pattern childGuard
    simpa only [d611, d277, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d611, d277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5542 pattern childGuard
    simpa only [d611, d277, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5544 (pattern : Ten) (guard : d0 pattern = 1) : d278 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5545 (pattern : Ten) (guard : d612 pattern = 1) : d279 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d611 pattern = 1 := by simpa only [d612, d279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5543 pattern childGuard
    simpa only [d612, d279, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d612, d279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5544 pattern childGuard
    simpa only [d612, d279, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5546 (pattern : Ten) (guard : d608 pattern = 1) : d280 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d607 pattern = 1 := by simpa only [d608, d280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5486 pattern childGuard
    simpa only [d608, d280, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d608, d280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c356 pattern childGuard
    simpa only [d608, d280, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5547 (pattern : Ten) (guard : d0 pattern = 1) : d202 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5548 (pattern : Ten) (guard : d609 pattern = 1) : d281 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d608 pattern = 1 := by simpa only [d609, d281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5546 pattern childGuard
    simpa only [d609, d281, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d609, d281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5547 pattern childGuard
    simpa only [d609, d281, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5549 (pattern : Ten) (guard : d610 pattern = 1) : d284 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d609 pattern = 1 := by simpa only [d610, d284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5548 pattern childGuard
    simpa only [d610, d284, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d610, d284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5547 pattern childGuard
    simpa only [d610, d284, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5550 (pattern : Ten) (guard : d0 pattern = 1) : d285 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5551 (pattern : Ten) (guard : d611 pattern = 1) : d286 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d610 pattern = 1 := by simpa only [d611, d286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5549 pattern childGuard
    simpa only [d611, d286, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d611, d286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5550 pattern childGuard
    simpa only [d611, d286, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5552 (pattern : Ten) (guard : d0 pattern = 1) : d287 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5553 (pattern : Ten) (guard : d612 pattern = 1) : d288 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d611 pattern = 1 := by simpa only [d612, d288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5551 pattern childGuard
    simpa only [d612, d288, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d612, d288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5552 pattern childGuard
    simpa only [d612, d288, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5554 (pattern : Ten) (guard : d612 pattern = 1) : d289 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d611 pattern = 1 := by simpa only [d612, d289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5493 pattern childGuard
    simpa only [d612, d289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d612, d289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c356 pattern childGuard
    simpa only [d612, d289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5555 (pattern : Ten) (guard : d611 pattern = 1) : d290 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d610 pattern = 1 := by simpa only [d611, d290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5491 pattern childGuard
    simpa only [d611, d290, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d611, d290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c356 pattern childGuard
    simpa only [d611, d290, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5556 (pattern : Ten) (guard : d0 pattern = 1) : d209 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5557 (pattern : Ten) (guard : d612 pattern = 1) : d291 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d611 pattern = 1 := by simpa only [d612, d291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5555 pattern childGuard
    simpa only [d612, d291, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d612, d291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5556 pattern childGuard
    simpa only [d612, d291, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5558 (pattern : Ten) (guard : d359 pattern = 1) : d292 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d358 pattern = 1 := by simpa only [d359, d292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c359 pattern childGuard
    simpa only [d359, d292, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d359, d292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4603 pattern childGuard
    simpa only [d359, d292, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5559 (pattern : Ten) (guard : d606 pattern = 1) : d293 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d359 pattern = 1 := by simpa only [d606, d293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5558 pattern childGuard
    simpa only [d606, d293, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d606, d293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5483 pattern childGuard
    simpa only [d606, d293, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5560 (pattern : Ten) (guard : d607 pattern = 1) : d294 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d606 pattern = 1 := by simpa only [d607, d294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5559 pattern childGuard
    simpa only [d607, d294, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d607, d294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5485 pattern childGuard
    simpa only [d607, d294, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5561 (pattern : Ten) (guard : d608 pattern = 1) : d295 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d607 pattern = 1 := by simpa only [d608, d295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5560 pattern childGuard
    simpa only [d608, d295, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d608, d295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5487 pattern childGuard
    simpa only [d608, d295, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5562 (pattern : Ten) (guard : d609 pattern = 1) : d296 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d608 pattern = 1 := by simpa only [d609, d296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5561 pattern childGuard
    simpa only [d609, d296, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d609, d296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5489 pattern childGuard
    simpa only [d609, d296, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5563 (pattern : Ten) (guard : d610 pattern = 1) : d297 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d609 pattern = 1 := by simpa only [d610, d297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5562 pattern childGuard
    simpa only [d610, d297, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d610, d297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5489 pattern childGuard
    simpa only [d610, d297, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5564 (pattern : Ten) (guard : d611 pattern = 1) : d298 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d610 pattern = 1 := by simpa only [d611, d298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5563 pattern childGuard
    simpa only [d611, d298, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d611, d298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5492 pattern childGuard
    simpa only [d611, d298, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5565 (pattern : Ten) (guard : d0 pattern = 1) : d299 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5566 (pattern : Ten) (guard : d612 pattern = 1) : d300 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d611 pattern = 1 := by simpa only [d612, d300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5564 pattern childGuard
    simpa only [d612, d300, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d612, d300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5565 pattern childGuard
    simpa only [d612, d300, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5567 (pattern : Ten) (guard : d607 pattern = 1) : d173 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d606 pattern = 1 := by simpa only [d607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5523 pattern childGuard
    simpa only [d607, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5471 pattern childGuard
    simpa only [d607, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5568 (pattern : Ten) (guard : d608 pattern = 1) : d302 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d607 pattern = 1 := by simpa only [d608, d302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5567 pattern childGuard
    simpa only [d608, d302, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d608, d302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5473 pattern childGuard
    simpa only [d608, d302, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5569 (pattern : Ten) (guard : d609 pattern = 1) : d304 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d608 pattern = 1 := by simpa only [d609, d304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5568 pattern childGuard
    simpa only [d609, d304, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d609, d304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5475 pattern childGuard
    simpa only [d609, d304, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5570 (pattern : Ten) (guard : d0 pattern = 1) : d305 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5571 (pattern : Ten) (guard : d610 pattern = 1) : d306 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d609 pattern = 1 := by simpa only [d610, d306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5569 pattern childGuard
    simpa only [d610, d306, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d610, d306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5570 pattern childGuard
    simpa only [d610, d306, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5572 (pattern : Ten) (guard : d611 pattern = 1) : d307 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d610 pattern = 1 := by simpa only [d611, d307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5571 pattern childGuard
    simpa only [d611, d307, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d611, d307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5479 pattern childGuard
    simpa only [d611, d307, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5573 (pattern : Ten) (guard : d612 pattern = 1) : d308 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d611 pattern = 1 := by simpa only [d612, d308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5572 pattern childGuard
    simpa only [d612, d308, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d612, d308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5481 pattern childGuard
    simpa only [d612, d308, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5574 (pattern : Ten) (guard : d609 pattern = 1) : d211 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d608 pattern = 1 := by simpa only [d609, d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5488 pattern childGuard
    simpa only [d609, d211, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d609, d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c356 pattern childGuard
    simpa only [d609, d211, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5575 (pattern : Ten) (guard : d610 pattern = 1) : d326 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d609 pattern = 1 := by simpa only [d610, d326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5574 pattern childGuard
    simpa only [d610, d326, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d610, d326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5489 pattern childGuard
    simpa only [d610, d326, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5576 (pattern : Ten) (guard : d0 pattern = 1) : d327 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5577 (pattern : Ten) (guard : d611 pattern = 1) : d329 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d610 pattern = 1 := by simpa only [d611, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5575 pattern childGuard
    simpa only [d611, d329, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d611, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5576 pattern childGuard
    simpa only [d611, d329, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5578 (pattern : Ten) (guard : d0 pattern = 1) : d330 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5579 (pattern : Ten) (guard : d612 pattern = 1) : d331 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d611 pattern = 1 := by simpa only [d612, d331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5577 pattern childGuard
    simpa only [d612, d331, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d612, d331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5578 pattern childGuard
    simpa only [d612, d331, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5580 (pattern : Ten) (guard : d0 pattern = 1) : d324 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5581 (pattern : Ten) (guard : d609 pattern = 1) : d332 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d608 pattern = 1 := by simpa only [d609, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5488 pattern childGuard
    simpa only [d609, d332, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d609, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5580 pattern childGuard
    simpa only [d609, d332, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5582 (pattern : Ten) (guard : d0 pattern = 1) : d332 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5583 (pattern : Ten) (guard : d610 pattern = 1) : d332 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d609 pattern = 1 := by simpa only [d610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5581 pattern childGuard
    simpa only [d610, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5582 pattern childGuard
    simpa only [d610, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5584 (pattern : Ten) (guard : d0 pattern = 1) : d336 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5585 (pattern : Ten) (guard : d611 pattern = 1) : d338 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d610 pattern = 1 := by simpa only [d611, d338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5583 pattern childGuard
    simpa only [d611, d338, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d611, d338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5584 pattern childGuard
    simpa only [d611, d338, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5586 (pattern : Ten) (guard : d0 pattern = 1) : d339 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5587 (pattern : Ten) (guard : d612 pattern = 1) : d340 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d611 pattern = 1 := by simpa only [d612, d340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5585 pattern childGuard
    simpa only [d612, d340, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d612, d340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5586 pattern childGuard
    simpa only [d612, d340, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5588 (pattern : Ten) (guard : d0 pattern = 1) : d325 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5589 (pattern : Ten) (guard : d609 pattern = 1) : d344 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d608 pattern = 1 := by simpa only [d609, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5488 pattern childGuard
    simpa only [d609, d344, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d609, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5588 pattern childGuard
    simpa only [d609, d344, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5590 (pattern : Ten) (guard : d0 pattern = 1) : d345 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5591 (pattern : Ten) (guard : d610 pattern = 1) : d346 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d609 pattern = 1 := by simpa only [d610, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5589 pattern childGuard
    simpa only [d610, d346, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d610, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5590 pattern childGuard
    simpa only [d610, d346, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5592 (pattern : Ten) (guard : d611 pattern = 1) : d347 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d610 pattern = 1 := by simpa only [d611, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5591 pattern childGuard
    simpa only [d611, d347, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d611, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5584 pattern childGuard
    simpa only [d611, d347, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5593 (pattern : Ten) (guard : d0 pattern = 1) : d348 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5594 (pattern : Ten) (guard : d612 pattern = 1) : d349 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d611 pattern = 1 := by simpa only [d612, d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5592 pattern childGuard
    simpa only [d612, d349, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d612, d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5593 pattern childGuard
    simpa only [d612, d349, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5595 (pattern : Ten) (guard : d759 pattern = 1) : d171 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c292 pattern childGuard
    simpa only [d759, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d358 pattern = 1 := by simpa only [d759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c359 pattern childGuard
    simpa only [d759, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5596 (pattern : Ten) (guard : d778 pattern = 1) : d171 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d759 pattern = 1 := by simpa only [d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5595 pattern childGuard
    simpa only [d778, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c292 pattern childGuard
    simpa only [d778, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5597 (pattern : Ten) (guard : d779 pattern = 1) : d176 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d778 pattern = 1 := by simpa only [d779, d176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5596 pattern childGuard
    simpa only [d779, d176, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d779, d176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5471 pattern childGuard
    simpa only [d779, d176, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5598 (pattern : Ten) (guard : d780 pattern = 1) : d180 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d779 pattern = 1 := by simpa only [d780, d180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5597 pattern childGuard
    simpa only [d780, d180, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d780, d180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5473 pattern childGuard
    simpa only [d780, d180, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5599 (pattern : Ten) (guard : d781 pattern = 1) : d184 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d780 pattern = 1 := by simpa only [d781, d184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5598 pattern childGuard
    simpa only [d781, d184, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d781, d184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5475 pattern childGuard
    simpa only [d781, d184, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban41.Diagram
