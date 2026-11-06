/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons023
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c3360 (pattern : Twelve) (guard : d1867 pattern = 1) : d4 pattern ≤ (0 : Int) + d13 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3358 pattern childGuard
    simpa only [d1867, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3359 pattern childGuard
    simpa only [d1867, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3361 (pattern : Twelve) (guard : d1867 pattern = 1) : d38 pattern ≤ (0 : Int) + d667 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d38, d667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3357 pattern childGuard
    simpa only [d38, d667, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d38, d667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3360 pattern childGuard
    simpa only [d38, d667, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3362 (pattern : Twelve) (guard : d1867 pattern = 1) : d39 pattern ≤ (0 : Int) + d668 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d39, d668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3295 pattern childGuard
    simpa only [d39, d668, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d39, d668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d39, d668, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3363 (pattern : Twelve) (guard : d1867 pattern = 1) : d59 pattern ≤ (0 : Int) + d696 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d59, d696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3361 pattern childGuard
    simpa only [d59, d696, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d59, d696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3362 pattern childGuard
    simpa only [d59, d696, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3364 (pattern : Twelve) (guard : d1867 pattern = 1) : d38 pattern ≤ (0 : Int) + d669 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d38, d669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3295 pattern childGuard
    simpa only [d38, d669, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d38, d669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3360 pattern childGuard
    simpa only [d38, d669, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3365 (pattern : Twelve) (guard : d1867 pattern = 1) : d40 pattern ≤ (0 : Int) + d668 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d40, d668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3305 pattern childGuard
    simpa only [d40, d668, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d40, d668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d40, d668, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3366 (pattern : Twelve) (guard : d1867 pattern = 1) : d60 pattern ≤ (0 : Int) + d697 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d60, d697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3364 pattern childGuard
    simpa only [d60, d697, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d60, d697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3365 pattern childGuard
    simpa only [d60, d697, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3367 (pattern : Twelve) (guard : d1867 pattern = 1) : d81 pattern ≤ (0 : Int) + d719 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d81, d719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3363 pattern childGuard
    simpa only [d81, d719, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d81, d719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3366 pattern childGuard
    simpa only [d81, d719, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3368 (pattern : Twelve) (guard : d1867 pattern = 1) : d59 pattern ≤ (0 : Int) + d697 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d59, d697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3364 pattern childGuard
    simpa only [d59, d697, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d59, d697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3362 pattern childGuard
    simpa only [d59, d697, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3369 (pattern : Twelve) (guard : d0 pattern = 1) : d15 pattern ≤ (0 : Int) + d13 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3370 (pattern : Twelve) (guard : d1867 pattern = 1) : d24 pattern ≤ (0 : Int) + d13 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3358 pattern childGuard
    simpa only [d1867, d24, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3369 pattern childGuard
    simpa only [d1867, d24, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3371 (pattern : Twelve) (guard : d1867 pattern = 1) : d41 pattern ≤ (0 : Int) + d669 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d41, d669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3305 pattern childGuard
    simpa only [d41, d669, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d41, d669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3370 pattern childGuard
    simpa only [d41, d669, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3372 (pattern : Twelve) (guard : d1866 pattern = 1) : d16 pattern ≤ (0 : Int) + d160 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1866, d16, d160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1333 pattern childGuard
    simpa only [d1866, d16, d160, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1866, d16, d160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1334 pattern childGuard
    simpa only [d1866, d16, d160, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3373 (pattern : Twelve) (guard : d0 pattern = 1) : d12 pattern ≤ (0 : Int) + d159 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3374 (pattern : Twelve) (guard : d1867 pattern = 1) : d25 pattern ≤ (0 : Int) + d644 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d25, d644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3372 pattern childGuard
    simpa only [d1867, d25, d644, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d25, d644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3373 pattern childGuard
    simpa only [d1867, d25, d644, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3375 (pattern : Twelve) (guard : d1867 pattern = 1) : d42 pattern ≤ (0 : Int) + d670 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d42, d670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3374 pattern childGuard
    simpa only [d42, d670, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d42, d670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d42, d670, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3376 (pattern : Twelve) (guard : d1867 pattern = 1) : d61 pattern ≤ (0 : Int) + d698 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d61, d698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3371 pattern childGuard
    simpa only [d61, d698, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d61, d698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3375 pattern childGuard
    simpa only [d61, d698, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3377 (pattern : Twelve) (guard : d1867 pattern = 1) : d82 pattern ≤ (0 : Int) + d720 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d82, d720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3368 pattern childGuard
    simpa only [d82, d720, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d82, d720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3376 pattern childGuard
    simpa only [d82, d720, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3378 (pattern : Twelve) (guard : d1867 pattern = 1) : d96 pattern ≤ (0 : Int) + d741 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d96, d741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3367 pattern childGuard
    simpa only [d96, d741, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d96, d741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3377 pattern childGuard
    simpa only [d96, d741, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3379 (pattern : Twelve) (guard : d1867 pattern = 1) : d104 pattern ≤ (0 : Int) + d756 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d104, d756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3354 pattern childGuard
    simpa only [d104, d756, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d104, d756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3378 pattern childGuard
    simpa only [d104, d756, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3380 (pattern : Twelve) (guard : d0 pattern = 1) : d0 pattern ≤ (0 : Int) + d5 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3381 (pattern : Twelve) (guard : d1866 pattern = 1) : d0 pattern ≤ (0 : Int) + d633 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1866, d633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1866, d633, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1866, d633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3380 pattern childGuard
    simpa only [d1866, d633, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3382 (pattern : Twelve) (guard : d1867 pattern = 1) : d0 pattern ≤ (0 : Int) + d645 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3381 pattern childGuard
    simpa only [d1867, d645, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2841 pattern childGuard
    simpa only [d1867, d645, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3383 (pattern : Twelve) (guard : d1867 pattern = 1) : d30 pattern ≤ (0 : Int) + d671 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d30, d671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3382 pattern childGuard
    simpa only [d30, d671, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d30, d671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3295 pattern childGuard
    simpa only [d30, d671, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3384 (pattern : Twelve) (guard : d1867 pattern = 1) : d56 pattern ≤ (0 : Int) + d699 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d56, d699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3383 pattern childGuard
    simpa only [d56, d699, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d56, d699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3327 pattern childGuard
    simpa only [d56, d699, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3385 (pattern : Twelve) (guard : d1867 pattern = 1) : d77 pattern ≤ (0 : Int) + d721 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d77, d721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3384 pattern childGuard
    simpa only [d77, d721, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d77, d721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3331 pattern childGuard
    simpa only [d77, d721, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3386 (pattern : Twelve) (guard : d1867 pattern = 1) : d94 pattern ≤ (0 : Int) + d742 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d94, d742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3385 pattern childGuard
    simpa only [d94, d742, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d94, d742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3334 pattern childGuard
    simpa only [d94, d742, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3387 (pattern : Twelve) (guard : d1867 pattern = 1) : d105 pattern ≤ (0 : Int) + d757 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d105, d757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3386 pattern childGuard
    simpa only [d105, d757, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d105, d757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d105, d757, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3388 (pattern : Twelve) (guard : d1867 pattern = 1) : d111 pattern ≤ (0 : Int) + d767 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d111, d767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3379 pattern childGuard
    simpa only [d111, d767, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d111, d767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3387 pattern childGuard
    simpa only [d111, d767, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3389 (pattern : Twelve) (guard : d1867 pattern = 1) : d114 pattern ≤ (0 : Int) + d772 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d114, d772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3337 pattern childGuard
    simpa only [d114, d772, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d114, d772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3388 pattern childGuard
    simpa only [d114, d772, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3390 (pattern : Twelve) (guard : d1867 pattern = 1) : d26 pattern ≤ (0 : Int) + d661 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d26, d661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3265 pattern childGuard
    simpa only [d26, d661, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d26, d661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3259 pattern childGuard
    simpa only [d26, d661, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3391 (pattern : Twelve) (guard : d1867 pattern = 1) : d50 pattern ≤ (0 : Int) + d661 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3390 pattern childGuard
    simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3317 pattern childGuard
    simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3392 (pattern : Twelve) (guard : d1867 pattern = 1) : d72 pattern ≤ (0 : Int) + d722 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d72, d722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3265 pattern childGuard
    simpa only [d72, d722, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d72, d722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3391 pattern childGuard
    simpa only [d72, d722, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3393 (pattern : Twelve) (guard : d1867 pattern = 1) : d28 pattern ≤ (0 : Int) + d672 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d28, d672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3297 pattern childGuard
    simpa only [d28, d672, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d28, d672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3270 pattern childGuard
    simpa only [d28, d672, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3394 (pattern : Twelve) (guard : d1867 pattern = 1) : d51 pattern ≤ (0 : Int) + d700 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d51, d700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3393 pattern childGuard
    simpa only [d51, d700, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d51, d700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3276 pattern childGuard
    simpa only [d51, d700, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3395 (pattern : Twelve) (guard : d1867 pattern = 1) : d73 pattern ≤ (0 : Int) + d723 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d73, d723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3265 pattern childGuard
    simpa only [d73, d723, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d73, d723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3394 pattern childGuard
    simpa only [d73, d723, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3396 (pattern : Twelve) (guard : d1867 pattern = 1) : d91 pattern ≤ (0 : Int) + d743 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d91, d743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3392 pattern childGuard
    simpa only [d91, d743, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d91, d743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3395 pattern childGuard
    simpa only [d91, d743, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3397 (pattern : Twelve) (guard : d1867 pattern = 1) : d31 pattern ≤ (0 : Int) + d673 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d31, d673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3265 pattern childGuard
    simpa only [d31, d673, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d31, d673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3291 pattern childGuard
    simpa only [d31, d673, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3398 (pattern : Twelve) (guard : d1867 pattern = 1) : d52 pattern ≤ (0 : Int) + d701 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d52, d701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3329 pattern childGuard
    simpa only [d52, d701, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d52, d701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3397 pattern childGuard
    simpa only [d52, d701, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3399 (pattern : Twelve) (guard : d1867 pattern = 1) : d53 pattern ≤ (0 : Int) + d702 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d53, d702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3329 pattern childGuard
    simpa only [d53, d702, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d53, d702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3299 pattern childGuard
    simpa only [d53, d702, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3400 (pattern : Twelve) (guard : d1867 pattern = 1) : d74 pattern ≤ (0 : Int) + d724 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d74, d724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3398 pattern childGuard
    simpa only [d74, d724, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d74, d724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3399 pattern childGuard
    simpa only [d74, d724, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3401 (pattern : Twelve) (guard : d1867 pattern = 1) : d54 pattern ≤ (0 : Int) + d703 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d54, d703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3329 pattern childGuard
    simpa only [d54, d703, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d54, d703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3303 pattern childGuard
    simpa only [d54, d703, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3402 (pattern : Twelve) (guard : d1867 pattern = 1) : d75 pattern ≤ (0 : Int) + d725 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d75, d725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3401 pattern childGuard
    simpa only [d75, d725, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d75, d725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3307 pattern childGuard
    simpa only [d75, d725, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3403 (pattern : Twelve) (guard : d1867 pattern = 1) : d92 pattern ≤ (0 : Int) + d744 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d92, d744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3400 pattern childGuard
    simpa only [d92, d744, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d92, d744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3402 pattern childGuard
    simpa only [d92, d744, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3404 (pattern : Twelve) (guard : d1867 pattern = 1) : d102 pattern ≤ (0 : Int) + d758 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d102, d758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3396 pattern childGuard
    simpa only [d102, d758, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d102, d758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3403 pattern childGuard
    simpa only [d102, d758, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3405 (pattern : Twelve) (guard : d1867 pattern = 1) : d76 pattern ≤ (0 : Int) + d726 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d76, d726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3265 pattern childGuard
    simpa only [d76, d726, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d76, d726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3307 pattern childGuard
    simpa only [d76, d726, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3406 (pattern : Twelve) (guard : d1867 pattern = 1) : d93 pattern ≤ (0 : Int) + d745 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d93, d745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3392 pattern childGuard
    simpa only [d93, d745, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d93, d745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3405 pattern childGuard
    simpa only [d93, d745, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3407 (pattern : Twelve) (guard : d1867 pattern = 1) : d77 pattern ≤ (0 : Int) + d692 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3333 pattern childGuard
    simpa only [d77, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3331 pattern childGuard
    simpa only [d77, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3408 (pattern : Twelve) (guard : d1867 pattern = 1) : d94 pattern ≤ (0 : Int) + d746 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d94, d746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3407 pattern childGuard
    simpa only [d94, d746, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d94, d746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3334 pattern childGuard
    simpa only [d94, d746, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3409 (pattern : Twelve) (guard : d1867 pattern = 1) : d103 pattern ≤ (0 : Int) + d759 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d103, d759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3406 pattern childGuard
    simpa only [d103, d759, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d103, d759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3408 pattern childGuard
    simpa only [d103, d759, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3410 (pattern : Twelve) (guard : d1867 pattern = 1) : d110 pattern ≤ (0 : Int) + d768 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d110, d768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3404 pattern childGuard
    simpa only [d110, d768, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d110, d768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3409 pattern childGuard
    simpa only [d110, d768, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3411 (pattern : Twelve) (guard : d1867 pattern = 1) : d58 pattern ≤ (0 : Int) + d704 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d58, d704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3329 pattern childGuard
    simpa only [d58, d704, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d58, d704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3349 pattern childGuard
    simpa only [d58, d704, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3412 (pattern : Twelve) (guard : d1867 pattern = 1) : d79 pattern ≤ (0 : Int) + d727 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d79, d727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3329 pattern childGuard
    simpa only [d79, d727, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d79, d727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3411 pattern childGuard
    simpa only [d79, d727, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3413 (pattern : Twelve) (guard : d1867 pattern = 1) : d80 pattern ≤ (0 : Int) + d728 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d80, d728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3329 pattern childGuard
    simpa only [d80, d728, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d80, d728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3307 pattern childGuard
    simpa only [d80, d728, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3414 (pattern : Twelve) (guard : d1867 pattern = 1) : d95 pattern ≤ (0 : Int) + d747 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d95, d747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3412 pattern childGuard
    simpa only [d95, d747, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d95, d747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3413 pattern childGuard
    simpa only [d95, d747, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3415 (pattern : Twelve) (guard : d1867 pattern = 1) : d81 pattern ≤ (0 : Int) + d697 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3368 pattern childGuard
    simpa only [d81, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3366 pattern childGuard
    simpa only [d81, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3416 (pattern : Twelve) (guard : d1867 pattern = 1) : d96 pattern ≤ (0 : Int) + d748 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d96, d748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3415 pattern childGuard
    simpa only [d96, d748, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d96, d748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3377 pattern childGuard
    simpa only [d96, d748, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3417 (pattern : Twelve) (guard : d1867 pattern = 1) : d104 pattern ≤ (0 : Int) + d760 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d104, d760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3414 pattern childGuard
    simpa only [d104, d760, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d104, d760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3416 pattern childGuard
    simpa only [d104, d760, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3418 (pattern : Twelve) (guard : d1867 pattern = 1) : d105 pattern ≤ (0 : Int) + d761 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d105, d761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3408 pattern childGuard
    simpa only [d105, d761, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d105, d761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d105, d761, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3419 (pattern : Twelve) (guard : d1867 pattern = 1) : d111 pattern ≤ (0 : Int) + d769 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d111, d769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3417 pattern childGuard
    simpa only [d111, d769, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d111, d769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3418 pattern childGuard
    simpa only [d111, d769, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3420 (pattern : Twelve) (guard : d1867 pattern = 1) : d114 pattern ≤ (0 : Int) + d773 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d114, d773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3410 pattern childGuard
    simpa only [d114, d773, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d114, d773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3419 pattern childGuard
    simpa only [d114, d773, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3421 (pattern : Twelve) (guard : d1867 pattern = 1) : d114 pattern ≤ (0 : Int) + d775 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3389 pattern childGuard
    simpa only [d775, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3420 pattern childGuard
    simpa only [d775, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3422 (pattern : Twelve) (guard : d1867 pattern = 1) : d114 pattern ≤ (0 : Int) + d776 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3421 pattern childGuard
    simpa only [d776, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3420 pattern childGuard
    simpa only [d776, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3423 (pattern : Twelve) (guard : d1867 pattern = 1) : d120 pattern ≤ (0 : Int) + d674 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d120, d674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3297 pattern childGuard
    simpa only [d120, d674, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d120, d674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3374 pattern childGuard
    simpa only [d120, d674, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3424 (pattern : Twelve) (guard : d1867 pattern = 1) : d129 pattern ≤ (0 : Int) + d705 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d129, d705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3423 pattern childGuard
    simpa only [d129, d705, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d129, d705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3276 pattern childGuard
    simpa only [d129, d705, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3425 (pattern : Twelve) (guard : d1867 pattern = 1) : d136 pattern ≤ (0 : Int) + d729 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d136, d729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3265 pattern childGuard
    simpa only [d136, d729, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d136, d729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3424 pattern childGuard
    simpa only [d136, d729, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3426 (pattern : Twelve) (guard : d1867 pattern = 1) : d144 pattern ≤ (0 : Int) + d749 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d144, d749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3392 pattern childGuard
    simpa only [d144, d749, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d144, d749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3425 pattern childGuard
    simpa only [d144, d749, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3427 (pattern : Twelve) (guard : d1867 pattern = 1) : d121 pattern ≤ (0 : Int) + d657 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d121, d657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3265 pattern childGuard
    simpa only [d121, d657, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d121, d657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3305 pattern childGuard
    simpa only [d121, d657, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3428 (pattern : Twelve) (guard : d1867 pattern = 1) : d130 pattern ≤ (0 : Int) + d692 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d130, d692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3427 pattern childGuard
    simpa only [d130, d692, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d130, d692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3330 pattern childGuard
    simpa only [d130, d692, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3429 (pattern : Twelve) (guard : d1867 pattern = 1) : d137 pattern ≤ (0 : Int) + d730 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d137, d730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3398 pattern childGuard
    simpa only [d137, d730, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d137, d730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3428 pattern childGuard
    simpa only [d137, d730, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3430 (pattern : Twelve) (guard : d1867 pattern = 1) : d138 pattern ≤ (0 : Int) + d731 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d138, d731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3333 pattern childGuard
    simpa only [d138, d731, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d138, d731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3424 pattern childGuard
    simpa only [d138, d731, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3431 (pattern : Twelve) (guard : d1867 pattern = 1) : d145 pattern ≤ (0 : Int) + d750 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d145, d750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3429 pattern childGuard
    simpa only [d145, d750, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d145, d750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3430 pattern childGuard
    simpa only [d145, d750, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3432 (pattern : Twelve) (guard : d1867 pattern = 1) : d149 pattern ≤ (0 : Int) + d762 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d149, d762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3426 pattern childGuard
    simpa only [d149, d762, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d149, d762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3431 pattern childGuard
    simpa only [d149, d762, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3433 (pattern : Twelve) (guard : d1867 pattern = 1) : d139 pattern ≤ (0 : Int) + d692 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3333 pattern childGuard
    simpa only [d139, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3428 pattern childGuard
    simpa only [d139, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3434 (pattern : Twelve) (guard : d1867 pattern = 1) : d146 pattern ≤ (0 : Int) + d751 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d146, d751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3433 pattern childGuard
    simpa only [d146, d751, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d146, d751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3430 pattern childGuard
    simpa only [d146, d751, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3435 (pattern : Twelve) (guard : d1867 pattern = 1) : d150 pattern ≤ (0 : Int) + d763 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d150, d763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3426 pattern childGuard
    simpa only [d150, d763, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d150, d763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3434 pattern childGuard
    simpa only [d150, d763, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3436 (pattern : Twelve) (guard : d1867 pattern = 1) : d153 pattern ≤ (0 : Int) + d770 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d153, d770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3432 pattern childGuard
    simpa only [d153, d770, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d153, d770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3435 pattern childGuard
    simpa only [d153, d770, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3437 (pattern : Twelve) (guard : d1867 pattern = 1) : d122 pattern ≤ (0 : Int) + d675 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d122, d675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3297 pattern childGuard
    simpa only [d122, d675, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d122, d675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3360 pattern childGuard
    simpa only [d122, d675, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3438 (pattern : Twelve) (guard : d1867 pattern = 1) : d131 pattern ≤ (0 : Int) + d706 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d131, d706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3427 pattern childGuard
    simpa only [d131, d706, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d131, d706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3437 pattern childGuard
    simpa only [d131, d706, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3439 (pattern : Twelve) (guard : d1867 pattern = 1) : d140 pattern ≤ (0 : Int) + d732 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d140, d732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3329 pattern childGuard
    simpa only [d140, d732, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d140, d732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3438 pattern childGuard
    simpa only [d140, d732, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3440 (pattern : Twelve) (guard : d1867 pattern = 1) : d123 pattern ≤ (0 : Int) + d666 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d123, d666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3265 pattern childGuard
    simpa only [d123, d666, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d123, d666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3348 pattern childGuard
    simpa only [d123, d666, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3441 (pattern : Twelve) (guard : d1867 pattern = 1) : d132 pattern ≤ (0 : Int) + d704 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d132, d704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3329 pattern childGuard
    simpa only [d132, d704, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d132, d704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3440 pattern childGuard
    simpa only [d132, d704, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3442 (pattern : Twelve) (guard : d1867 pattern = 1) : d141 pattern ≤ (0 : Int) + d733 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d141, d733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3441 pattern childGuard
    simpa only [d141, d733, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d141, d733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3424 pattern childGuard
    simpa only [d141, d733, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3443 (pattern : Twelve) (guard : d1867 pattern = 1) : d147 pattern ≤ (0 : Int) + d752 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d147, d752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3439 pattern childGuard
    simpa only [d147, d752, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d147, d752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3442 pattern childGuard
    simpa only [d147, d752, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3444 (pattern : Twelve) (guard : d1866 pattern = 1) : d5 pattern ≤ (0 : Int) + d14 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1866, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3017 pattern childGuard
    simpa only [d1866, d14, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1866, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3025 pattern childGuard
    simpa only [d1866, d14, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3445 (pattern : Twelve) (guard : d0 pattern = 1) : d14 pattern ≤ (0 : Int) + d14 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3446 (pattern : Twelve) (guard : d1867 pattern = 1) : d118 pattern ≤ (0 : Int) + d14 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3444 pattern childGuard
    simpa only [d1867, d118, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3445 pattern childGuard
    simpa only [d1867, d118, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3447 (pattern : Twelve) (guard : d1867 pattern = 1) : d124 pattern ≤ (0 : Int) + d676 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d124, d676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3295 pattern childGuard
    simpa only [d124, d676, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d124, d676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3446 pattern childGuard
    simpa only [d124, d676, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3448 (pattern : Twelve) (guard : d0 pattern = 1) : d117 pattern ≤ (0 : Int) + d159 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3449 (pattern : Twelve) (guard : d1867 pattern = 1) : d119 pattern ≤ (0 : Int) + d159 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3346 pattern childGuard
    simpa only [d1867, d119, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3448 pattern childGuard
    simpa only [d1867, d119, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3450 (pattern : Twelve) (guard : d1867 pattern = 1) : d125 pattern ≤ (0 : Int) + d677 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d125, d677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3449 pattern childGuard
    simpa only [d125, d677, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d125, d677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d125, d677, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3451 (pattern : Twelve) (guard : d1867 pattern = 1) : d133 pattern ≤ (0 : Int) + d707 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d133, d707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3447 pattern childGuard
    simpa only [d133, d707, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d133, d707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3450 pattern childGuard
    simpa only [d133, d707, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3452 (pattern : Twelve) (guard : d1867 pattern = 1) : d142 pattern ≤ (0 : Int) + d734 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d142, d734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3368 pattern childGuard
    simpa only [d142, d734, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d142, d734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3451 pattern childGuard
    simpa only [d142, d734, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3453 (pattern : Twelve) (guard : d0 pattern = 1) : d5 pattern ≤ (0 : Int) + d14 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3454 (pattern : Twelve) (guard : d1867 pattern = 1) : d5 pattern ≤ (0 : Int) + d14 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3444 pattern childGuard
    simpa only [d1867, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3453 pattern childGuard
    simpa only [d1867, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3455 (pattern : Twelve) (guard : d1867 pattern = 1) : d126 pattern ≤ (0 : Int) + d676 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d126, d676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3295 pattern childGuard
    simpa only [d126, d676, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d126, d676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3454 pattern childGuard
    simpa only [d126, d676, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3456 (pattern : Twelve) (guard : d1867 pattern = 1) : d47 pattern ≤ (0 : Int) + d677 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d47, d677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3348 pattern childGuard
    simpa only [d47, d677, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d47, d677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d47, d677, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3457 (pattern : Twelve) (guard : d1867 pattern = 1) : d134 pattern ≤ (0 : Int) + d707 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d134, d707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3455 pattern childGuard
    simpa only [d134, d707, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d134, d707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3456 pattern childGuard
    simpa only [d134, d707, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3458 (pattern : Twelve) (guard : d1867 pattern = 1) : d127 pattern ≤ (0 : Int) + d678 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d127, d678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3305 pattern childGuard
    simpa only [d127, d678, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d127, d678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3302 pattern childGuard
    simpa only [d127, d678, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3459 (pattern : Twelve) (guard : d1867 pattern = 1) : d128 pattern ≤ (0 : Int) + d679 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d128, d679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3291 pattern childGuard
    simpa only [d128, d679, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d128, d679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d128, d679, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3460 (pattern : Twelve) (guard : d1867 pattern = 1) : d135 pattern ≤ (0 : Int) + d708 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d135, d708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3458 pattern childGuard
    simpa only [d135, d708, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d135, d708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3459 pattern childGuard
    simpa only [d135, d708, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3461 (pattern : Twelve) (guard : d1867 pattern = 1) : d143 pattern ≤ (0 : Int) + d735 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d143, d735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3457 pattern childGuard
    simpa only [d143, d735, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d143, d735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3460 pattern childGuard
    simpa only [d143, d735, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3462 (pattern : Twelve) (guard : d1867 pattern = 1) : d148 pattern ≤ (0 : Int) + d753 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d148, d753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3452 pattern childGuard
    simpa only [d148, d753, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d148, d753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3461 pattern childGuard
    simpa only [d148, d753, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3463 (pattern : Twelve) (guard : d1867 pattern = 1) : d151 pattern ≤ (0 : Int) + d764 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d151, d764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3443 pattern childGuard
    simpa only [d151, d764, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d151, d764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3462 pattern childGuard
    simpa only [d151, d764, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3464 (pattern : Twelve) (guard : d1867 pattern = 1) : d152 pattern ≤ (0 : Int) + d765 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d152, d765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3434 pattern childGuard
    simpa only [d152, d765, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d152, d765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d152, d765, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3465 (pattern : Twelve) (guard : d1867 pattern = 1) : d154 pattern ≤ (0 : Int) + d771 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d154, d771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3463 pattern childGuard
    simpa only [d154, d771, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d154, d771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3464 pattern childGuard
    simpa only [d154, d771, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3466 (pattern : Twelve) (guard : d1867 pattern = 1) : d155 pattern ≤ (0 : Int) + d774 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d155, d774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3436 pattern childGuard
    simpa only [d155, d774, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d155, d774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3465 pattern childGuard
    simpa only [d155, d774, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3467 (pattern : Twelve) (guard : d1867 pattern = 1) : d156 pattern ≤ (0 : Int) + d777 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d156, d777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3422 pattern childGuard
    simpa only [d156, d777, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d156, d777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3466 pattern childGuard
    simpa only [d156, d777, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3468 (pattern : Twelve) (guard : d1866 pattern = 1) : d7 pattern ≤ (0 : Int) + d158 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1866, d7, d158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1866, d7, d158, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1866, d7, d158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1356 pattern childGuard
    simpa only [d1866, d7, d158, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3469 (pattern : Twelve) (guard : d1867 pattern = 1) : d814 pattern ≤ (0 : Int) + d636 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d814, d636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3468 pattern childGuard
    simpa only [d1867, d814, d636, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d814, d636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2832 pattern childGuard
    simpa only [d1867, d814, d636, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3470 (pattern : Twelve) (guard : d1867 pattern = 1) : d816 pattern ≤ (0 : Int) + d1183 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d816, d1183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3469 pattern childGuard
    simpa only [d816, d1183, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d816, d1183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3259 pattern childGuard
    simpa only [d816, d1183, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3471 (pattern : Twelve) (guard : d1867 pattern = 1) : d824 pattern ≤ (0 : Int) + d1189 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d824, d1189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3260 pattern childGuard
    simpa only [d824, d1189, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d824, d1189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3470 pattern childGuard
    simpa only [d824, d1189, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3472 (pattern : Twelve) (guard : d1867 pattern = 1) : d838 pattern ≤ (0 : Int) + d1199 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d838, d1199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3267 pattern childGuard
    simpa only [d838, d1199, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d838, d1199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3471 pattern childGuard
    simpa only [d838, d1199, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3473 (pattern : Twelve) (guard : d1867 pattern = 1) : d17 pattern ≤ (0 : Int) + d649 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3257 pattern childGuard
    simpa only [d649, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3297 pattern childGuard
    simpa only [d649, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3474 (pattern : Twelve) (guard : d1867 pattern = 1) : d17 pattern ≤ (0 : Int) + d1190 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3473 pattern childGuard
    simpa only [d1190, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3297 pattern childGuard
    simpa only [d1190, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3475 (pattern : Twelve) (guard : d1867 pattern = 1) : d817 pattern ≤ (0 : Int) + d1184 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d817, d1184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3274 pattern childGuard
    simpa only [d817, d1184, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d817, d1184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3374 pattern childGuard
    simpa only [d817, d1184, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3476 (pattern : Twelve) (guard : d1867 pattern = 1) : d825 pattern ≤ (0 : Int) + d1191 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d825, d1191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3475 pattern childGuard
    simpa only [d825, d1191, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d825, d1191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3375 pattern childGuard
    simpa only [d825, d1191, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3477 (pattern : Twelve) (guard : d1867 pattern = 1) : d839 pattern ≤ (0 : Int) + d1200 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d839, d1200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3474 pattern childGuard
    simpa only [d839, d1200, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d839, d1200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3476 pattern childGuard
    simpa only [d839, d1200, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3478 (pattern : Twelve) (guard : d1867 pattern = 1) : d853 pattern ≤ (0 : Int) + d1216 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d853, d1216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3472 pattern childGuard
    simpa only [d853, d1216, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d853, d1216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3477 pattern childGuard
    simpa only [d853, d1216, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3479 (pattern : Twelve) (guard : d1867 pattern = 1) : d56 pattern ≤ (0 : Int) + d1192 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d56, d1192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3296 pattern childGuard
    simpa only [d56, d1192, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d56, d1192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3327 pattern childGuard
    simpa only [d56, d1192, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3480 (pattern : Twelve) (guard : d1867 pattern = 1) : d818 pattern ≤ (0 : Int) + d651 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d818, d651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3469 pattern childGuard
    simpa only [d818, d651, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d818, d651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d818, d651, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3481 (pattern : Twelve) (guard : d1867 pattern = 1) : d826 pattern ≤ (0 : Int) + d687 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d826, d687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3306 pattern childGuard
    simpa only [d826, d687, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d826, d687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3480 pattern childGuard
    simpa only [d826, d687, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3482 (pattern : Twelve) (guard : d1867 pattern = 1) : d840 pattern ≤ (0 : Int) + d1201 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d840, d1201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3479 pattern childGuard
    simpa only [d840, d1201, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d840, d1201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3481 pattern childGuard
    simpa only [d840, d1201, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3483 (pattern : Twelve) (guard : d1867 pattern = 1) : d827 pattern ≤ (0 : Int) + d692 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d827, d692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3306 pattern childGuard
    simpa only [d827, d692, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d827, d692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3330 pattern childGuard
    simpa only [d827, d692, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3484 (pattern : Twelve) (guard : d1867 pattern = 1) : d841 pattern ≤ (0 : Int) + d1202 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d841, d1202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3483 pattern childGuard
    simpa only [d841, d1202, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d841, d1202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3476 pattern childGuard
    simpa only [d841, d1202, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3485 (pattern : Twelve) (guard : d1867 pattern = 1) : d854 pattern ≤ (0 : Int) + d1217 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d854, d1217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3482 pattern childGuard
    simpa only [d854, d1217, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d854, d1217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3484 pattern childGuard
    simpa only [d854, d1217, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3486 (pattern : Twelve) (guard : d1867 pattern = 1) : d861 pattern ≤ (0 : Int) + d1228 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d861, d1228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3478 pattern childGuard
    simpa only [d861, d1228, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d861, d1228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3485 pattern childGuard
    simpa only [d861, d1228, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3487 (pattern : Twelve) (guard : d1867 pattern = 1) : d824 pattern ≤ (0 : Int) + d1193 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d824, d1193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3317 pattern childGuard
    simpa only [d824, d1193, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d824, d1193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3470 pattern childGuard
    simpa only [d824, d1193, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3488 (pattern : Twelve) (guard : d1867 pattern = 1) : d838 pattern ≤ (0 : Int) + d1203 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d838, d1203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3320 pattern childGuard
    simpa only [d838, d1203, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d838, d1203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3487 pattern childGuard
    simpa only [d838, d1203, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3489 (pattern : Twelve) (guard : d1867 pattern = 1) : d839 pattern ≤ (0 : Int) + d1204 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d839, d1204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3297 pattern childGuard
    simpa only [d839, d1204, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d839, d1204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3476 pattern childGuard
    simpa only [d839, d1204, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3490 (pattern : Twelve) (guard : d1867 pattern = 1) : d853 pattern ≤ (0 : Int) + d1218 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d853, d1218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3488 pattern childGuard
    simpa only [d853, d1218, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d853, d1218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3489 pattern childGuard
    simpa only [d853, d1218, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3491 (pattern : Twelve) (guard : d1867 pattern = 1) : d840 pattern ≤ (0 : Int) + d716 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d840, d716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3333 pattern childGuard
    simpa only [d840, d716, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d840, d716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3481 pattern childGuard
    simpa only [d840, d716, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3492 (pattern : Twelve) (guard : d1867 pattern = 1) : d854 pattern ≤ (0 : Int) + d1219 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d854, d1219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3491 pattern childGuard
    simpa only [d854, d1219, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d854, d1219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3484 pattern childGuard
    simpa only [d854, d1219, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3493 (pattern : Twelve) (guard : d1867 pattern = 1) : d861 pattern ≤ (0 : Int) + d1229 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d861, d1229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3490 pattern childGuard
    simpa only [d861, d1229, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d861, d1229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3492 pattern childGuard
    simpa only [d861, d1229, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3494 (pattern : Twelve) (guard : d1867 pattern = 1) : d861 pattern ≤ (0 : Int) + d1237 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3486 pattern childGuard
    simpa only [d1237, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3493 pattern childGuard
    simpa only [d1237, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3495 (pattern : Twelve) (guard : d1867 pattern = 1) : d819 pattern ≤ (0 : Int) + d1185 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d819, d1185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3469 pattern childGuard
    simpa only [d819, d1185, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d819, d1185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3348 pattern childGuard
    simpa only [d819, d1185, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3496 (pattern : Twelve) (guard : d1867 pattern = 1) : d828 pattern ≤ (0 : Int) + d1194 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d828, d1194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3306 pattern childGuard
    simpa only [d828, d1194, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d828, d1194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3495 pattern childGuard
    simpa only [d828, d1194, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3497 (pattern : Twelve) (guard : d1867 pattern = 1) : d842 pattern ≤ (0 : Int) + d1205 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d842, d1205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3352 pattern childGuard
    simpa only [d842, d1205, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d842, d1205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3496 pattern childGuard
    simpa only [d842, d1205, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3498 (pattern : Twelve) (guard : d1867 pattern = 1) : d843 pattern ≤ (0 : Int) + d1206 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d843, d1206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3306 pattern childGuard
    simpa only [d843, d1206, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d843, d1206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3476 pattern childGuard
    simpa only [d843, d1206, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3499 (pattern : Twelve) (guard : d1867 pattern = 1) : d855 pattern ≤ (0 : Int) + d1220 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d855, d1220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3497 pattern childGuard
    simpa only [d855, d1220, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d855, d1220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3498 pattern childGuard
    simpa only [d855, d1220, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
