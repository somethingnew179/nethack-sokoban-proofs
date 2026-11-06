/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons052
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c7420 (pattern : Twelve) (guard : d1867 pattern = 1) : d563 pattern ≤ (0 : Int) + d711 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d563, d711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7414 pattern childGuard
    simpa only [d563, d711, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d563, d711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7419 pattern childGuard
    simpa only [d563, d711, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7421 (pattern : Twelve) (guard : d1867 pattern = 1) : d508 pattern ≤ (0 : Int) + d656 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d508, d656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7394 pattern childGuard
    simpa only [d508, d656, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d508, d656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3302 pattern childGuard
    simpa only [d508, d656, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7422 (pattern : Twelve) (guard : d1867 pattern = 1) : d538 pattern ≤ (0 : Int) + d686 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d538, d686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7416 pattern childGuard
    simpa only [d538, d686, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d538, d686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7421 pattern childGuard
    simpa only [d538, d686, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7423 (pattern : Twelve) (guard : d1867 pattern = 1) : d509 pattern ≤ (0 : Int) + d657 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d509, d657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7394 pattern childGuard
    simpa only [d509, d657, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d509, d657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7415 pattern childGuard
    simpa only [d509, d657, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7424 (pattern : Twelve) (guard : d1867 pattern = 1) : d539 pattern ≤ (0 : Int) + d687 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d539, d687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7423 pattern childGuard
    simpa only [d539, d687, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d539, d687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7401 pattern childGuard
    simpa only [d539, d687, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7425 (pattern : Twelve) (guard : d1867 pattern = 1) : d564 pattern ≤ (0 : Int) + d712 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d564, d712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7422 pattern childGuard
    simpa only [d564, d712, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d564, d712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7424 pattern childGuard
    simpa only [d564, d712, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7426 (pattern : Twelve) (guard : d1867 pattern = 1) : d589 pattern ≤ (0 : Int) + d737 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d589, d737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7420 pattern childGuard
    simpa only [d589, d737, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d589, d737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7425 pattern childGuard
    simpa only [d589, d737, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7427 (pattern : Twelve) (guard : d1867 pattern = 1) : d606 pattern ≤ (0 : Int) + d754 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d606, d754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7404 pattern childGuard
    simpa only [d606, d754, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d606, d754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7426 pattern childGuard
    simpa only [d606, d754, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7428 (pattern : Twelve) (guard : d0 pattern = 1) : d159 pattern ≤ (0 : Int) + d158 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c7429 (pattern : Twelve) (guard : d1867 pattern = 1) : d488 pattern ≤ (0 : Int) + d640 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d488, d640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3311 pattern childGuard
    simpa only [d1867, d488, d640, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d488, d640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7428 pattern childGuard
    simpa only [d1867, d488, d640, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7430 (pattern : Twelve) (guard : d1867 pattern = 1) : d510 pattern ≤ (0 : Int) + d658 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d510, d658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7406 pattern childGuard
    simpa only [d510, d658, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d510, d658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7429 pattern childGuard
    simpa only [d510, d658, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7431 (pattern : Twelve) (guard : d1867 pattern = 1) : d511 pattern ≤ (0 : Int) + d659 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d511, d659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7411 pattern childGuard
    simpa only [d511, d659, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d511, d659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7394 pattern childGuard
    simpa only [d511, d659, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7432 (pattern : Twelve) (guard : d1867 pattern = 1) : d540 pattern ≤ (0 : Int) + d688 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d540, d688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7430 pattern childGuard
    simpa only [d540, d688, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d540, d688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7431 pattern childGuard
    simpa only [d540, d688, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7433 (pattern : Twelve) (guard : d1867 pattern = 1) : d512 pattern ≤ (0 : Int) + d660 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d512, d660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7411 pattern childGuard
    simpa only [d512, d660, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d512, d660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7389 pattern childGuard
    simpa only [d512, d660, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7434 (pattern : Twelve) (guard : d1867 pattern = 1) : d513 pattern ≤ (0 : Int) + d661 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d513, d661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7394 pattern childGuard
    simpa only [d513, d661, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d513, d661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7389 pattern childGuard
    simpa only [d513, d661, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7435 (pattern : Twelve) (guard : d1867 pattern = 1) : d541 pattern ≤ (0 : Int) + d689 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d541, d689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7433 pattern childGuard
    simpa only [d541, d689, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d541, d689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7434 pattern childGuard
    simpa only [d541, d689, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7436 (pattern : Twelve) (guard : d1867 pattern = 1) : d565 pattern ≤ (0 : Int) + d713 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d565, d713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7432 pattern childGuard
    simpa only [d565, d713, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d565, d713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7435 pattern childGuard
    simpa only [d565, d713, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7437 (pattern : Twelve) (guard : d1867 pattern = 1) : d542 pattern ≤ (0 : Int) + d690 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d542, d690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7431 pattern childGuard
    simpa only [d542, d690, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d542, d690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7394 pattern childGuard
    simpa only [d542, d690, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7438 (pattern : Twelve) (guard : d1867 pattern = 1) : d566 pattern ≤ (0 : Int) + d714 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d566, d714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7437 pattern childGuard
    simpa only [d566, d714, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d566, d714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7424 pattern childGuard
    simpa only [d566, d714, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7439 (pattern : Twelve) (guard : d1867 pattern = 1) : d590 pattern ≤ (0 : Int) + d738 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d590, d738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7436 pattern childGuard
    simpa only [d590, d738, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d590, d738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7438 pattern childGuard
    simpa only [d590, d738, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7440 (pattern : Twelve) (guard : d0 pattern = 1) : d13 pattern ≤ (0 : Int) + d158 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c7441 (pattern : Twelve) (guard : d1867 pattern = 1) : d489 pattern ≤ (0 : Int) + d641 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d489, d641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3324 pattern childGuard
    simpa only [d1867, d489, d641, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d489, d641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7440 pattern childGuard
    simpa only [d1867, d489, d641, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7442 (pattern : Twelve) (guard : d1867 pattern = 1) : d514 pattern ≤ (0 : Int) + d662 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d514, d662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7441 pattern childGuard
    simpa only [d514, d662, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d514, d662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7415 pattern childGuard
    simpa only [d514, d662, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7443 (pattern : Twelve) (guard : d1867 pattern = 1) : d515 pattern ≤ (0 : Int) + d663 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d515, d663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7394 pattern childGuard
    simpa only [d515, d663, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d515, d663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d515, d663, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7444 (pattern : Twelve) (guard : d1867 pattern = 1) : d543 pattern ≤ (0 : Int) + d691 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d543, d691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7442 pattern childGuard
    simpa only [d543, d691, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d543, d691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7443 pattern childGuard
    simpa only [d543, d691, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7445 (pattern : Twelve) (guard : d1867 pattern = 1) : d544 pattern ≤ (0 : Int) + d692 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d544, d692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7423 pattern childGuard
    simpa only [d544, d692, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d544, d692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7443 pattern childGuard
    simpa only [d544, d692, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7446 (pattern : Twelve) (guard : d1867 pattern = 1) : d567 pattern ≤ (0 : Int) + d715 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d567, d715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7444 pattern childGuard
    simpa only [d567, d715, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d567, d715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7445 pattern childGuard
    simpa only [d567, d715, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7447 (pattern : Twelve) (guard : d1867 pattern = 1) : d568 pattern ≤ (0 : Int) + d716 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d568, d716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7445 pattern childGuard
    simpa only [d568, d716, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d568, d716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7424 pattern childGuard
    simpa only [d568, d716, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7448 (pattern : Twelve) (guard : d1867 pattern = 1) : d591 pattern ≤ (0 : Int) + d739 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d591, d739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7446 pattern childGuard
    simpa only [d591, d739, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d591, d739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7447 pattern childGuard
    simpa only [d591, d739, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7449 (pattern : Twelve) (guard : d1867 pattern = 1) : d607 pattern ≤ (0 : Int) + d755 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d607, d755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7439 pattern childGuard
    simpa only [d607, d755, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d607, d755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7448 pattern childGuard
    simpa only [d607, d755, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7450 (pattern : Twelve) (guard : d1867 pattern = 1) : d618 pattern ≤ (0 : Int) + d766 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d618, d766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7427 pattern childGuard
    simpa only [d618, d766, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d618, d766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7449 pattern childGuard
    simpa only [d618, d766, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7451 (pattern : Twelve) (guard : d0 pattern = 1) : d3 pattern ≤ (0 : Int) + d630 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c7452 (pattern : Twelve) (guard : d1867 pattern = 1) : d490 pattern ≤ (0 : Int) + d630 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3311 pattern childGuard
    simpa only [d1867, d490, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7451 pattern childGuard
    simpa only [d1867, d490, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7453 (pattern : Twelve) (guard : d0 pattern = 1) : d13 pattern ≤ (0 : Int) + d160 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c7454 (pattern : Twelve) (guard : d1867 pattern = 1) : d491 pattern ≤ (0 : Int) + d642 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d491, d642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3341 pattern childGuard
    simpa only [d1867, d491, d642, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d491, d642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7453 pattern childGuard
    simpa only [d1867, d491, d642, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7455 (pattern : Twelve) (guard : d1867 pattern = 1) : d516 pattern ≤ (0 : Int) + d664 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d516, d664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7452 pattern childGuard
    simpa only [d516, d664, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d516, d664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7454 pattern childGuard
    simpa only [d516, d664, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7456 (pattern : Twelve) (guard : d1867 pattern = 1) : d517 pattern ≤ (0 : Int) + d665 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d517, d665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7429 pattern childGuard
    simpa only [d517, d665, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d517, d665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7415 pattern childGuard
    simpa only [d517, d665, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7457 (pattern : Twelve) (guard : d1867 pattern = 1) : d545 pattern ≤ (0 : Int) + d693 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d545, d693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7455 pattern childGuard
    simpa only [d545, d693, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d545, d693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7456 pattern childGuard
    simpa only [d545, d693, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7458 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d159 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c7459 (pattern : Twelve) (guard : d1867 pattern = 1) : d492 pattern ≤ (0 : Int) + d159 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3346 pattern childGuard
    simpa only [d1867, d492, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7458 pattern childGuard
    simpa only [d1867, d492, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7460 (pattern : Twelve) (guard : d1867 pattern = 1) : d518 pattern ≤ (0 : Int) + d666 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d518, d666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7394 pattern childGuard
    simpa only [d518, d666, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d518, d666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7459 pattern childGuard
    simpa only [d518, d666, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7461 (pattern : Twelve) (guard : d1867 pattern = 1) : d546 pattern ≤ (0 : Int) + d694 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d546, d694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7456 pattern childGuard
    simpa only [d546, d694, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d546, d694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7460 pattern childGuard
    simpa only [d546, d694, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7462 (pattern : Twelve) (guard : d1867 pattern = 1) : d569 pattern ≤ (0 : Int) + d717 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d569, d717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7457 pattern childGuard
    simpa only [d569, d717, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d569, d717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7461 pattern childGuard
    simpa only [d569, d717, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7463 (pattern : Twelve) (guard : d1867 pattern = 1) : d547 pattern ≤ (0 : Int) + d695 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d547, d695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7456 pattern childGuard
    simpa only [d547, d695, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d547, d695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7423 pattern childGuard
    simpa only [d547, d695, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7464 (pattern : Twelve) (guard : d1867 pattern = 1) : d570 pattern ≤ (0 : Int) + d718 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d570, d718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7463 pattern childGuard
    simpa only [d570, d718, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d570, d718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7424 pattern childGuard
    simpa only [d570, d718, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7465 (pattern : Twelve) (guard : d1867 pattern = 1) : d592 pattern ≤ (0 : Int) + d740 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d592, d740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7462 pattern childGuard
    simpa only [d592, d740, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d592, d740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7464 pattern childGuard
    simpa only [d592, d740, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7466 (pattern : Twelve) (guard : d0 pattern = 1) : d14 pattern ≤ (0 : Int) + d160 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c7467 (pattern : Twelve) (guard : d1867 pattern = 1) : d493 pattern ≤ (0 : Int) + d643 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d493, d643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3356 pattern childGuard
    simpa only [d1867, d493, d643, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d493, d643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7466 pattern childGuard
    simpa only [d1867, d493, d643, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7468 (pattern : Twelve) (guard : d1867 pattern = 1) : d494 pattern ≤ (0 : Int) + d13 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3358 pattern childGuard
    simpa only [d1867, d494, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7014 pattern childGuard
    simpa only [d1867, d494, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7469 (pattern : Twelve) (guard : d1867 pattern = 1) : d519 pattern ≤ (0 : Int) + d667 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d519, d667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7467 pattern childGuard
    simpa only [d519, d667, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d519, d667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7468 pattern childGuard
    simpa only [d519, d667, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7470 (pattern : Twelve) (guard : d1867 pattern = 1) : d520 pattern ≤ (0 : Int) + d668 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d520, d668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7415 pattern childGuard
    simpa only [d520, d668, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d520, d668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d520, d668, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7471 (pattern : Twelve) (guard : d1867 pattern = 1) : d548 pattern ≤ (0 : Int) + d696 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d548, d696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7469 pattern childGuard
    simpa only [d548, d696, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d548, d696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7470 pattern childGuard
    simpa only [d548, d696, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7472 (pattern : Twelve) (guard : d1867 pattern = 1) : d521 pattern ≤ (0 : Int) + d669 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d521, d669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7415 pattern childGuard
    simpa only [d521, d669, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d521, d669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7468 pattern childGuard
    simpa only [d521, d669, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7473 (pattern : Twelve) (guard : d1867 pattern = 1) : d549 pattern ≤ (0 : Int) + d697 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d549, d697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7472 pattern childGuard
    simpa only [d549, d697, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d549, d697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7470 pattern childGuard
    simpa only [d549, d697, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7474 (pattern : Twelve) (guard : d1867 pattern = 1) : d571 pattern ≤ (0 : Int) + d719 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d571, d719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7471 pattern childGuard
    simpa only [d571, d719, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d571, d719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7473 pattern childGuard
    simpa only [d571, d719, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7475 (pattern : Twelve) (guard : d1867 pattern = 1) : d495 pattern ≤ (0 : Int) + d644 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d495, d644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3372 pattern childGuard
    simpa only [d1867, d495, d644, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d495, d644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7458 pattern childGuard
    simpa only [d1867, d495, d644, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7476 (pattern : Twelve) (guard : d1867 pattern = 1) : d522 pattern ≤ (0 : Int) + d670 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d522, d670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7475 pattern childGuard
    simpa only [d522, d670, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d522, d670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d522, d670, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7477 (pattern : Twelve) (guard : d1867 pattern = 1) : d550 pattern ≤ (0 : Int) + d698 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d550, d698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7472 pattern childGuard
    simpa only [d550, d698, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d550, d698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7476 pattern childGuard
    simpa only [d550, d698, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7478 (pattern : Twelve) (guard : d1867 pattern = 1) : d572 pattern ≤ (0 : Int) + d720 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d572, d720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7473 pattern childGuard
    simpa only [d572, d720, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d572, d720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7477 pattern childGuard
    simpa only [d572, d720, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7479 (pattern : Twelve) (guard : d1867 pattern = 1) : d593 pattern ≤ (0 : Int) + d741 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d593, d741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7474 pattern childGuard
    simpa only [d593, d741, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d593, d741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7478 pattern childGuard
    simpa only [d593, d741, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7480 (pattern : Twelve) (guard : d1867 pattern = 1) : d608 pattern ≤ (0 : Int) + d756 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d608, d756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7465 pattern childGuard
    simpa only [d608, d756, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d608, d756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7479 pattern childGuard
    simpa only [d608, d756, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7481 (pattern : Twelve) (guard : d0 pattern = 1) : d14 pattern ≤ (0 : Int) + d158 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c7482 (pattern : Twelve) (guard : d1867 pattern = 1) : d496 pattern ≤ (0 : Int) + d645 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d496, d645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3381 pattern childGuard
    simpa only [d1867, d496, d645, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d496, d645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7481 pattern childGuard
    simpa only [d1867, d496, d645, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7483 (pattern : Twelve) (guard : d1867 pattern = 1) : d523 pattern ≤ (0 : Int) + d671 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d523, d671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7482 pattern childGuard
    simpa only [d523, d671, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d523, d671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7415 pattern childGuard
    simpa only [d523, d671, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7484 (pattern : Twelve) (guard : d1867 pattern = 1) : d551 pattern ≤ (0 : Int) + d699 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d551, d699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7483 pattern childGuard
    simpa only [d551, d699, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d551, d699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7443 pattern childGuard
    simpa only [d551, d699, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7485 (pattern : Twelve) (guard : d1867 pattern = 1) : d573 pattern ≤ (0 : Int) + d721 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d573, d721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7484 pattern childGuard
    simpa only [d573, d721, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d573, d721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7445 pattern childGuard
    simpa only [d573, d721, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7486 (pattern : Twelve) (guard : d1867 pattern = 1) : d594 pattern ≤ (0 : Int) + d742 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d594, d742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7485 pattern childGuard
    simpa only [d594, d742, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d594, d742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7447 pattern childGuard
    simpa only [d594, d742, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7487 (pattern : Twelve) (guard : d1867 pattern = 1) : d609 pattern ≤ (0 : Int) + d757 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d609, d757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7486 pattern childGuard
    simpa only [d609, d757, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d609, d757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d609, d757, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7488 (pattern : Twelve) (guard : d1867 pattern = 1) : d619 pattern ≤ (0 : Int) + d767 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d619, d767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7480 pattern childGuard
    simpa only [d619, d767, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d619, d767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7487 pattern childGuard
    simpa only [d619, d767, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7489 (pattern : Twelve) (guard : d1867 pattern = 1) : d624 pattern ≤ (0 : Int) + d772 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d624, d772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7450 pattern childGuard
    simpa only [d624, d772, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d624, d772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7488 pattern childGuard
    simpa only [d624, d772, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7490 (pattern : Twelve) (guard : d1867 pattern = 1) : d574 pattern ≤ (0 : Int) + d722 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d574, d722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7394 pattern childGuard
    simpa only [d574, d722, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d574, d722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7434 pattern childGuard
    simpa only [d574, d722, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7491 (pattern : Twelve) (guard : d1867 pattern = 1) : d524 pattern ≤ (0 : Int) + d672 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d524, d672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7394 pattern childGuard
    simpa only [d524, d672, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d524, d672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7398 pattern childGuard
    simpa only [d524, d672, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7492 (pattern : Twelve) (guard : d1867 pattern = 1) : d552 pattern ≤ (0 : Int) + d700 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d552, d700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7491 pattern childGuard
    simpa only [d552, d700, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d552, d700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7401 pattern childGuard
    simpa only [d552, d700, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7493 (pattern : Twelve) (guard : d1867 pattern = 1) : d575 pattern ≤ (0 : Int) + d723 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d575, d723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7394 pattern childGuard
    simpa only [d575, d723, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d575, d723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7492 pattern childGuard
    simpa only [d575, d723, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7494 (pattern : Twelve) (guard : d1867 pattern = 1) : d595 pattern ≤ (0 : Int) + d743 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d595, d743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7490 pattern childGuard
    simpa only [d595, d743, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d595, d743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7493 pattern childGuard
    simpa only [d595, d743, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7495 (pattern : Twelve) (guard : d1867 pattern = 1) : d525 pattern ≤ (0 : Int) + d673 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d525, d673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7394 pattern childGuard
    simpa only [d525, d673, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d525, d673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7412 pattern childGuard
    simpa only [d525, d673, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7496 (pattern : Twelve) (guard : d1867 pattern = 1) : d553 pattern ≤ (0 : Int) + d701 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d553, d701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7423 pattern childGuard
    simpa only [d553, d701, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d553, d701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7495 pattern childGuard
    simpa only [d553, d701, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7497 (pattern : Twelve) (guard : d1867 pattern = 1) : d554 pattern ≤ (0 : Int) + d702 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d554, d702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7423 pattern childGuard
    simpa only [d554, d702, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d554, d702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7418 pattern childGuard
    simpa only [d554, d702, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7498 (pattern : Twelve) (guard : d1867 pattern = 1) : d576 pattern ≤ (0 : Int) + d724 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d576, d724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7496 pattern childGuard
    simpa only [d576, d724, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d576, d724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7497 pattern childGuard
    simpa only [d576, d724, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7499 (pattern : Twelve) (guard : d1867 pattern = 1) : d555 pattern ≤ (0 : Int) + d703 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d555, d703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7423 pattern childGuard
    simpa only [d555, d703, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d555, d703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7421 pattern childGuard
    simpa only [d555, d703, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7500 (pattern : Twelve) (guard : d1867 pattern = 1) : d577 pattern ≤ (0 : Int) + d725 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d577, d725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7499 pattern childGuard
    simpa only [d577, d725, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d577, d725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7424 pattern childGuard
    simpa only [d577, d725, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7501 (pattern : Twelve) (guard : d1867 pattern = 1) : d596 pattern ≤ (0 : Int) + d744 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d596, d744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7498 pattern childGuard
    simpa only [d596, d744, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d596, d744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7500 pattern childGuard
    simpa only [d596, d744, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7502 (pattern : Twelve) (guard : d1867 pattern = 1) : d610 pattern ≤ (0 : Int) + d758 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d610, d758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7494 pattern childGuard
    simpa only [d610, d758, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d610, d758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7501 pattern childGuard
    simpa only [d610, d758, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7503 (pattern : Twelve) (guard : d1867 pattern = 1) : d578 pattern ≤ (0 : Int) + d726 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d578, d726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7394 pattern childGuard
    simpa only [d578, d726, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d578, d726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7424 pattern childGuard
    simpa only [d578, d726, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7504 (pattern : Twelve) (guard : d1867 pattern = 1) : d597 pattern ≤ (0 : Int) + d745 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d597, d745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7490 pattern childGuard
    simpa only [d597, d745, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d597, d745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7503 pattern childGuard
    simpa only [d597, d745, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7505 (pattern : Twelve) (guard : d1867 pattern = 1) : d598 pattern ≤ (0 : Int) + d746 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d598, d746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7445 pattern childGuard
    simpa only [d598, d746, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d598, d746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7447 pattern childGuard
    simpa only [d598, d746, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7506 (pattern : Twelve) (guard : d1867 pattern = 1) : d611 pattern ≤ (0 : Int) + d759 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d611, d759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7504 pattern childGuard
    simpa only [d611, d759, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d611, d759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7505 pattern childGuard
    simpa only [d611, d759, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7507 (pattern : Twelve) (guard : d1867 pattern = 1) : d620 pattern ≤ (0 : Int) + d768 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d620, d768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7502 pattern childGuard
    simpa only [d620, d768, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d620, d768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7506 pattern childGuard
    simpa only [d620, d768, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7508 (pattern : Twelve) (guard : d1867 pattern = 1) : d556 pattern ≤ (0 : Int) + d704 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d556, d704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7423 pattern childGuard
    simpa only [d556, d704, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d556, d704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7460 pattern childGuard
    simpa only [d556, d704, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7509 (pattern : Twelve) (guard : d1867 pattern = 1) : d579 pattern ≤ (0 : Int) + d727 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d579, d727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7423 pattern childGuard
    simpa only [d579, d727, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d579, d727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7508 pattern childGuard
    simpa only [d579, d727, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7510 (pattern : Twelve) (guard : d1867 pattern = 1) : d580 pattern ≤ (0 : Int) + d728 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d580, d728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7423 pattern childGuard
    simpa only [d580, d728, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d580, d728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7424 pattern childGuard
    simpa only [d580, d728, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7511 (pattern : Twelve) (guard : d1867 pattern = 1) : d599 pattern ≤ (0 : Int) + d747 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d599, d747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7509 pattern childGuard
    simpa only [d599, d747, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d599, d747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7510 pattern childGuard
    simpa only [d599, d747, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7512 (pattern : Twelve) (guard : d1867 pattern = 1) : d600 pattern ≤ (0 : Int) + d748 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d600, d748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7473 pattern childGuard
    simpa only [d600, d748, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d600, d748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7478 pattern childGuard
    simpa only [d600, d748, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7513 (pattern : Twelve) (guard : d1867 pattern = 1) : d612 pattern ≤ (0 : Int) + d760 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d612, d760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7511 pattern childGuard
    simpa only [d612, d760, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d612, d760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7512 pattern childGuard
    simpa only [d612, d760, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7514 (pattern : Twelve) (guard : d1867 pattern = 1) : d613 pattern ≤ (0 : Int) + d761 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d613, d761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7505 pattern childGuard
    simpa only [d613, d761, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d613, d761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d613, d761, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7515 (pattern : Twelve) (guard : d1867 pattern = 1) : d621 pattern ≤ (0 : Int) + d769 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d621, d769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7513 pattern childGuard
    simpa only [d621, d769, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d621, d769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7514 pattern childGuard
    simpa only [d621, d769, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7516 (pattern : Twelve) (guard : d1867 pattern = 1) : d625 pattern ≤ (0 : Int) + d773 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d625, d773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7507 pattern childGuard
    simpa only [d625, d773, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d625, d773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7515 pattern childGuard
    simpa only [d625, d773, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7517 (pattern : Twelve) (guard : d1867 pattern = 1) : d627 pattern ≤ (0 : Int) + d775 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d627, d775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7489 pattern childGuard
    simpa only [d627, d775, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d627, d775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7516 pattern childGuard
    simpa only [d627, d775, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7518 (pattern : Twelve) (guard : d1867 pattern = 1) : d628 pattern ≤ (0 : Int) + d776 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d628, d776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7517 pattern childGuard
    simpa only [d628, d776, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d628, d776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7516 pattern childGuard
    simpa only [d628, d776, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7519 (pattern : Twelve) (guard : d1867 pattern = 1) : d526 pattern ≤ (0 : Int) + d674 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d526, d674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7394 pattern childGuard
    simpa only [d526, d674, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d526, d674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7475 pattern childGuard
    simpa only [d526, d674, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7520 (pattern : Twelve) (guard : d1867 pattern = 1) : d557 pattern ≤ (0 : Int) + d705 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d557, d705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7519 pattern childGuard
    simpa only [d557, d705, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d557, d705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7401 pattern childGuard
    simpa only [d557, d705, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7521 (pattern : Twelve) (guard : d1867 pattern = 1) : d581 pattern ≤ (0 : Int) + d729 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d581, d729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7394 pattern childGuard
    simpa only [d581, d729, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d581, d729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7520 pattern childGuard
    simpa only [d581, d729, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7522 (pattern : Twelve) (guard : d1867 pattern = 1) : d601 pattern ≤ (0 : Int) + d749 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d601, d749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7490 pattern childGuard
    simpa only [d601, d749, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d601, d749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7521 pattern childGuard
    simpa only [d601, d749, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7523 (pattern : Twelve) (guard : d1867 pattern = 1) : d582 pattern ≤ (0 : Int) + d730 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d582, d730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7496 pattern childGuard
    simpa only [d582, d730, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d582, d730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7445 pattern childGuard
    simpa only [d582, d730, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7524 (pattern : Twelve) (guard : d1867 pattern = 1) : d583 pattern ≤ (0 : Int) + d731 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d583, d731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7445 pattern childGuard
    simpa only [d583, d731, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d583, d731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7520 pattern childGuard
    simpa only [d583, d731, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7525 (pattern : Twelve) (guard : d1867 pattern = 1) : d602 pattern ≤ (0 : Int) + d750 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d602, d750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7523 pattern childGuard
    simpa only [d602, d750, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d602, d750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7524 pattern childGuard
    simpa only [d602, d750, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7526 (pattern : Twelve) (guard : d1867 pattern = 1) : d614 pattern ≤ (0 : Int) + d762 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d614, d762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7522 pattern childGuard
    simpa only [d614, d762, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d614, d762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7525 pattern childGuard
    simpa only [d614, d762, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7527 (pattern : Twelve) (guard : d1867 pattern = 1) : d603 pattern ≤ (0 : Int) + d751 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d603, d751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7445 pattern childGuard
    simpa only [d603, d751, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d603, d751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7524 pattern childGuard
    simpa only [d603, d751, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7528 (pattern : Twelve) (guard : d1867 pattern = 1) : d615 pattern ≤ (0 : Int) + d763 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d615, d763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7522 pattern childGuard
    simpa only [d615, d763, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d615, d763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7527 pattern childGuard
    simpa only [d615, d763, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7529 (pattern : Twelve) (guard : d1867 pattern = 1) : d622 pattern ≤ (0 : Int) + d770 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d622, d770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7526 pattern childGuard
    simpa only [d622, d770, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d622, d770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7528 pattern childGuard
    simpa only [d622, d770, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7530 (pattern : Twelve) (guard : d1867 pattern = 1) : d527 pattern ≤ (0 : Int) + d675 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d527, d675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7394 pattern childGuard
    simpa only [d527, d675, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d527, d675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7468 pattern childGuard
    simpa only [d527, d675, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7531 (pattern : Twelve) (guard : d1867 pattern = 1) : d558 pattern ≤ (0 : Int) + d706 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d558, d706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7423 pattern childGuard
    simpa only [d558, d706, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d558, d706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7530 pattern childGuard
    simpa only [d558, d706, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7532 (pattern : Twelve) (guard : d1867 pattern = 1) : d584 pattern ≤ (0 : Int) + d732 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d584, d732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7423 pattern childGuard
    simpa only [d584, d732, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d584, d732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7531 pattern childGuard
    simpa only [d584, d732, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7533 (pattern : Twelve) (guard : d1867 pattern = 1) : d585 pattern ≤ (0 : Int) + d733 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d585, d733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7508 pattern childGuard
    simpa only [d585, d733, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d585, d733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7520 pattern childGuard
    simpa only [d585, d733, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7534 (pattern : Twelve) (guard : d1867 pattern = 1) : d604 pattern ≤ (0 : Int) + d752 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d604, d752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7532 pattern childGuard
    simpa only [d604, d752, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d604, d752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7533 pattern childGuard
    simpa only [d604, d752, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7535 (pattern : Twelve) (guard : d1867 pattern = 1) : d497 pattern ≤ (0 : Int) + d14 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3444 pattern childGuard
    simpa only [d1867, d497, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7022 pattern childGuard
    simpa only [d1867, d497, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7536 (pattern : Twelve) (guard : d1867 pattern = 1) : d528 pattern ≤ (0 : Int) + d676 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d528, d676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7415 pattern childGuard
    simpa only [d528, d676, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d528, d676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7535 pattern childGuard
    simpa only [d528, d676, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7537 (pattern : Twelve) (guard : d1867 pattern = 1) : d529 pattern ≤ (0 : Int) + d677 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d529, d677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7459 pattern childGuard
    simpa only [d529, d677, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d529, d677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d529, d677, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7538 (pattern : Twelve) (guard : d1867 pattern = 1) : d559 pattern ≤ (0 : Int) + d707 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d559, d707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7536 pattern childGuard
    simpa only [d559, d707, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d559, d707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7537 pattern childGuard
    simpa only [d559, d707, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7539 (pattern : Twelve) (guard : d1867 pattern = 1) : d586 pattern ≤ (0 : Int) + d734 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d586, d734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7473 pattern childGuard
    simpa only [d586, d734, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d586, d734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7538 pattern childGuard
    simpa only [d586, d734, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7540 (pattern : Twelve) (guard : d1867 pattern = 1) : d530 pattern ≤ (0 : Int) + d678 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d530, d678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7415 pattern childGuard
    simpa only [d530, d678, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d530, d678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3302 pattern childGuard
    simpa only [d530, d678, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7541 (pattern : Twelve) (guard : d1867 pattern = 1) : d531 pattern ≤ (0 : Int) + d679 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d531, d679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7412 pattern childGuard
    simpa only [d531, d679, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d531, d679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d531, d679, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7542 (pattern : Twelve) (guard : d1867 pattern = 1) : d560 pattern ≤ (0 : Int) + d708 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d560, d708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7540 pattern childGuard
    simpa only [d560, d708, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d560, d708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7541 pattern childGuard
    simpa only [d560, d708, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7543 (pattern : Twelve) (guard : d1867 pattern = 1) : d587 pattern ≤ (0 : Int) + d735 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d587, d735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7538 pattern childGuard
    simpa only [d587, d735, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d587, d735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7542 pattern childGuard
    simpa only [d587, d735, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7544 (pattern : Twelve) (guard : d1867 pattern = 1) : d605 pattern ≤ (0 : Int) + d753 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d605, d753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7539 pattern childGuard
    simpa only [d605, d753, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d605, d753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7543 pattern childGuard
    simpa only [d605, d753, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7545 (pattern : Twelve) (guard : d1867 pattern = 1) : d616 pattern ≤ (0 : Int) + d764 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d616, d764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7534 pattern childGuard
    simpa only [d616, d764, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d616, d764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7544 pattern childGuard
    simpa only [d616, d764, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7546 (pattern : Twelve) (guard : d1867 pattern = 1) : d617 pattern ≤ (0 : Int) + d765 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d617, d765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7527 pattern childGuard
    simpa only [d617, d765, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d617, d765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d617, d765, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7547 (pattern : Twelve) (guard : d1867 pattern = 1) : d623 pattern ≤ (0 : Int) + d771 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d623, d771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7545 pattern childGuard
    simpa only [d623, d771, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d623, d771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7546 pattern childGuard
    simpa only [d623, d771, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7548 (pattern : Twelve) (guard : d1867 pattern = 1) : d626 pattern ≤ (0 : Int) + d774 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d626, d774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7529 pattern childGuard
    simpa only [d626, d774, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d626, d774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7547 pattern childGuard
    simpa only [d626, d774, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7549 (pattern : Twelve) (guard : d1867 pattern = 1) : d629 pattern ≤ (0 : Int) + d777 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d629, d777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7518 pattern childGuard
    simpa only [d629, d777, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d629, d777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7548 pattern childGuard
    simpa only [d629, d777, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7550 (pattern : Twelve) (guard : d1867 pattern = 1) : d1105 pattern ≤ (0 : Int) + d636 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d1105, d636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3468 pattern childGuard
    simpa only [d1867, d1105, d636, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d1105, d636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7388 pattern childGuard
    simpa only [d1867, d1105, d636, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7551 (pattern : Twelve) (guard : d1867 pattern = 1) : d1108 pattern ≤ (0 : Int) + d1183 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1108, d1183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7550 pattern childGuard
    simpa only [d1108, d1183, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1108, d1183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7389 pattern childGuard
    simpa only [d1108, d1183, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7552 (pattern : Twelve) (guard : d1867 pattern = 1) : d1118 pattern ≤ (0 : Int) + d1189 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1118, d1189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7390 pattern childGuard
    simpa only [d1118, d1189, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1118, d1189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7551 pattern childGuard
    simpa only [d1118, d1189, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7553 (pattern : Twelve) (guard : d1867 pattern = 1) : d1132 pattern ≤ (0 : Int) + d1199 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1132, d1199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7396 pattern childGuard
    simpa only [d1132, d1199, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1132, d1199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7552 pattern childGuard
    simpa only [d1132, d1199, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7554 (pattern : Twelve) (guard : d1867 pattern = 1) : d1119 pattern ≤ (0 : Int) + d1190 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1119, d1190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7395 pattern childGuard
    simpa only [d1119, d1190, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1119, d1190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7394 pattern childGuard
    simpa only [d1119, d1190, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7555 (pattern : Twelve) (guard : d1867 pattern = 1) : d1109 pattern ≤ (0 : Int) + d1184 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1109, d1184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7400 pattern childGuard
    simpa only [d1109, d1184, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1109, d1184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7475 pattern childGuard
    simpa only [d1109, d1184, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7556 (pattern : Twelve) (guard : d1867 pattern = 1) : d1120 pattern ≤ (0 : Int) + d1191 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1120, d1191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7555 pattern childGuard
    simpa only [d1120, d1191, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1120, d1191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7476 pattern childGuard
    simpa only [d1120, d1191, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7557 (pattern : Twelve) (guard : d1867 pattern = 1) : d1133 pattern ≤ (0 : Int) + d1200 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1133, d1200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7554 pattern childGuard
    simpa only [d1133, d1200, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1133, d1200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7556 pattern childGuard
    simpa only [d1133, d1200, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7558 (pattern : Twelve) (guard : d1867 pattern = 1) : d1152 pattern ≤ (0 : Int) + d1216 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1152, d1216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7553 pattern childGuard
    simpa only [d1152, d1216, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1152, d1216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7557 pattern childGuard
    simpa only [d1152, d1216, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7559 (pattern : Twelve) (guard : d1867 pattern = 1) : d1121 pattern ≤ (0 : Int) + d1192 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1121, d1192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7416 pattern childGuard
    simpa only [d1121, d1192, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1121, d1192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7443 pattern childGuard
    simpa only [d1121, d1192, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
