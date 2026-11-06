/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons195
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare27440 (p : Pattern) (guard : d5847 p = 1) : d3250 p ≤ (0 : Int) + d3643 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27371 p hg
    simpa only [d3643, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27377 p hg
    simpa only [d3643, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27441 (p : Pattern) (guard : d5847 p = 1) : d3287 p ≤ (0 : Int) + d3644 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3287, d3644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27440 p hg
    simpa only [d3287, d3644, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3287, d3644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3287, d3644, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27442 (p : Pattern) (guard : d5847 p = 1) : d3288 p ≤ (0 : Int) + d3645 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3288, d3645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27387 p hg
    simpa only [d3288, d3645, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3288, d3645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27441 p hg
    simpa only [d3288, d3645, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27443 (p : Pattern) (guard : d5847 p = 1) : d3289 p ≤ (0 : Int) + d3646 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3289, d3646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27401 p hg
    simpa only [d3289, d3646, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3289, d3646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27406 p hg
    simpa only [d3289, d3646, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27444 (p : Pattern) (guard : d5847 p = 1) : d3290 p ≤ (0 : Int) + d3647 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3290, d3647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27442 p hg
    simpa only [d3290, d3647, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3290, d3647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d3290, d3647, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27445 (p : Pattern) (guard : d5847 p = 1) : d3291 p ≤ (0 : Int) + d3648 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3291, d3648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27431 p hg
    simpa only [d3291, d3648, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3291, d3648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3291, d3648, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27446 (p : Pattern) (guard : d5847 p = 1) : d3292 p ≤ (0 : Int) + d3649 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3292, d3649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27401 p hg
    simpa only [d3292, d3649, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3292, d3649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27445 p hg
    simpa only [d3292, d3649, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27447 (p : Pattern) (guard : d5847 p = 1) : d3293 p ≤ (0 : Int) + d3650 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3293, d3650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27435 p hg
    simpa only [d3293, d3650, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3293, d3650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3293, d3650, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27448 (p : Pattern) (guard : d5847 p = 1) : d3294 p ≤ (0 : Int) + d3651 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3294, d3651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27447 p hg
    simpa only [d3294, d3651, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3294, d3651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3294, d3651, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27449 (p : Pattern) (guard : d5847 p = 1) : d3295 p ≤ (0 : Int) + d3652 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3295, d3652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27446 p hg
    simpa only [d3295, d3652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3295, d3652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27448 p hg
    simpa only [d3295, d3652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27450 (p : Pattern) (guard : d5847 p = 1) : d3296 p ≤ (0 : Int) + d3653 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3296, d3653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27444 p hg
    simpa only [d3296, d3653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3296, d3653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27449 p hg
    simpa only [d3296, d3653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27451 (p : Pattern) (guard : d5847 p = 1) : d3297 p ≤ (0 : Int) + d3654 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3297, d3654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27439 p hg
    simpa only [d3297, d3654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3297, d3654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27450 p hg
    simpa only [d3297, d3654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27452 (p : Pattern) (guard : d5847 p = 1) : d3298 p ≤ (0 : Int) + d3655 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3298, d3655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27410 p hg
    simpa only [d3298, d3655, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3298, d3655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27451 p hg
    simpa only [d3298, d3655, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27453 (p : Pattern) (guard : d5847 p = 1) : d3226 p ≤ (0 : Int) + d3656 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27322 p hg
    simpa only [d3656, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27365 p hg
    simpa only [d3656, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27454 (p : Pattern) (guard : d5847 p = 1) : d3226 p ≤ (0 : Int) + d3657 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27366 p hg
    simpa only [d3657, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27453 p hg
    simpa only [d3657, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27455 (p : Pattern) (guard : d5847 p = 1) : d3226 p ≤ (0 : Int) + d3658 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27319 p hg
    simpa only [d3658, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27454 p hg
    simpa only [d3658, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27456 (p : Pattern) (guard : d5847 p = 1) : d3230 p ≤ (0 : Int) + d3659 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3230, d3659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27324 p hg
    simpa only [d3230, d3659, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3230, d3659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3230, d3659, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27457 (p : Pattern) (guard : d5847 p = 1) : d3238 p ≤ (0 : Int) + d3660 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3238, d3660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27455 p hg
    simpa only [d3238, d3660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3238, d3660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27456 p hg
    simpa only [d3238, d3660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27458 (p : Pattern) (guard : d5847 p = 1) : d3226 p ≤ (0 : Int) + d3661 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3226, d3661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19829 p hg
    simpa only [d5847, d3226, d3661, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3226, d3661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20382 p hg
    simpa only [d5847, d3226, d3661, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27459 (p : Pattern) (guard : d5847 p = 1) : d3226 p ≤ (0 : Int) + d3662 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27322 p hg
    simpa only [d3662, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27458 p hg
    simpa only [d3662, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27460 (p : Pattern) (guard : d5847 p = 1) : d3226 p ≤ (0 : Int) + d3663 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27366 p hg
    simpa only [d3663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27459 p hg
    simpa only [d3663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27461 (p : Pattern) (guard : d5847 p = 1) : d3230 p ≤ (0 : Int) + d3664 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3230, d3664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27460 p hg
    simpa only [d3230, d3664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3230, d3664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3230, d3664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27462 (p : Pattern) (guard : d5847 p = 1) : d3238 p ≤ (0 : Int) + d3665 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3238, d3665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27370 p hg
    simpa only [d3238, d3665, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3238, d3665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27461 p hg
    simpa only [d3238, d3665, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27463 (p : Pattern) (guard : d5847 p = 1) : d3238 p ≤ (0 : Int) + d3666 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27457 p hg
    simpa only [d3666, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27462 p hg
    simpa only [d3666, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27464 (p : Pattern) (guard : d5847 p = 1) : d3230 p ≤ (0 : Int) + d3667 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3230, d3667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27369 p hg
    simpa only [d3230, d3667, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3230, d3667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3230, d3667, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27465 (p : Pattern) (guard : d5847 p = 1) : d3238 p ≤ (0 : Int) + d3668 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3238, d3668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27370 p hg
    simpa only [d3238, d3668, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3238, d3668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27464 p hg
    simpa only [d3238, d3668, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27466 (p : Pattern) (guard : d5847 p = 1) : d3240 p ≤ (0 : Int) + d3669 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3240, d3669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27399 p hg
    simpa only [d3240, d3669, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3240, d3669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3240, d3669, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27467 (p : Pattern) (guard : d5847 p = 1) : d3241 p ≤ (0 : Int) + d3670 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3241, d3670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27400 p hg
    simpa only [d3241, d3670, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3241, d3670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27466 p hg
    simpa only [d3241, d3670, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27468 (p : Pattern) (guard : d5847 p = 1) : d3242 p ≤ (0 : Int) + d3671 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3242, d3671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27465 p hg
    simpa only [d3242, d3671, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3242, d3671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27467 p hg
    simpa only [d3242, d3671, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27469 (p : Pattern) (guard : d5847 p = 1) : d3299 p ≤ (0 : Int) + d3672 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3299, d3672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27463 p hg
    simpa only [d3299, d3672, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3299, d3672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27468 p hg
    simpa only [d3299, d3672, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27470 (p : Pattern) (guard : d5847 p = 1) : d3245 p ≤ (0 : Int) + d3673 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3245, d3673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27355 p hg
    simpa only [d3245, d3673, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3245, d3673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3245, d3673, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27471 (p : Pattern) (guard : d5847 p = 1) : d3246 p ≤ (0 : Int) + d3674 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3246, d3674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27356 p hg
    simpa only [d3246, d3674, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3246, d3674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27470 p hg
    simpa only [d3246, d3674, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27472 (p : Pattern) (guard : d5847 p = 1) : d3247 p ≤ (0 : Int) + d3675 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3247, d3675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27471 p hg
    simpa only [d3247, d3675, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3247, d3675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3247, d3675, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27473 (p : Pattern) (guard : d5847 p = 1) : d3248 p ≤ (0 : Int) + d3676 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3248, d3676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27468 p hg
    simpa only [d3248, d3676, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3248, d3676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27472 p hg
    simpa only [d3248, d3676, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27474 (p : Pattern) (guard : d5847 p = 1) : d3300 p ≤ (0 : Int) + d3677 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3300, d3677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27469 p hg
    simpa only [d3300, d3677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3300, d3677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27473 p hg
    simpa only [d3300, d3677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27475 (p : Pattern) (guard : d5847 p = 1) : d3275 p ≤ (0 : Int) + d3678 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3275, d3678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27440 p hg
    simpa only [d3275, d3678, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3275, d3678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27378 p hg
    simpa only [d3275, d3678, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27476 (p : Pattern) (guard : d5847 p = 1) : d3253 p ≤ (0 : Int) + d3679 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27380 p hg
    simpa only [d3679, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27385 p hg
    simpa only [d3679, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27477 (p : Pattern) (guard : d5847 p = 1) : d3301 p ≤ (0 : Int) + d3680 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3301, d3680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27476 p hg
    simpa only [d3301, d3680, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3301, d3680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27386 p hg
    simpa only [d3301, d3680, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27478 (p : Pattern) (guard : d5847 p = 1) : d3302 p ≤ (0 : Int) + d3681 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3302, d3681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27475 p hg
    simpa only [d3302, d3681, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3302, d3681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27477 p hg
    simpa only [d3302, d3681, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27479 (p : Pattern) (guard : d5847 p = 1) : d3303 p ≤ (0 : Int) + d3682 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3303, d3682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27478 p hg
    simpa only [d3303, d3682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3303, d3682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27437 p hg
    simpa only [d3303, d3682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27480 (p : Pattern) (guard : d5847 p = 1) : d3304 p ≤ (0 : Int) + d3683 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3304, d3683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27479 p hg
    simpa only [d3304, d3683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3304, d3683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3304, d3683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27481 (p : Pattern) (guard : d5847 p = 1) : d3305 p ≤ (0 : Int) + d3684 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3305, d3684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27474 p hg
    simpa only [d3305, d3684, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3305, d3684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27480 p hg
    simpa only [d3305, d3684, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27482 (p : Pattern) (guard : d5847 p = 1) : d3306 p ≤ (0 : Int) + d3685 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3306, d3685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27462 p hg
    simpa only [d3306, d3685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3306, d3685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27475 p hg
    simpa only [d3306, d3685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27483 (p : Pattern) (guard : d5847 p = 1) : d3277 p ≤ (0 : Int) + d3686 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3277, d3686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27467 p hg
    simpa only [d3277, d3686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3277, d3686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27471 p hg
    simpa only [d3277, d3686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27484 (p : Pattern) (guard : d5847 p = 1) : d3307 p ≤ (0 : Int) + d3687 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3307, d3687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27482 p hg
    simpa only [d3307, d3687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3307, d3687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27483 p hg
    simpa only [d3307, d3687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27485 (p : Pattern) (guard : d5847 p = 1) : d3282 p ≤ (0 : Int) + d3688 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3282, d3688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27467 p hg
    simpa only [d3282, d3688, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3282, d3688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27433 p hg
    simpa only [d3282, d3688, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27486 (p : Pattern) (guard : d5847 p = 1) : d3285 p ≤ (0 : Int) + d3689 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3285, d3689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27485 p hg
    simpa only [d3285, d3689, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3285, d3689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27437 p hg
    simpa only [d3285, d3689, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27487 (p : Pattern) (guard : d5847 p = 1) : d3308 p ≤ (0 : Int) + d3690 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3308, d3690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27484 p hg
    simpa only [d3308, d3690, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3308, d3690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27486 p hg
    simpa only [d3308, d3690, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27488 (p : Pattern) (guard : d5847 p = 1) : d3309 p ≤ (0 : Int) + d3691 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3309, d3691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27477 p hg
    simpa only [d3309, d3691, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3309, d3691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3309, d3691, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27489 (p : Pattern) (guard : d5847 p = 1) : d3310 p ≤ (0 : Int) + d3692 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3310, d3692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27488 p hg
    simpa only [d3310, d3692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3310, d3692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3310, d3692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27490 (p : Pattern) (guard : d5847 p = 1) : d3311 p ≤ (0 : Int) + d3693 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3311, d3693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27489 p hg
    simpa only [d3311, d3693, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3311, d3693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3311, d3693, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27491 (p : Pattern) (guard : d5847 p = 1) : d3312 p ≤ (0 : Int) + d3694 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3312, d3694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27487 p hg
    simpa only [d3312, d3694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3312, d3694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27490 p hg
    simpa only [d3312, d3694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27492 (p : Pattern) (guard : d5847 p = 1) : d3313 p ≤ (0 : Int) + d3695 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3313, d3695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27481 p hg
    simpa only [d3313, d3695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3313, d3695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27491 p hg
    simpa only [d3313, d3695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27493 (p : Pattern) (guard : d5847 p = 1) : d3314 p ≤ (0 : Int) + d3696 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3314, d3696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27452 p hg
    simpa only [d3314, d3696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3314, d3696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27492 p hg
    simpa only [d3314, d3696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27494 (p : Pattern) (guard : d5847 p = 1) : d3315 p ≤ (0 : Int) + d3697 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3315, d3697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27471 p hg
    simpa only [d3315, d3697, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3315, d3697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27436 p hg
    simpa only [d3315, d3697, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27495 (p : Pattern) (guard : d5847 p = 1) : d3316 p ≤ (0 : Int) + d3698 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3316, d3698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27494 p hg
    simpa only [d3316, d3698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3316, d3698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27437 p hg
    simpa only [d3316, d3698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27496 (p : Pattern) (guard : d5847 p = 1) : d3317 p ≤ (0 : Int) + d3699 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3317, d3699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27437 p hg
    simpa only [d3317, d3699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3317, d3699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3317, d3699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27497 (p : Pattern) (guard : d5847 p = 1) : d3318 p ≤ (0 : Int) + d3700 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3318, d3700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27495 p hg
    simpa only [d3318, d3700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3318, d3700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27496 p hg
    simpa only [d3318, d3700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27498 (p : Pattern) (guard : d5847 p = 1) : d3319 p ≤ (0 : Int) + d3701 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3319, d3701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27496 p hg
    simpa only [d3319, d3701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3319, d3701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3319, d3701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27499 (p : Pattern) (guard : d5847 p = 1) : d3320 p ≤ (0 : Int) + d3702 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3320, d3702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27497 p hg
    simpa only [d3320, d3702, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3320, d3702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27498 p hg
    simpa only [d3320, d3702, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27500 (p : Pattern) (guard : d5847 p = 1) : d3321 p ≤ (0 : Int) + d3703 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3321, d3703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27498 p hg
    simpa only [d3321, d3703, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3321, d3703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3321, d3703, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27501 (p : Pattern) (guard : d5847 p = 1) : d3322 p ≤ (0 : Int) + d3704 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3322, d3704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27499 p hg
    simpa only [d3322, d3704, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3322, d3704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27500 p hg
    simpa only [d3322, d3704, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27502 (p : Pattern) (guard : d5847 p = 1) : d3323 p ≤ (0 : Int) + d3705 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3323, d3705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27492 p hg
    simpa only [d3323, d3705, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3323, d3705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27501 p hg
    simpa only [d3323, d3705, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27503 (p : Pattern) (guard : d5847 p = 1) : d3324 p ≤ (0 : Int) + d3706 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3324, d3706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27493 p hg
    simpa only [d3324, d3706, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3324, d3706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27502 p hg
    simpa only [d3324, d3706, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27504 (p : Pattern) (guard : d5847 p = 1) : d3325 p ≤ (0 : Int) + d3553 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27336 p hg
    simpa only [d3325, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27339 p hg
    simpa only [d3325, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27505 (p : Pattern) (guard : d5847 p = 1) : d3326 p ≤ (0 : Int) + d3707 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3326, d3707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27504 p hg
    simpa only [d3326, d3707, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3326, d3707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27350 p hg
    simpa only [d3326, d3707, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27506 (p : Pattern) (guard : d5847 p = 1) : d3327 p ≤ (0 : Int) + d3708 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3327, d3708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27505 p hg
    simpa only [d3327, d3708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3327, d3708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27363 p hg
    simpa only [d3327, d3708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27507 (p : Pattern) (guard : d5847 p = 1) : d3328 p ≤ (0 : Int) + d3709 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3328, d3709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27506 p hg
    simpa only [d3328, d3709, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3328, d3709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27409 p hg
    simpa only [d3328, d3709, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27508 (p : Pattern) (guard : d5847 p = 1) : d3306 p ≤ (0 : Int) + d3710 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3306, d3710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27339 p hg
    simpa only [d3306, d3710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3306, d3710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27423 p hg
    simpa only [d3306, d3710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27509 (p : Pattern) (guard : d5847 p = 1) : d3307 p ≤ (0 : Int) + d3711 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3307, d3711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27508 p hg
    simpa only [d3307, d3711, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3307, d3711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27425 p hg
    simpa only [d3307, d3711, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27510 (p : Pattern) (guard : d5847 p = 1) : d3308 p ≤ (0 : Int) + d3712 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3308, d3712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27509 p hg
    simpa only [d3308, d3712, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3308, d3712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27438 p hg
    simpa only [d3308, d3712, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27511 (p : Pattern) (guard : d5847 p = 1) : d3329 p ≤ (0 : Int) + d3713 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3329, d3713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27510 p hg
    simpa only [d3329, d3713, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3329, d3713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27450 p hg
    simpa only [d3329, d3713, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27512 (p : Pattern) (guard : d5847 p = 1) : d3330 p ≤ (0 : Int) + d3714 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3330, d3714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27507 p hg
    simpa only [d3330, d3714, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3330, d3714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27511 p hg
    simpa only [d3330, d3714, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27513 (p : Pattern) (guard : d5847 p = 1) : d3331 p ≤ (0 : Int) + d3715 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3331, d3715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27512 p hg
    simpa only [d3331, d3715, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3331, d3715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27492 p hg
    simpa only [d3331, d3715, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27514 (p : Pattern) (guard : d5847 p = 1) : d3332 p ≤ (0 : Int) + d3716 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3332, d3716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27492 p hg
    simpa only [d3332, d3716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3332, d3716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3332, d3716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27515 (p : Pattern) (guard : d5847 p = 1) : d3333 p ≤ (0 : Int) + d3717 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3333, d3717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27513 p hg
    simpa only [d3333, d3717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3333, d3717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27514 p hg
    simpa only [d3333, d3717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27516 (p : Pattern) (guard : d5847 p = 1) : d3334 p ≤ (0 : Int) + d3718 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3334, d3718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27503 p hg
    simpa only [d3334, d3718, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3334, d3718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27515 p hg
    simpa only [d3334, d3718, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27517 (p : Pattern) (guard : d5847 p = 1) : d3335 p ≤ (0 : Int) + d3719 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3335, d3719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20102 p hg
    simpa only [d5847, d3335, d3719, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3335, d3719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26743 p hg
    simpa only [d5847, d3335, d3719, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27518 (p : Pattern) (guard : d5847 p = 1) : d3336 p ≤ (0 : Int) + d3720 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3336, d3720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27517 p hg
    simpa only [d3336, d3720, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3336, d3720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27319 p hg
    simpa only [d3336, d3720, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27519 (p : Pattern) (guard : d5847 p = 1) : d3337 p ≤ (0 : Int) + d3721 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3337, d3721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27518 p hg
    simpa only [d3337, d3721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3337, d3721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27319 p hg
    simpa only [d3337, d3721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27520 (p : Pattern) (guard : d5847 p = 1) : d3338 p ≤ (0 : Int) + d3722 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3338, d3722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27519 p hg
    simpa only [d3338, d3722, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3338, d3722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27324 p hg
    simpa only [d3338, d3722, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27521 (p : Pattern) (guard : d5847 p = 1) : d3339 p ≤ (0 : Int) + d3723 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3339, d3723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27520 p hg
    simpa only [d3339, d3723, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3339, d3723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27330 p hg
    simpa only [d3339, d3723, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27522 (p : Pattern) (guard : d5847 p = 1) : d3340 p ≤ (0 : Int) + d3724 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3340, d3724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27521 p hg
    simpa only [d3340, d3724, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3340, d3724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27339 p hg
    simpa only [d3340, d3724, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27523 (p : Pattern) (guard : d5847 p = 1) : d3341 p ≤ (0 : Int) + d3725 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3341, d3725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27522 p hg
    simpa only [d3341, d3725, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3341, d3725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27350 p hg
    simpa only [d3341, d3725, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27524 (p : Pattern) (guard : d5847 p = 1) : d3342 p ≤ (0 : Int) + d3726 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3342, d3726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27523 p hg
    simpa only [d3342, d3726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3342, d3726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27363 p hg
    simpa only [d3342, d3726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27525 (p : Pattern) (guard : d5847 p = 1) : d3343 p ≤ (0 : Int) + d3727 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3343, d3727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27524 p hg
    simpa only [d3343, d3727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3343, d3727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27409 p hg
    simpa only [d3343, d3727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27526 (p : Pattern) (guard : d5847 p = 1) : d3344 p ≤ (0 : Int) + d3710 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3344, d3710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27336 p hg
    simpa only [d3344, d3710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3344, d3710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27423 p hg
    simpa only [d3344, d3710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27527 (p : Pattern) (guard : d5847 p = 1) : d3345 p ≤ (0 : Int) + d3711 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3345, d3711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27526 p hg
    simpa only [d3345, d3711, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3345, d3711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27425 p hg
    simpa only [d3345, d3711, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27528 (p : Pattern) (guard : d5847 p = 1) : d3346 p ≤ (0 : Int) + d3712 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3346, d3712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27527 p hg
    simpa only [d3346, d3712, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3346, d3712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27438 p hg
    simpa only [d3346, d3712, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27529 (p : Pattern) (guard : d5847 p = 1) : d3347 p ≤ (0 : Int) + d3713 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3347, d3713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27528 p hg
    simpa only [d3347, d3713, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3347, d3713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27450 p hg
    simpa only [d3347, d3713, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27530 (p : Pattern) (guard : d5847 p = 1) : d3348 p ≤ (0 : Int) + d3728 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3348, d3728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27525 p hg
    simpa only [d3348, d3728, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3348, d3728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27529 p hg
    simpa only [d3348, d3728, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27531 (p : Pattern) (guard : d5847 p = 1) : d3349 p ≤ (0 : Int) + d3729 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3349, d3729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27530 p hg
    simpa only [d3349, d3729, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3349, d3729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27492 p hg
    simpa only [d3349, d3729, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27532 (p : Pattern) (guard : d5847 p = 1) : d3350 p ≤ (0 : Int) + d3730 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3350, d3730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27531 p hg
    simpa only [d3350, d3730, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3350, d3730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27502 p hg
    simpa only [d3350, d3730, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27533 (p : Pattern) (guard : d5847 p = 1) : d3299 p ≤ (0 : Int) + d3707 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3299, d3707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27339 p hg
    simpa only [d3299, d3707, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3299, d3707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27350 p hg
    simpa only [d3299, d3707, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27534 (p : Pattern) (guard : d5847 p = 1) : d3300 p ≤ (0 : Int) + d3708 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3300, d3708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27533 p hg
    simpa only [d3300, d3708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3300, d3708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27363 p hg
    simpa only [d3300, d3708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27535 (p : Pattern) (guard : d5847 p = 1) : d3351 p ≤ (0 : Int) + d3709 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3351, d3709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27534 p hg
    simpa only [d3351, d3709, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3351, d3709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27409 p hg
    simpa only [d3351, d3709, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27536 (p : Pattern) (guard : d5847 p = 1) : d3352 p ≤ (0 : Int) + d3714 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3352, d3714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27535 p hg
    simpa only [d3352, d3714, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3352, d3714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27511 p hg
    simpa only [d3352, d3714, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27537 (p : Pattern) (guard : d5847 p = 1) : d3353 p ≤ (0 : Int) + d3715 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3353, d3715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27536 p hg
    simpa only [d3353, d3715, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3353, d3715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27492 p hg
    simpa only [d3353, d3715, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27538 (p : Pattern) (guard : d5847 p = 1) : d3354 p ≤ (0 : Int) + d3717 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3354, d3717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27537 p hg
    simpa only [d3354, d3717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3354, d3717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27514 p hg
    simpa only [d3354, d3717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27539 (p : Pattern) (guard : d5847 p = 1) : d3355 p ≤ (0 : Int) + d3731 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3355, d3731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27532 p hg
    simpa only [d3355, d3731, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3355, d3731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27538 p hg
    simpa only [d3355, d3731, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27540 (p : Pattern) (guard : d5847 p = 1) : d3356 p ≤ (0 : Int) + d3732 p := by
  cases selected : p 71 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3356, d3732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27516 p hg
    simpa only [d3356, d3732, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3356, d3732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27539 p hg
    simpa only [d3356, d3732, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27541 (p : Pattern) (guard : d5847 p = 1) : d3357 p ≤ (0 : Int) + d3733 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3357, d3733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20131 p hg
    simpa only [d5847, d3357, d3733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3357, d3733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26768 p hg
    simpa only [d5847, d3357, d3733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27542 (p : Pattern) (guard : d5847 p = 1) : d3358 p ≤ (0 : Int) + d102 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20135 p hg
    simpa only [d5847, d3358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20160 p hg
    simpa only [d5847, d3358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27543 (p : Pattern) (guard : d5847 p = 1) : d3359 p ≤ (0 : Int) + d3734 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3359, d3734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27541 p hg
    simpa only [d3359, d3734, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3359, d3734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27542 p hg
    simpa only [d3359, d3734, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27544 (p : Pattern) (guard : d5847 p = 1) : d3360 p ≤ (0 : Int) + d3735 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3360, d3735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27543 p hg
    simpa only [d3360, d3735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3360, d3735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27542 p hg
    simpa only [d3360, d3735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27545 (p : Pattern) (guard : d5847 p = 1) : d3358 p ≤ (0 : Int) + d3736 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3358, d3736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20135 p hg
    simpa only [d5847, d3358, d3736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3358, d3736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20170 p hg
    simpa only [d5847, d3358, d3736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27546 (p : Pattern) (guard : d5847 p = 1) : d3358 p ≤ (0 : Int) + d3737 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27542 p hg
    simpa only [d3737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27545 p hg
    simpa only [d3737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27547 (p : Pattern) (guard : d5847 p = 1) : d3358 p ≤ (0 : Int) + d3738 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27546 p hg
    simpa only [d3738, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27545 p hg
    simpa only [d3738, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27548 (p : Pattern) (guard : d5847 p = 1) : d3361 p ≤ (0 : Int) + d3739 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3361, d3739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27544 p hg
    simpa only [d3361, d3739, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3361, d3739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27547 p hg
    simpa only [d3361, d3739, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27549 (p : Pattern) (guard : d5847 p = 1) : d3358 p ≤ (0 : Int) + d3740 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3358, d3740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20135 p hg
    simpa only [d5847, d3358, d3740, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3358, d3740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20238 p hg
    simpa only [d5847, d3358, d3740, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27550 (p : Pattern) (guard : d5847 p = 1) : d3358 p ≤ (0 : Int) + d3741 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27542 p hg
    simpa only [d3741, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27549 p hg
    simpa only [d3741, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27551 (p : Pattern) (guard : d5847 p = 1) : d3358 p ≤ (0 : Int) + d3742 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27550 p hg
    simpa only [d3742, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27549 p hg
    simpa only [d3742, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27552 (p : Pattern) (guard : d5847 p = 1) : d3362 p ≤ (0 : Int) + d3743 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3362, d3743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27551 p hg
    simpa only [d3362, d3743, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3362, d3743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3362, d3743, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27553 (p : Pattern) (guard : d5847 p = 1) : d3363 p ≤ (0 : Int) + d3744 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3363, d3744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27548 p hg
    simpa only [d3363, d3744, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3363, d3744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27552 p hg
    simpa only [d3363, d3744, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27554 (p : Pattern) (guard : d5847 p = 1) : d3358 p ≤ (0 : Int) + d3745 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27542 p hg
    simpa only [d3745, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27547 p hg
    simpa only [d3745, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27555 (p : Pattern) (guard : d5847 p = 1) : d3364 p ≤ (0 : Int) + d3746 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3364, d3746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27554 p hg
    simpa only [d3364, d3746, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3364, d3746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27552 p hg
    simpa only [d3364, d3746, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27556 (p : Pattern) (guard : d5847 p = 1) : d3365 p ≤ (0 : Int) + d3747 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3365, d3747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27553 p hg
    simpa only [d3365, d3747, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3365, d3747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27555 p hg
    simpa only [d3365, d3747, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27557 (p : Pattern) (guard : d5847 p = 1) : d3366 p ≤ (0 : Int) + d106 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20165 p hg
    simpa only [d5847, d3366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20170 p hg
    simpa only [d5847, d3366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27558 (p : Pattern) (guard : d5847 p = 1) : d3366 p ≤ (0 : Int) + d3748 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3366, d3748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20165 p hg
    simpa only [d5847, d3366, d3748, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3366, d3748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19893 p hg
    simpa only [d5847, d3366, d3748, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27559 (p : Pattern) (guard : d5847 p = 1) : d3366 p ≤ (0 : Int) + d3749 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27557 p hg
    simpa only [d3749, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27558 p hg
    simpa only [d3749, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27560 (p : Pattern) (guard : d5847 p = 1) : d3366 p ≤ (0 : Int) + d3750 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27559 p hg
    simpa only [d3750, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27558 p hg
    simpa only [d3750, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27561 (p : Pattern) (guard : d5847 p = 1) : d3366 p ≤ (0 : Int) + d3751 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27557 p hg
    simpa only [d3751, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27560 p hg
    simpa only [d3751, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27562 (p : Pattern) (guard : d5847 p = 1) : d3366 p ≤ (0 : Int) + d3752 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3366, d3752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20165 p hg
    simpa only [d5847, d3366, d3752, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3366, d3752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20290 p hg
    simpa only [d5847, d3366, d3752, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27563 (p : Pattern) (guard : d5847 p = 1) : d3366 p ≤ (0 : Int) + d3753 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27557 p hg
    simpa only [d3753, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27562 p hg
    simpa only [d3753, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27564 (p : Pattern) (guard : d5847 p = 1) : d3366 p ≤ (0 : Int) + d3754 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27563 p hg
    simpa only [d3754, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27562 p hg
    simpa only [d3754, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27565 (p : Pattern) (guard : d5847 p = 1) : d3367 p ≤ (0 : Int) + d3755 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3367, d3755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27564 p hg
    simpa only [d3367, d3755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3367, d3755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3367, d3755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27566 (p : Pattern) (guard : d5847 p = 1) : d3368 p ≤ (0 : Int) + d3756 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3368, d3756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27561 p hg
    simpa only [d3368, d3756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3368, d3756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27565 p hg
    simpa only [d3368, d3756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27567 (p : Pattern) (guard : d5847 p = 1) : d3369 p ≤ (0 : Int) + d3757 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3369, d3757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27555 p hg
    simpa only [d3369, d3757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3369, d3757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27566 p hg
    simpa only [d3369, d3757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27568 (p : Pattern) (guard : d5847 p = 1) : d3370 p ≤ (0 : Int) + d3758 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3370, d3758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27556 p hg
    simpa only [d3370, d3758, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3370, d3758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27567 p hg
    simpa only [d3370, d3758, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27569 (p : Pattern) (guard : d5847 p = 1) : d3371 p ≤ (0 : Int) + d3759 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3371, d3759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27433 p hg
    simpa only [d3371, d3759, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3371, d3759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3371, d3759, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27570 (p : Pattern) (guard : d5847 p = 1) : d3372 p ≤ (0 : Int) + d3760 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3372, d3760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27567 p hg
    simpa only [d3372, d3760, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3372, d3760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27569 p hg
    simpa only [d3372, d3760, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27571 (p : Pattern) (guard : d5847 p = 1) : d3373 p ≤ (0 : Int) + d3761 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3373, d3761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27568 p hg
    simpa only [d3373, d3761, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3373, d3761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27570 p hg
    simpa only [d3373, d3761, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27572 (p : Pattern) (guard : d5847 p = 1) : d3358 p ≤ (0 : Int) + d3762 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3358, d3762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20135 p hg
    simpa only [d5847, d3358, d3762, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3358, d3762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20290 p hg
    simpa only [d5847, d3358, d3762, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27573 (p : Pattern) (guard : d5847 p = 1) : d3358 p ≤ (0 : Int) + d3763 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27542 p hg
    simpa only [d3763, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27572 p hg
    simpa only [d3763, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27574 (p : Pattern) (guard : d5847 p = 1) : d3358 p ≤ (0 : Int) + d1955 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3358, d1955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20135 p hg
    simpa only [d5847, d3358, d1955, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3358, d1955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19996 p hg
    simpa only [d5847, d3358, d1955, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27575 (p : Pattern) (guard : d5847 p = 1) : d3358 p ≤ (0 : Int) + d3764 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27545 p hg
    simpa only [d3764, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27574 p hg
    simpa only [d3764, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27576 (p : Pattern) (guard : d5847 p = 1) : d3358 p ≤ (0 : Int) + d3765 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27573 p hg
    simpa only [d3765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27575 p hg
    simpa only [d3765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27577 (p : Pattern) (guard : d5847 p = 1) : d3358 p ≤ (0 : Int) + d3766 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27542 p hg
    simpa only [d3766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27576 p hg
    simpa only [d3766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27578 (p : Pattern) (guard : d5847 p = 1) : d3374 p ≤ (0 : Int) + d115 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20197 p hg
    simpa only [d5847, d3374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20238 p hg
    simpa only [d5847, d3374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27579 (p : Pattern) (guard : d5847 p = 1) : d3374 p ≤ (0 : Int) + d3767 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3374, d3767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20197 p hg
    simpa only [d5847, d3374, d3767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3374, d3767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19893 p hg
    simpa only [d5847, d3374, d3767, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
