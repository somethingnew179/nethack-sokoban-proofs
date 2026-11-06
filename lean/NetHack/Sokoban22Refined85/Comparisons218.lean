/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons217
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare30520 (p : Pattern) (guard : d5847 p = 1) : d3730 p ≤ (0 : Int) + d3350 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3730, d3350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30519 p hg
    simpa only [d3730, d3350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3730, d3350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30490 p hg
    simpa only [d3730, d3350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30521 (p : Pattern) (guard : d5847 p = 1) : d3707 p ≤ (0 : Int) + d3299 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3707, d3299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30330 p hg
    simpa only [d3707, d3299, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3707, d3299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30341 p hg
    simpa only [d3707, d3299, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30522 (p : Pattern) (guard : d5847 p = 1) : d3708 p ≤ (0 : Int) + d3300 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3708, d3300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30521 p hg
    simpa only [d3708, d3300, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3708, d3300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30353 p hg
    simpa only [d3708, d3300, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30523 (p : Pattern) (guard : d5847 p = 1) : d3709 p ≤ (0 : Int) + d3351 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3709, d3351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30522 p hg
    simpa only [d3709, d3351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3709, d3351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30398 p hg
    simpa only [d3709, d3351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30524 (p : Pattern) (guard : d5847 p = 1) : d3714 p ≤ (0 : Int) + d3352 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3714, d3352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30523 p hg
    simpa only [d3714, d3352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3714, d3352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30499 p hg
    simpa only [d3714, d3352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30525 (p : Pattern) (guard : d5847 p = 1) : d3715 p ≤ (0 : Int) + d3353 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3715, d3353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30524 p hg
    simpa only [d3715, d3353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3715, d3353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30480 p hg
    simpa only [d3715, d3353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30526 (p : Pattern) (guard : d5847 p = 1) : d3717 p ≤ (0 : Int) + d3354 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3717, d3354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30525 p hg
    simpa only [d3717, d3354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3717, d3354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30502 p hg
    simpa only [d3717, d3354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30527 (p : Pattern) (guard : d5847 p = 1) : d3731 p ≤ (0 : Int) + d3355 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3731, d3355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30520 p hg
    simpa only [d3731, d3355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3731, d3355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30526 p hg
    simpa only [d3731, d3355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30528 (p : Pattern) (guard : d5847 p = 1) : d3732 p ≤ (0 : Int) + d3356 p := by
  cases selected : p 71 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3732, d3356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30504 p hg
    simpa only [d3732, d3356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3732, d3356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30527 p hg
    simpa only [d3732, d3356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30529 (p : Pattern) (guard : d5847 p = 1) : d3733 p ≤ (0 : Int) + d3357 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3733, d3357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29462 p hg
    simpa only [d5847, d3733, d3357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3733, d3357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17786 p hg
    simpa only [d5847, d3733, d3357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30530 (p : Pattern) (guard : d5847 p = 1) : d102 p ≤ (0 : Int) + d3358 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26431 p hg
    simpa only [d5847, d3358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17788 p hg
    simpa only [d5847, d3358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30531 (p : Pattern) (guard : d5847 p = 1) : d3734 p ≤ (0 : Int) + d3359 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3734, d3359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30529 p hg
    simpa only [d3734, d3359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3734, d3359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30530 p hg
    simpa only [d3734, d3359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30532 (p : Pattern) (guard : d5847 p = 1) : d3735 p ≤ (0 : Int) + d3360 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3735, d3360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30531 p hg
    simpa only [d3735, d3360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3735, d3360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30530 p hg
    simpa only [d3735, d3360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30533 (p : Pattern) (guard : d5847 p = 1) : d3736 p ≤ (0 : Int) + d3358 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3736, d3358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26431 p hg
    simpa only [d5847, d3736, d3358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3736, d3358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17797 p hg
    simpa only [d5847, d3736, d3358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30534 (p : Pattern) (guard : d5847 p = 1) : d3737 p ≤ (0 : Int) + d3358 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30530 p hg
    simpa only [d3737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30533 p hg
    simpa only [d3737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30535 (p : Pattern) (guard : d5847 p = 1) : d3738 p ≤ (0 : Int) + d3358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30534 p hg
    simpa only [d3738, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30533 p hg
    simpa only [d3738, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30536 (p : Pattern) (guard : d5847 p = 1) : d3739 p ≤ (0 : Int) + d3361 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3739, d3361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30532 p hg
    simpa only [d3739, d3361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3739, d3361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30535 p hg
    simpa only [d3739, d3361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30537 (p : Pattern) (guard : d5847 p = 1) : d3740 p ≤ (0 : Int) + d3358 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3740, d3358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26431 p hg
    simpa only [d5847, d3740, d3358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3740, d3358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17806 p hg
    simpa only [d5847, d3740, d3358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30538 (p : Pattern) (guard : d5847 p = 1) : d3741 p ≤ (0 : Int) + d3358 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30530 p hg
    simpa only [d3741, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30537 p hg
    simpa only [d3741, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30539 (p : Pattern) (guard : d5847 p = 1) : d3742 p ≤ (0 : Int) + d3358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30538 p hg
    simpa only [d3742, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30537 p hg
    simpa only [d3742, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30540 (p : Pattern) (guard : d5847 p = 1) : d3743 p ≤ (0 : Int) + d3362 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3743, d3362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30539 p hg
    simpa only [d3743, d3362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3743, d3362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3743, d3362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30541 (p : Pattern) (guard : d5847 p = 1) : d3744 p ≤ (0 : Int) + d3363 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3744, d3363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30536 p hg
    simpa only [d3744, d3363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3744, d3363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30540 p hg
    simpa only [d3744, d3363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30542 (p : Pattern) (guard : d5847 p = 1) : d3745 p ≤ (0 : Int) + d3358 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30530 p hg
    simpa only [d3745, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30535 p hg
    simpa only [d3745, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30543 (p : Pattern) (guard : d5847 p = 1) : d3746 p ≤ (0 : Int) + d3364 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3746, d3364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30542 p hg
    simpa only [d3746, d3364, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3746, d3364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30540 p hg
    simpa only [d3746, d3364, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30544 (p : Pattern) (guard : d5847 p = 1) : d3747 p ≤ (0 : Int) + d3365 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3747, d3365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30541 p hg
    simpa only [d3747, d3365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3747, d3365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30543 p hg
    simpa only [d3747, d3365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30545 (p : Pattern) (guard : d5847 p = 1) : d106 p ≤ (0 : Int) + d3366 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26437 p hg
    simpa only [d5847, d3366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17797 p hg
    simpa only [d5847, d3366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30546 (p : Pattern) (guard : d5847 p = 1) : d3748 p ≤ (0 : Int) + d3366 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3748, d3366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26437 p hg
    simpa only [d5847, d3748, d3366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3748, d3366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17666 p hg
    simpa only [d5847, d3748, d3366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30547 (p : Pattern) (guard : d5847 p = 1) : d3749 p ≤ (0 : Int) + d3366 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30545 p hg
    simpa only [d3749, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30546 p hg
    simpa only [d3749, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30548 (p : Pattern) (guard : d5847 p = 1) : d3750 p ≤ (0 : Int) + d3366 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30547 p hg
    simpa only [d3750, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30546 p hg
    simpa only [d3750, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30549 (p : Pattern) (guard : d5847 p = 1) : d3751 p ≤ (0 : Int) + d3366 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30545 p hg
    simpa only [d3751, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30548 p hg
    simpa only [d3751, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30550 (p : Pattern) (guard : d5847 p = 1) : d3752 p ≤ (0 : Int) + d3366 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3752, d3366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26437 p hg
    simpa only [d5847, d3752, d3366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3752, d3366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17810 p hg
    simpa only [d5847, d3752, d3366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30551 (p : Pattern) (guard : d5847 p = 1) : d3753 p ≤ (0 : Int) + d3366 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30545 p hg
    simpa only [d3753, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30550 p hg
    simpa only [d3753, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30552 (p : Pattern) (guard : d5847 p = 1) : d3754 p ≤ (0 : Int) + d3366 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30551 p hg
    simpa only [d3754, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30550 p hg
    simpa only [d3754, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30553 (p : Pattern) (guard : d5847 p = 1) : d3755 p ≤ (0 : Int) + d3367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3755, d3367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30552 p hg
    simpa only [d3755, d3367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3755, d3367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3755, d3367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30554 (p : Pattern) (guard : d5847 p = 1) : d3756 p ≤ (0 : Int) + d3368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3756, d3368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30549 p hg
    simpa only [d3756, d3368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3756, d3368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30553 p hg
    simpa only [d3756, d3368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30555 (p : Pattern) (guard : d5847 p = 1) : d3757 p ≤ (0 : Int) + d3369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3757, d3369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30543 p hg
    simpa only [d3757, d3369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3757, d3369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30554 p hg
    simpa only [d3757, d3369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30556 (p : Pattern) (guard : d5847 p = 1) : d3758 p ≤ (0 : Int) + d3370 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3758, d3370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30544 p hg
    simpa only [d3758, d3370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3758, d3370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30555 p hg
    simpa only [d3758, d3370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30557 (p : Pattern) (guard : d5847 p = 1) : d3759 p ≤ (0 : Int) + d3371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3759, d3371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30421 p hg
    simpa only [d3759, d3371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3759, d3371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3759, d3371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30558 (p : Pattern) (guard : d5847 p = 1) : d3760 p ≤ (0 : Int) + d3372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3760, d3372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30555 p hg
    simpa only [d3760, d3372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3760, d3372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30557 p hg
    simpa only [d3760, d3372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30559 (p : Pattern) (guard : d5847 p = 1) : d3761 p ≤ (0 : Int) + d3373 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3761, d3373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30556 p hg
    simpa only [d3761, d3373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3761, d3373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30558 p hg
    simpa only [d3761, d3373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30560 (p : Pattern) (guard : d5847 p = 1) : d3762 p ≤ (0 : Int) + d3358 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3762, d3358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26431 p hg
    simpa only [d5847, d3762, d3358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3762, d3358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17810 p hg
    simpa only [d5847, d3762, d3358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30561 (p : Pattern) (guard : d5847 p = 1) : d3763 p ≤ (0 : Int) + d3358 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30530 p hg
    simpa only [d3763, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30560 p hg
    simpa only [d3763, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30562 (p : Pattern) (guard : d5847 p = 1) : d1955 p ≤ (0 : Int) + d3358 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d1955, d3358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26431 p hg
    simpa only [d5847, d1955, d3358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d1955, d3358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17706 p hg
    simpa only [d5847, d1955, d3358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30563 (p : Pattern) (guard : d5847 p = 1) : d3764 p ≤ (0 : Int) + d3358 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30533 p hg
    simpa only [d3764, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30562 p hg
    simpa only [d3764, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30564 (p : Pattern) (guard : d5847 p = 1) : d3765 p ≤ (0 : Int) + d3358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30561 p hg
    simpa only [d3765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30563 p hg
    simpa only [d3765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30565 (p : Pattern) (guard : d5847 p = 1) : d3766 p ≤ (0 : Int) + d3358 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30530 p hg
    simpa only [d3766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30564 p hg
    simpa only [d3766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30566 (p : Pattern) (guard : d5847 p = 1) : d115 p ≤ (0 : Int) + d3374 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26448 p hg
    simpa only [d5847, d3374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17806 p hg
    simpa only [d5847, d3374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30567 (p : Pattern) (guard : d5847 p = 1) : d3767 p ≤ (0 : Int) + d3374 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3767, d3374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26448 p hg
    simpa only [d5847, d3767, d3374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3767, d3374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17666 p hg
    simpa only [d5847, d3767, d3374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30568 (p : Pattern) (guard : d5847 p = 1) : d3768 p ≤ (0 : Int) + d3374 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30566 p hg
    simpa only [d3768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30567 p hg
    simpa only [d3768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30569 (p : Pattern) (guard : d5847 p = 1) : d3769 p ≤ (0 : Int) + d3374 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3769, d3374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26448 p hg
    simpa only [d5847, d3769, d3374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3769, d3374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17810 p hg
    simpa only [d5847, d3769, d3374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30570 (p : Pattern) (guard : d5847 p = 1) : d1896 p ≤ (0 : Int) + d3374 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d1896, d3374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26448 p hg
    simpa only [d5847, d1896, d3374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d1896, d3374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5847, d1896, d3374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30571 (p : Pattern) (guard : d5847 p = 1) : d3770 p ≤ (0 : Int) + d3374 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30569 p hg
    simpa only [d3770, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30570 p hg
    simpa only [d3770, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30572 (p : Pattern) (guard : d5847 p = 1) : d3771 p ≤ (0 : Int) + d3374 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30568 p hg
    simpa only [d3771, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30571 p hg
    simpa only [d3771, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30573 (p : Pattern) (guard : d5847 p = 1) : d3772 p ≤ (0 : Int) + d3375 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3772, d3375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30572 p hg
    simpa only [d3772, d3375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3772, d3375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3772, d3375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30574 (p : Pattern) (guard : d5847 p = 1) : d3773 p ≤ (0 : Int) + d3376 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3773, d3376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30565 p hg
    simpa only [d3773, d3376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3773, d3376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30573 p hg
    simpa only [d3773, d3376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30575 (p : Pattern) (guard : d5847 p = 1) : d119 p ≤ (0 : Int) + d3377 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26454 p hg
    simpa only [d5847, d3377, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17810 p hg
    simpa only [d5847, d3377, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30576 (p : Pattern) (guard : d5847 p = 1) : d317 p ≤ (0 : Int) + d3377 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d317, d3377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26454 p hg
    simpa only [d5847, d317, d3377, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d317, d3377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5847, d317, d3377, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30577 (p : Pattern) (guard : d5847 p = 1) : d3774 p ≤ (0 : Int) + d3377 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30575 p hg
    simpa only [d3774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30576 p hg
    simpa only [d3774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30578 (p : Pattern) (guard : d5847 p = 1) : d3775 p ≤ (0 : Int) + d3377 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3775, d3377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26454 p hg
    simpa only [d5847, d3775, d3377, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3775, d3377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17682 p hg
    simpa only [d5847, d3775, d3377, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30579 (p : Pattern) (guard : d5847 p = 1) : d3776 p ≤ (0 : Int) + d3377 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30578 p hg
    simpa only [d3776, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30576 p hg
    simpa only [d3776, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30580 (p : Pattern) (guard : d5847 p = 1) : d3777 p ≤ (0 : Int) + d3377 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30577 p hg
    simpa only [d3777, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30579 p hg
    simpa only [d3777, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30581 (p : Pattern) (guard : d5847 p = 1) : d3778 p ≤ (0 : Int) + d3378 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3778, d3378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30580 p hg
    simpa only [d3778, d3378, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3778, d3378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3778, d3378, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30582 (p : Pattern) (guard : d5847 p = 1) : d3779 p ≤ (0 : Int) + d3379 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3779, d3379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30565 p hg
    simpa only [d3779, d3379, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3779, d3379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30581 p hg
    simpa only [d3779, d3379, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30583 (p : Pattern) (guard : d5847 p = 1) : d3780 p ≤ (0 : Int) + d3380 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3780, d3380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30574 p hg
    simpa only [d3780, d3380, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3780, d3380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30582 p hg
    simpa only [d3780, d3380, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30584 (p : Pattern) (guard : d5847 p = 1) : d3781 p ≤ (0 : Int) + d3381 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3781, d3381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30565 p hg
    simpa only [d3781, d3381, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3781, d3381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3781, d3381, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30585 (p : Pattern) (guard : d5847 p = 1) : d3782 p ≤ (0 : Int) + d3366 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3782, d3366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26437 p hg
    simpa only [d5847, d3782, d3366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3782, d3366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17682 p hg
    simpa only [d5847, d3782, d3366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30586 (p : Pattern) (guard : d5847 p = 1) : d3783 p ≤ (0 : Int) + d3366 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30545 p hg
    simpa only [d3783, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30585 p hg
    simpa only [d3783, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30587 (p : Pattern) (guard : d5847 p = 1) : d348 p ≤ (0 : Int) + d3366 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d348, d3366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26437 p hg
    simpa only [d5847, d348, d3366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d348, d3366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5847, d348, d3366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30588 (p : Pattern) (guard : d5847 p = 1) : d3784 p ≤ (0 : Int) + d3366 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30546 p hg
    simpa only [d3784, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30587 p hg
    simpa only [d3784, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30589 (p : Pattern) (guard : d5847 p = 1) : d3785 p ≤ (0 : Int) + d3366 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30586 p hg
    simpa only [d3785, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30588 p hg
    simpa only [d3785, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30590 (p : Pattern) (guard : d5847 p = 1) : d3786 p ≤ (0 : Int) + d3366 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30545 p hg
    simpa only [d3786, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30589 p hg
    simpa only [d3786, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30591 (p : Pattern) (guard : d5847 p = 1) : d3787 p ≤ (0 : Int) + d3382 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3787, d3382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30590 p hg
    simpa only [d3787, d3382, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3787, d3382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3787, d3382, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30592 (p : Pattern) (guard : d5847 p = 1) : d3788 p ≤ (0 : Int) + d3383 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3788, d3383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30584 p hg
    simpa only [d3788, d3383, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3788, d3383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30591 p hg
    simpa only [d3788, d3383, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30593 (p : Pattern) (guard : d5847 p = 1) : d3789 p ≤ (0 : Int) + d3384 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3789, d3384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30583 p hg
    simpa only [d3789, d3384, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3789, d3384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30592 p hg
    simpa only [d3789, d3384, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30594 (p : Pattern) (guard : d5847 p = 1) : d3790 p ≤ (0 : Int) + d3385 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3790, d3385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30433 p hg
    simpa only [d3790, d3385, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3790, d3385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3790, d3385, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30595 (p : Pattern) (guard : d5847 p = 1) : d3791 p ≤ (0 : Int) + d3386 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3791, d3386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30592 p hg
    simpa only [d3791, d3386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3791, d3386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30594 p hg
    simpa only [d3791, d3386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30596 (p : Pattern) (guard : d5847 p = 1) : d3792 p ≤ (0 : Int) + d3387 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3792, d3387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30593 p hg
    simpa only [d3792, d3387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3792, d3387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30595 p hg
    simpa only [d3792, d3387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30597 (p : Pattern) (guard : d5847 p = 1) : d3793 p ≤ (0 : Int) + d3388 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3793, d3388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30559 p hg
    simpa only [d3793, d3388, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3793, d3388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30596 p hg
    simpa only [d3793, d3388, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30598 (p : Pattern) (guard : d5847 p = 1) : d102 p ≤ (0 : Int) + d3389 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26431 p hg
    simpa only [d5847, d3389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17823 p hg
    simpa only [d5847, d3389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30599 (p : Pattern) (guard : d5847 p = 1) : d102 p ≤ (0 : Int) + d3390 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30598 p hg
    simpa only [d3390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30530 p hg
    simpa only [d3390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30600 (p : Pattern) (guard : d5847 p = 1) : d102 p ≤ (0 : Int) + d3391 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30599 p hg
    simpa only [d3391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30530 p hg
    simpa only [d3391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30601 (p : Pattern) (guard : d5847 p = 1) : d3745 p ≤ (0 : Int) + d3392 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3745, d3392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30600 p hg
    simpa only [d3745, d3392, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3745, d3392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30535 p hg
    simpa only [d3745, d3392, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30602 (p : Pattern) (guard : d5847 p = 1) : d3746 p ≤ (0 : Int) + d3393 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3746, d3393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30601 p hg
    simpa only [d3746, d3393, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3746, d3393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30540 p hg
    simpa only [d3746, d3393, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30603 (p : Pattern) (guard : d5847 p = 1) : d3794 p ≤ (0 : Int) + d3374 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30566 p hg
    simpa only [d3794, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30569 p hg
    simpa only [d3794, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30604 (p : Pattern) (guard : d5847 p = 1) : d3795 p ≤ (0 : Int) + d3374 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30603 p hg
    simpa only [d3795, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30569 p hg
    simpa only [d3795, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30605 (p : Pattern) (guard : d5847 p = 1) : d3796 p ≤ (0 : Int) + d3374 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30566 p hg
    simpa only [d3796, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30604 p hg
    simpa only [d3796, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30606 (p : Pattern) (guard : d5847 p = 1) : d3797 p ≤ (0 : Int) + d3374 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3797, d3374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26448 p hg
    simpa only [d5847, d3797, d3374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3797, d3374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17797 p hg
    simpa only [d5847, d3797, d3374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30607 (p : Pattern) (guard : d5847 p = 1) : d3798 p ≤ (0 : Int) + d3374 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30566 p hg
    simpa only [d3798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30606 p hg
    simpa only [d3798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30608 (p : Pattern) (guard : d5847 p = 1) : d3799 p ≤ (0 : Int) + d3374 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30607 p hg
    simpa only [d3799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30606 p hg
    simpa only [d3799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30609 (p : Pattern) (guard : d5847 p = 1) : d3800 p ≤ (0 : Int) + d3375 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3800, d3375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30608 p hg
    simpa only [d3800, d3375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3800, d3375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3800, d3375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30610 (p : Pattern) (guard : d5847 p = 1) : d3801 p ≤ (0 : Int) + d3394 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3801, d3394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30605 p hg
    simpa only [d3801, d3394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3801, d3394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30609 p hg
    simpa only [d3801, d3394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30611 (p : Pattern) (guard : d5847 p = 1) : d3802 p ≤ (0 : Int) + d3395 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3802, d3395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30602 p hg
    simpa only [d3802, d3395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3802, d3395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30610 p hg
    simpa only [d3802, d3395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30612 (p : Pattern) (guard : d5847 p = 1) : d3803 p ≤ (0 : Int) + d3396 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3803, d3396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30554 p hg
    simpa only [d3803, d3396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3803, d3396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30421 p hg
    simpa only [d3803, d3396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30613 (p : Pattern) (guard : d5847 p = 1) : d3804 p ≤ (0 : Int) + d3397 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3804, d3397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30611 p hg
    simpa only [d3804, d3397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3804, d3397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30612 p hg
    simpa only [d3804, d3397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30614 (p : Pattern) (guard : d5847 p = 1) : d3805 p ≤ (0 : Int) + d3398 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3805, d3398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30554 p hg
    simpa only [d3805, d3398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3805, d3398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30424 p hg
    simpa only [d3805, d3398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30615 (p : Pattern) (guard : d5847 p = 1) : d3806 p ≤ (0 : Int) + d3399 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3806, d3399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30614 p hg
    simpa only [d3806, d3399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3806, d3399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3806, d3399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30616 (p : Pattern) (guard : d5847 p = 1) : d3807 p ≤ (0 : Int) + d3400 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3807, d3400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30613 p hg
    simpa only [d3807, d3400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3807, d3400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30615 p hg
    simpa only [d3807, d3400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30617 (p : Pattern) (guard : d5847 p = 1) : d3808 p ≤ (0 : Int) + d3374 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30566 p hg
    simpa only [d3808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30572 p hg
    simpa only [d3808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30618 (p : Pattern) (guard : d5847 p = 1) : d3809 p ≤ (0 : Int) + d3401 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3809, d3401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30617 p hg
    simpa only [d3809, d3401, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3809, d3401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3809, d3401, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30619 (p : Pattern) (guard : d5847 p = 1) : d3810 p ≤ (0 : Int) + d3402 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3810, d3402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30582 p hg
    simpa only [d3810, d3402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3810, d3402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30618 p hg
    simpa only [d3810, d3402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30620 (p : Pattern) (guard : d5847 p = 1) : d3811 p ≤ (0 : Int) + d3403 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3811, d3403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30591 p hg
    simpa only [d3811, d3403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3811, d3403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30433 p hg
    simpa only [d3811, d3403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30621 (p : Pattern) (guard : d5847 p = 1) : d3812 p ≤ (0 : Int) + d3404 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3812, d3404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30619 p hg
    simpa only [d3812, d3404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3812, d3404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30620 p hg
    simpa only [d3812, d3404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30622 (p : Pattern) (guard : d5847 p = 1) : d3813 p ≤ (0 : Int) + d3405 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3813, d3405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30591 p hg
    simpa only [d3813, d3405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3813, d3405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30435 p hg
    simpa only [d3813, d3405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30623 (p : Pattern) (guard : d5847 p = 1) : d3814 p ≤ (0 : Int) + d3406 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3814, d3406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30622 p hg
    simpa only [d3814, d3406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3814, d3406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3814, d3406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30624 (p : Pattern) (guard : d5847 p = 1) : d3815 p ≤ (0 : Int) + d3407 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3815, d3407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30621 p hg
    simpa only [d3815, d3407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3815, d3407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30623 p hg
    simpa only [d3815, d3407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30625 (p : Pattern) (guard : d5847 p = 1) : d3816 p ≤ (0 : Int) + d3408 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3816, d3408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30616 p hg
    simpa only [d3816, d3408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3816, d3408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30624 p hg
    simpa only [d3816, d3408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30626 (p : Pattern) (guard : d5847 p = 1) : d3817 p ≤ (0 : Int) + d3409 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3817, d3409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30597 p hg
    simpa only [d3817, d3409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3817, d3409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30625 p hg
    simpa only [d3817, d3409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30627 (p : Pattern) (guard : d5847 p = 1) : d3818 p ≤ (0 : Int) + d3358 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30533 p hg
    simpa only [d3818, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30560 p hg
    simpa only [d3818, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30628 (p : Pattern) (guard : d5847 p = 1) : d3819 p ≤ (0 : Int) + d3358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30561 p hg
    simpa only [d3819, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30627 p hg
    simpa only [d3819, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30629 (p : Pattern) (guard : d5847 p = 1) : d3820 p ≤ (0 : Int) + d3358 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30530 p hg
    simpa only [d3820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30628 p hg
    simpa only [d3820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30630 (p : Pattern) (guard : d5847 p = 1) : d3821 p ≤ (0 : Int) + d3362 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3821, d3362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30535 p hg
    simpa only [d3821, d3362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3821, d3362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3821, d3362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30631 (p : Pattern) (guard : d5847 p = 1) : d3822 p ≤ (0 : Int) + d3364 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3822, d3364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30629 p hg
    simpa only [d3822, d3364, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3822, d3364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30630 p hg
    simpa only [d3822, d3364, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30632 (p : Pattern) (guard : d5847 p = 1) : d3823 p ≤ (0 : Int) + d3358 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3823, d3358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26431 p hg
    simpa only [d5847, d3823, d3358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3823, d3358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17666 p hg
    simpa only [d5847, d3823, d3358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30633 (p : Pattern) (guard : d5847 p = 1) : d3824 p ≤ (0 : Int) + d3358 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30533 p hg
    simpa only [d3824, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30632 p hg
    simpa only [d3824, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30634 (p : Pattern) (guard : d5847 p = 1) : d3825 p ≤ (0 : Int) + d3358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30561 p hg
    simpa only [d3825, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30633 p hg
    simpa only [d3825, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30635 (p : Pattern) (guard : d5847 p = 1) : d3826 p ≤ (0 : Int) + d3362 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3826, d3362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30634 p hg
    simpa only [d3826, d3362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3826, d3362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3826, d3362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30636 (p : Pattern) (guard : d5847 p = 1) : d3827 p ≤ (0 : Int) + d3364 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3827, d3364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30565 p hg
    simpa only [d3827, d3364, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3827, d3364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30635 p hg
    simpa only [d3827, d3364, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30637 (p : Pattern) (guard : d5847 p = 1) : d3828 p ≤ (0 : Int) + d3364 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30631 p hg
    simpa only [d3828, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30636 p hg
    simpa only [d3828, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30638 (p : Pattern) (guard : d5847 p = 1) : d3829 p ≤ (0 : Int) + d3362 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3829, d3362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30564 p hg
    simpa only [d3829, d3362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3829, d3362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3829, d3362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30639 (p : Pattern) (guard : d5847 p = 1) : d3830 p ≤ (0 : Int) + d3364 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3830, d3364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30565 p hg
    simpa only [d3830, d3364, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3830, d3364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30638 p hg
    simpa only [d3830, d3364, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30640 (p : Pattern) (guard : d5847 p = 1) : d3831 p ≤ (0 : Int) + d3367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3831, d3367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30589 p hg
    simpa only [d3831, d3367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3831, d3367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3831, d3367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30641 (p : Pattern) (guard : d5847 p = 1) : d3832 p ≤ (0 : Int) + d3368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3832, d3368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30590 p hg
    simpa only [d3832, d3368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3832, d3368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30640 p hg
    simpa only [d3832, d3368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30642 (p : Pattern) (guard : d5847 p = 1) : d3833 p ≤ (0 : Int) + d3369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3833, d3369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30639 p hg
    simpa only [d3833, d3369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3833, d3369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30641 p hg
    simpa only [d3833, d3369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30643 (p : Pattern) (guard : d5847 p = 1) : d3834 p ≤ (0 : Int) + d3410 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3834, d3410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30637 p hg
    simpa only [d3834, d3410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3834, d3410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30642 p hg
    simpa only [d3834, d3410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30644 (p : Pattern) (guard : d5847 p = 1) : d3835 p ≤ (0 : Int) + d3372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3835, d3372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30642 p hg
    simpa only [d3835, d3372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3835, d3372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30557 p hg
    simpa only [d3835, d3372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30645 (p : Pattern) (guard : d5847 p = 1) : d3836 p ≤ (0 : Int) + d3411 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3836, d3411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30643 p hg
    simpa only [d3836, d3411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3836, d3411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30644 p hg
    simpa only [d3836, d3411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30646 (p : Pattern) (guard : d5847 p = 1) : d3837 p ≤ (0 : Int) + d3394 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3837, d3394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30617 p hg
    simpa only [d3837, d3394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3837, d3394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30573 p hg
    simpa only [d3837, d3394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30647 (p : Pattern) (guard : d5847 p = 1) : d3838 p ≤ (0 : Int) + d3377 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30575 p hg
    simpa only [d3838, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30580 p hg
    simpa only [d3838, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30648 (p : Pattern) (guard : d5847 p = 1) : d3839 p ≤ (0 : Int) + d3412 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3839, d3412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30647 p hg
    simpa only [d3839, d3412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3839, d3412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30581 p hg
    simpa only [d3839, d3412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30649 (p : Pattern) (guard : d5847 p = 1) : d3840 p ≤ (0 : Int) + d3413 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3840, d3413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30646 p hg
    simpa only [d3840, d3413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3840, d3413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30648 p hg
    simpa only [d3840, d3413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30650 (p : Pattern) (guard : d5847 p = 1) : d3841 p ≤ (0 : Int) + d3414 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3841, d3414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30649 p hg
    simpa only [d3841, d3414, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3841, d3414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3841, d3414, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30651 (p : Pattern) (guard : d5847 p = 1) : d3842 p ≤ (0 : Int) + d3415 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3842, d3415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30650 p hg
    simpa only [d3842, d3415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3842, d3415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3842, d3415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30652 (p : Pattern) (guard : d5847 p = 1) : d3843 p ≤ (0 : Int) + d3416 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3843, d3416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30645 p hg
    simpa only [d3843, d3416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3843, d3416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30651 p hg
    simpa only [d3843, d3416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30653 (p : Pattern) (guard : d5847 p = 1) : d3844 p ≤ (0 : Int) + d3417 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3844, d3417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30636 p hg
    simpa only [d3844, d3417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3844, d3417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30646 p hg
    simpa only [d3844, d3417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30654 (p : Pattern) (guard : d5847 p = 1) : d3845 p ≤ (0 : Int) + d3396 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3845, d3396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30641 p hg
    simpa only [d3845, d3396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3845, d3396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30421 p hg
    simpa only [d3845, d3396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30655 (p : Pattern) (guard : d5847 p = 1) : d3846 p ≤ (0 : Int) + d3418 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3846, d3418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30653 p hg
    simpa only [d3846, d3418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3846, d3418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30654 p hg
    simpa only [d3846, d3418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30656 (p : Pattern) (guard : d5847 p = 1) : d3847 p ≤ (0 : Int) + d3398 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3847, d3398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30641 p hg
    simpa only [d3847, d3398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3847, d3398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30424 p hg
    simpa only [d3847, d3398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30657 (p : Pattern) (guard : d5847 p = 1) : d3848 p ≤ (0 : Int) + d3399 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3848, d3399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30656 p hg
    simpa only [d3848, d3399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3848, d3399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3848, d3399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30658 (p : Pattern) (guard : d5847 p = 1) : d3849 p ≤ (0 : Int) + d3419 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3849, d3419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30655 p hg
    simpa only [d3849, d3419, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3849, d3419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30657 p hg
    simpa only [d3849, d3419, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30659 (p : Pattern) (guard : d5847 p = 1) : d3850 p ≤ (0 : Int) + d3420 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3850, d3420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30648 p hg
    simpa only [d3850, d3420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3850, d3420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3850, d3420, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
