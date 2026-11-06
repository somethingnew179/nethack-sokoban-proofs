/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons218
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare30660 (p : Pattern) (guard : d5847 p = 1) : d3851 p ≤ (0 : Int) + d3421 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3851, d3421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30659 p hg
    simpa only [d3851, d3421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3851, d3421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3851, d3421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30661 (p : Pattern) (guard : d5847 p = 1) : d3852 p ≤ (0 : Int) + d3422 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3852, d3422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30660 p hg
    simpa only [d3852, d3422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3852, d3422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3852, d3422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30662 (p : Pattern) (guard : d5847 p = 1) : d3853 p ≤ (0 : Int) + d3423 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3853, d3423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30658 p hg
    simpa only [d3853, d3423, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3853, d3423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30661 p hg
    simpa only [d3853, d3423, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30663 (p : Pattern) (guard : d5847 p = 1) : d3854 p ≤ (0 : Int) + d3424 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3854, d3424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30652 p hg
    simpa only [d3854, d3424, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3854, d3424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30662 p hg
    simpa only [d3854, d3424, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30664 (p : Pattern) (guard : d5847 p = 1) : d3855 p ≤ (0 : Int) + d3425 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3855, d3425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30626 p hg
    simpa only [d3855, d3425, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3855, d3425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30663 p hg
    simpa only [d3855, d3425, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30665 (p : Pattern) (guard : d5847 p = 1) : d3856 p ≤ (0 : Int) + d3426 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3856, d3426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30557 p hg
    simpa only [d3856, d3426, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3856, d3426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3856, d3426, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30666 (p : Pattern) (guard : d5847 p = 1) : d3857 p ≤ (0 : Int) + d3427 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3857, d3427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30665 p hg
    simpa only [d3857, d3427, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3857, d3427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3857, d3427, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30667 (p : Pattern) (guard : d5847 p = 1) : d3858 p ≤ (0 : Int) + d3428 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3858, d3428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30666 p hg
    simpa only [d3858, d3428, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3858, d3428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3858, d3428, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30668 (p : Pattern) (guard : d5847 p = 1) : d3859 p ≤ (0 : Int) + d3429 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3859, d3429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30667 p hg
    simpa only [d3859, d3429, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3859, d3429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3859, d3429, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30669 (p : Pattern) (guard : d5847 p = 1) : d3860 p ≤ (0 : Int) + d3430 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3860, d3430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30663 p hg
    simpa only [d3860, d3430, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3860, d3430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30668 p hg
    simpa only [d3860, d3430, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30670 (p : Pattern) (guard : d5847 p = 1) : d3861 p ≤ (0 : Int) + d3431 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3861, d3431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30664 p hg
    simpa only [d3861, d3431, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3861, d3431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30669 p hg
    simpa only [d3861, d3431, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30671 (p : Pattern) (guard : d5847 p = 1) : d3862 p ≤ (0 : Int) + d3410 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3862, d3410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30543 p hg
    simpa only [d3862, d3410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3862, d3410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30555 p hg
    simpa only [d3862, d3410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30672 (p : Pattern) (guard : d5847 p = 1) : d3863 p ≤ (0 : Int) + d3411 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3863, d3411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30671 p hg
    simpa only [d3863, d3411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3863, d3411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30558 p hg
    simpa only [d3863, d3411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30673 (p : Pattern) (guard : d5847 p = 1) : d3864 p ≤ (0 : Int) + d3432 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3864, d3432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30672 p hg
    simpa only [d3864, d3432, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3864, d3432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30596 p hg
    simpa only [d3864, d3432, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30674 (p : Pattern) (guard : d5847 p = 1) : d3802 p ≤ (0 : Int) + d3417 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3802, d3417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30543 p hg
    simpa only [d3802, d3417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3802, d3417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30610 p hg
    simpa only [d3802, d3417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30675 (p : Pattern) (guard : d5847 p = 1) : d3804 p ≤ (0 : Int) + d3418 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3804, d3418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30674 p hg
    simpa only [d3804, d3418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3804, d3418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30612 p hg
    simpa only [d3804, d3418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30676 (p : Pattern) (guard : d5847 p = 1) : d3807 p ≤ (0 : Int) + d3419 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3807, d3419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30675 p hg
    simpa only [d3807, d3419, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3807, d3419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30615 p hg
    simpa only [d3807, d3419, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30677 (p : Pattern) (guard : d5847 p = 1) : d3816 p ≤ (0 : Int) + d3433 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3816, d3433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30676 p hg
    simpa only [d3816, d3433, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3816, d3433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30624 p hg
    simpa only [d3816, d3433, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30678 (p : Pattern) (guard : d5847 p = 1) : d3865 p ≤ (0 : Int) + d3434 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3865, d3434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30673 p hg
    simpa only [d3865, d3434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3865, d3434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30677 p hg
    simpa only [d3865, d3434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30679 (p : Pattern) (guard : d5847 p = 1) : d3866 p ≤ (0 : Int) + d3435 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3866, d3435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30678 p hg
    simpa only [d3866, d3435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3866, d3435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30663 p hg
    simpa only [d3866, d3435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30680 (p : Pattern) (guard : d5847 p = 1) : d3867 p ≤ (0 : Int) + d3436 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3867, d3436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30663 p hg
    simpa only [d3867, d3436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3867, d3436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3867, d3436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30681 (p : Pattern) (guard : d5847 p = 1) : d3868 p ≤ (0 : Int) + d3437 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3868, d3437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30679 p hg
    simpa only [d3868, d3437, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3868, d3437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30680 p hg
    simpa only [d3868, d3437, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30682 (p : Pattern) (guard : d5847 p = 1) : d3869 p ≤ (0 : Int) + d3438 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3869, d3438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30670 p hg
    simpa only [d3869, d3438, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3869, d3438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30681 p hg
    simpa only [d3869, d3438, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30683 (p : Pattern) (guard : d5847 p = 1) : d3870 p ≤ (0 : Int) + d3439 p := by
  cases selected : p 71 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3870, d3439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30504 p hg
    simpa only [d3870, d3439, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3870, d3439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30682 p hg
    simpa only [d3870, d3439, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30684 (p : Pattern) (guard : d5847 p = 1) : d3871 p ≤ (0 : Int) + d3440 p := by
  cases selected : p 49 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3871, d3440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30528 p hg
    simpa only [d3871, d3440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3871, d3440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30683 p hg
    simpa only [d3871, d3440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30685 (p : Pattern) (guard : d5847 p = 1) : d3872 p ≤ (0 : Int) + d3239 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30332 p hg
    simpa only [d3872, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30384 p hg
    simpa only [d3872, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30686 (p : Pattern) (guard : d5847 p = 1) : d3873 p ≤ (0 : Int) + d3239 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30385 p hg
    simpa only [d3873, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30685 p hg
    simpa only [d3873, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30687 (p : Pattern) (guard : d5847 p = 1) : d3874 p ≤ (0 : Int) + d3239 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30331 p hg
    simpa only [d3874, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30686 p hg
    simpa only [d3874, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30688 (p : Pattern) (guard : d5847 p = 1) : d3875 p ≤ (0 : Int) + d3240 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3875, d3240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30334 p hg
    simpa only [d3875, d3240, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3875, d3240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3875, d3240, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30689 (p : Pattern) (guard : d5847 p = 1) : d3876 p ≤ (0 : Int) + d3241 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3876, d3241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30687 p hg
    simpa only [d3876, d3241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3876, d3241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30688 p hg
    simpa only [d3876, d3241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30690 (p : Pattern) (guard : d5847 p = 1) : d3877 p ≤ (0 : Int) + d3242 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3877, d3242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30445 p hg
    simpa only [d3877, d3242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3877, d3242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30689 p hg
    simpa only [d3877, d3242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30691 (p : Pattern) (guard : d5847 p = 1) : d3878 p ≤ (0 : Int) + d3299 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3878, d3299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30445 p hg
    simpa only [d3878, d3299, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3878, d3299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30690 p hg
    simpa only [d3878, d3299, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30692 (p : Pattern) (guard : d5847 p = 1) : d3879 p ≤ (0 : Int) + d3248 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3879, d3248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30690 p hg
    simpa only [d3879, d3248, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3879, d3248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30460 p hg
    simpa only [d3879, d3248, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30693 (p : Pattern) (guard : d5847 p = 1) : d3880 p ≤ (0 : Int) + d3300 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3880, d3300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30691 p hg
    simpa only [d3880, d3300, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3880, d3300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30692 p hg
    simpa only [d3880, d3300, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30694 (p : Pattern) (guard : d5847 p = 1) : d3881 p ≤ (0 : Int) + d3441 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3881, d3441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30428 p hg
    simpa only [d3881, d3441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3881, d3441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30376 p hg
    simpa only [d3881, d3441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30695 (p : Pattern) (guard : d5847 p = 1) : d3882 p ≤ (0 : Int) + d3442 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3882, d3442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30463 p hg
    simpa only [d3882, d3442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3882, d3442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30694 p hg
    simpa only [d3882, d3442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30696 (p : Pattern) (guard : d5847 p = 1) : d3883 p ≤ (0 : Int) + d3443 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3883, d3443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30428 p hg
    simpa only [d3883, d3443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3883, d3443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30382 p hg
    simpa only [d3883, d3443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30697 (p : Pattern) (guard : d5847 p = 1) : d3884 p ≤ (0 : Int) + d3444 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3884, d3444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30464 p hg
    simpa only [d3884, d3444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3884, d3444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3884, d3444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30698 (p : Pattern) (guard : d5847 p = 1) : d3885 p ≤ (0 : Int) + d3445 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3885, d3445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30696 p hg
    simpa only [d3885, d3445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3885, d3445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30697 p hg
    simpa only [d3885, d3445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30699 (p : Pattern) (guard : d5847 p = 1) : d3886 p ≤ (0 : Int) + d3446 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3886, d3446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30695 p hg
    simpa only [d3886, d3446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3886, d3446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30698 p hg
    simpa only [d3886, d3446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30700 (p : Pattern) (guard : d5847 p = 1) : d3887 p ≤ (0 : Int) + d3447 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3887, d3447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30429 p hg
    simpa only [d3887, d3447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3887, d3447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30697 p hg
    simpa only [d3887, d3447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30701 (p : Pattern) (guard : d5847 p = 1) : d3888 p ≤ (0 : Int) + d3448 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3888, d3448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30700 p hg
    simpa only [d3888, d3448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3888, d3448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30436 p hg
    simpa only [d3888, d3448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30702 (p : Pattern) (guard : d5847 p = 1) : d3889 p ≤ (0 : Int) + d3449 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3889, d3449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30699 p hg
    simpa only [d3889, d3449, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3889, d3449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30701 p hg
    simpa only [d3889, d3449, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30703 (p : Pattern) (guard : d5847 p = 1) : d3890 p ≤ (0 : Int) + d3450 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3890, d3450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30693 p hg
    simpa only [d3890, d3450, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3890, d3450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30702 p hg
    simpa only [d3890, d3450, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30704 (p : Pattern) (guard : d5847 p = 1) : d3891 p ≤ (0 : Int) + d3250 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30364 p hg
    simpa only [d3891, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30362 p hg
    simpa only [d3891, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30705 (p : Pattern) (guard : d5847 p = 1) : d3892 p ≤ (0 : Int) + d3250 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30363 p hg
    simpa only [d3892, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30704 p hg
    simpa only [d3892, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30706 (p : Pattern) (guard : d5847 p = 1) : d3893 p ≤ (0 : Int) + d3250 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30361 p hg
    simpa only [d3893, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30705 p hg
    simpa only [d3893, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30707 (p : Pattern) (guard : d5847 p = 1) : d3894 p ≤ (0 : Int) + d3251 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3894, d3251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30406 p hg
    simpa only [d3894, d3251, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3894, d3251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3894, d3251, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30708 (p : Pattern) (guard : d5847 p = 1) : d3895 p ≤ (0 : Int) + d3275 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3895, d3275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30706 p hg
    simpa only [d3895, d3275, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3895, d3275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30707 p hg
    simpa only [d3895, d3275, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30709 (p : Pattern) (guard : d5847 p = 1) : d3896 p ≤ (0 : Int) + d3306 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3896, d3306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30445 p hg
    simpa only [d3896, d3306, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3896, d3306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30708 p hg
    simpa only [d3896, d3306, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30710 (p : Pattern) (guard : d5847 p = 1) : d3897 p ≤ (0 : Int) + d3277 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3897, d3277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30689 p hg
    simpa only [d3897, d3277, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3897, d3277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30459 p hg
    simpa only [d3897, d3277, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30711 (p : Pattern) (guard : d5847 p = 1) : d3898 p ≤ (0 : Int) + d3307 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3898, d3307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30709 p hg
    simpa only [d3898, d3307, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3898, d3307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30710 p hg
    simpa only [d3898, d3307, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30712 (p : Pattern) (guard : d5847 p = 1) : d3899 p ≤ (0 : Int) + d3282 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3899, d3282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30689 p hg
    simpa only [d3899, d3282, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3899, d3282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30421 p hg
    simpa only [d3899, d3282, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30713 (p : Pattern) (guard : d5847 p = 1) : d3900 p ≤ (0 : Int) + d3285 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3900, d3285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30712 p hg
    simpa only [d3900, d3285, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3900, d3285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30425 p hg
    simpa only [d3900, d3285, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30714 (p : Pattern) (guard : d5847 p = 1) : d3901 p ≤ (0 : Int) + d3308 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3901, d3308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30711 p hg
    simpa only [d3901, d3308, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3901, d3308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30713 p hg
    simpa only [d3901, d3308, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30715 (p : Pattern) (guard : d5847 p = 1) : d3902 p ≤ (0 : Int) + d3451 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3902, d3451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30694 p hg
    simpa only [d3902, d3451, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3902, d3451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30390 p hg
    simpa only [d3902, d3451, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30716 (p : Pattern) (guard : d5847 p = 1) : d3903 p ≤ (0 : Int) + d3452 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3903, d3452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30697 p hg
    simpa only [d3903, d3452, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3903, d3452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30435 p hg
    simpa only [d3903, d3452, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30717 (p : Pattern) (guard : d5847 p = 1) : d3904 p ≤ (0 : Int) + d3453 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3904, d3453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30715 p hg
    simpa only [d3904, d3453, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3904, d3453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30716 p hg
    simpa only [d3904, d3453, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30718 (p : Pattern) (guard : d5847 p = 1) : d3905 p ≤ (0 : Int) + d3454 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3905, d3454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30697 p hg
    simpa only [d3905, d3454, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3905, d3454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3905, d3454, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30719 (p : Pattern) (guard : d5847 p = 1) : d3906 p ≤ (0 : Int) + d3455 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3906, d3455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30718 p hg
    simpa only [d3906, d3455, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3906, d3455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3906, d3455, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30720 (p : Pattern) (guard : d5847 p = 1) : d3907 p ≤ (0 : Int) + d3456 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3907, d3456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30717 p hg
    simpa only [d3907, d3456, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3907, d3456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30719 p hg
    simpa only [d3907, d3456, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30721 (p : Pattern) (guard : d5847 p = 1) : d3908 p ≤ (0 : Int) + d3457 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3908, d3457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30714 p hg
    simpa only [d3908, d3457, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3908, d3457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30720 p hg
    simpa only [d3908, d3457, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30722 (p : Pattern) (guard : d5847 p = 1) : d3909 p ≤ (0 : Int) + d3458 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3909, d3458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30703 p hg
    simpa only [d3909, d3458, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3909, d3458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30721 p hg
    simpa only [d3909, d3458, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30723 (p : Pattern) (guard : d5847 p = 1) : d3910 p ≤ (0 : Int) + d3226 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30311 p hg
    simpa only [d3910, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30448 p hg
    simpa only [d3910, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30724 (p : Pattern) (guard : d5847 p = 1) : d3911 p ≤ (0 : Int) + d3230 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3911, d3230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30442 p hg
    simpa only [d3911, d3230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3911, d3230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3911, d3230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30725 (p : Pattern) (guard : d5847 p = 1) : d3912 p ≤ (0 : Int) + d3238 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3912, d3238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30723 p hg
    simpa only [d3912, d3238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3912, d3238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30724 p hg
    simpa only [d3912, d3238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30726 (p : Pattern) (guard : d5847 p = 1) : d3913 p ≤ (0 : Int) + d3238 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30725 p hg
    simpa only [d3913, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30453 p hg
    simpa only [d3913, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30727 (p : Pattern) (guard : d5847 p = 1) : d3914 p ≤ (0 : Int) + d3459 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3914, d3459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30726 p hg
    simpa only [d3914, d3459, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3914, d3459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30466 p hg
    simpa only [d3914, d3459, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30728 (p : Pattern) (guard : d5847 p = 1) : d3915 p ≤ (0 : Int) + d3460 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3915, d3460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30727 p hg
    simpa only [d3915, d3460, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3915, d3460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30467 p hg
    simpa only [d3915, d3460, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30729 (p : Pattern) (guard : d5847 p = 1) : d190 p ≤ (0 : Int) + d3461 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23785 p hg
    simpa only [d5847, d3461, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17896 p hg
    simpa only [d5847, d3461, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30730 (p : Pattern) (guard : d5847 p = 1) : d3916 p ≤ (0 : Int) + d3461 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30729 p hg
    simpa only [d3916, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23786 p hg
    simpa only [d3916, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30731 (p : Pattern) (guard : d5847 p = 1) : d3917 p ≤ (0 : Int) + d3461 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30730 p hg
    simpa only [d3917, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23786 p hg
    simpa only [d3917, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30732 (p : Pattern) (guard : d5847 p = 1) : d3918 p ≤ (0 : Int) + d3461 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30729 p hg
    simpa only [d3918, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30731 p hg
    simpa only [d3918, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30733 (p : Pattern) (guard : d5847 p = 1) : d3919 p ≤ (0 : Int) + d3462 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3919, d3462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30731 p hg
    simpa only [d3919, d3462, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3919, d3462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3919, d3462, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30734 (p : Pattern) (guard : d5847 p = 1) : d3920 p ≤ (0 : Int) + d3463 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3920, d3463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30732 p hg
    simpa only [d3920, d3463, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3920, d3463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30733 p hg
    simpa only [d3920, d3463, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30735 (p : Pattern) (guard : d5847 p = 1) : d3921 p ≤ (0 : Int) + d3464 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3921, d3464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30455 p hg
    simpa only [d3921, d3464, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3921, d3464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30734 p hg
    simpa only [d3921, d3464, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30736 (p : Pattern) (guard : d5847 p = 1) : d3922 p ≤ (0 : Int) + d3465 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3922, d3465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30735 p hg
    simpa only [d3922, d3465, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3922, d3465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3922, d3465, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30737 (p : Pattern) (guard : d5847 p = 1) : d3923 p ≤ (0 : Int) + d3466 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3923, d3466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30736 p hg
    simpa only [d3923, d3466, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3923, d3466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3923, d3466, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30738 (p : Pattern) (guard : d5847 p = 1) : d3924 p ≤ (0 : Int) + d3467 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3924, d3467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30728 p hg
    simpa only [d3924, d3467, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3924, d3467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30737 p hg
    simpa only [d3924, d3467, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30739 (p : Pattern) (guard : d5847 p = 1) : d3925 p ≤ (0 : Int) + d3250 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3925, d3250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26355 p hg
    simpa only [d5847, d3925, d3250, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3925, d3250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17706 p hg
    simpa only [d5847, d3925, d3250, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30740 (p : Pattern) (guard : d5847 p = 1) : d3926 p ≤ (0 : Int) + d3250 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30364 p hg
    simpa only [d3926, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30739 p hg
    simpa only [d3926, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30741 (p : Pattern) (guard : d5847 p = 1) : d3927 p ≤ (0 : Int) + d3250 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30363 p hg
    simpa only [d3927, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30740 p hg
    simpa only [d3927, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30742 (p : Pattern) (guard : d5847 p = 1) : d3928 p ≤ (0 : Int) + d3251 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3928, d3251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30741 p hg
    simpa only [d3928, d3251, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3928, d3251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3928, d3251, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30743 (p : Pattern) (guard : d5847 p = 1) : d3929 p ≤ (0 : Int) + d3275 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3929, d3275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30428 p hg
    simpa only [d3929, d3275, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3929, d3275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30742 p hg
    simpa only [d3929, d3275, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30744 (p : Pattern) (guard : d5847 p = 1) : d3930 p ≤ (0 : Int) + d3275 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30743 p hg
    simpa only [d3930, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30463 p hg
    simpa only [d3930, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30745 (p : Pattern) (guard : d5847 p = 1) : d3931 p ≤ (0 : Int) + d3468 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3931, d3468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30455 p hg
    simpa only [d3931, d3468, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3931, d3468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30424 p hg
    simpa only [d3931, d3468, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30746 (p : Pattern) (guard : d5847 p = 1) : d3932 p ≤ (0 : Int) + d3469 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3932, d3469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30744 p hg
    simpa only [d3932, d3469, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3932, d3469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30745 p hg
    simpa only [d3932, d3469, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30747 (p : Pattern) (guard : d5847 p = 1) : d3933 p ≤ (0 : Int) + d3470 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3933, d3470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30746 p hg
    simpa only [d3933, d3470, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3933, d3470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30477 p hg
    simpa only [d3933, d3470, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30748 (p : Pattern) (guard : d5847 p = 1) : d3934 p ≤ (0 : Int) + d3471 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3934, d3471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30734 p hg
    simpa only [d3934, d3471, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3934, d3471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3934, d3471, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30749 (p : Pattern) (guard : d5847 p = 1) : d3935 p ≤ (0 : Int) + d3472 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3935, d3472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30748 p hg
    simpa only [d3935, d3472, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3935, d3472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3935, d3472, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30750 (p : Pattern) (guard : d5847 p = 1) : d3936 p ≤ (0 : Int) + d3473 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3936, d3473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30749 p hg
    simpa only [d3936, d3473, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3936, d3473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3936, d3473, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30751 (p : Pattern) (guard : d5847 p = 1) : d3937 p ≤ (0 : Int) + d3474 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3937, d3474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30747 p hg
    simpa only [d3937, d3474, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3937, d3474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30750 p hg
    simpa only [d3937, d3474, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30752 (p : Pattern) (guard : d5847 p = 1) : d3938 p ≤ (0 : Int) + d3475 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3938, d3475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30738 p hg
    simpa only [d3938, d3475, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3938, d3475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30751 p hg
    simpa only [d3938, d3475, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30753 (p : Pattern) (guard : d5847 p = 1) : d3939 p ≤ (0 : Int) + d3476 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3939, d3476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30722 p hg
    simpa only [d3939, d3476, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3939, d3476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30752 p hg
    simpa only [d3939, d3476, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30754 (p : Pattern) (guard : d5847 p = 1) : d3940 p ≤ (0 : Int) + d3477 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3940, d3477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30752 p hg
    simpa only [d3940, d3477, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3940, d3477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3940, d3477, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30755 (p : Pattern) (guard : d5847 p = 1) : d3941 p ≤ (0 : Int) + d3478 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3941, d3478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30753 p hg
    simpa only [d3941, d3478, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3941, d3478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30754 p hg
    simpa only [d3941, d3478, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30756 (p : Pattern) (guard : d5847 p = 1) : d3942 p ≤ (0 : Int) + d3479 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3942, d3479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30520 p hg
    simpa only [d3942, d3479, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3942, d3479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30755 p hg
    simpa only [d3942, d3479, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30757 (p : Pattern) (guard : d5847 p = 1) : d3943 p ≤ (0 : Int) + d3480 p := by
  cases selected : p 71 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3943, d3480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30504 p hg
    simpa only [d3943, d3480, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3943, d3480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30756 p hg
    simpa only [d3943, d3480, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30758 (p : Pattern) (guard : d5847 p = 1) : d3944 p ≤ (0 : Int) + d3481 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3944, d3481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30554 p hg
    simpa only [d3944, d3481, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3944, d3481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3944, d3481, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30759 (p : Pattern) (guard : d5847 p = 1) : d3945 p ≤ (0 : Int) + d3482 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3945, d3482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30611 p hg
    simpa only [d3945, d3482, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3945, d3482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30758 p hg
    simpa only [d3945, d3482, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30760 (p : Pattern) (guard : d5847 p = 1) : d3946 p ≤ (0 : Int) + d3483 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3946, d3483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30758 p hg
    simpa only [d3946, d3483, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3946, d3483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3946, d3483, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30761 (p : Pattern) (guard : d5847 p = 1) : d3947 p ≤ (0 : Int) + d3484 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3947, d3484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30759 p hg
    simpa only [d3947, d3484, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3947, d3484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30760 p hg
    simpa only [d3947, d3484, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30762 (p : Pattern) (guard : d5847 p = 1) : d3948 p ≤ (0 : Int) + d3485 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3948, d3485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30591 p hg
    simpa only [d3948, d3485, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3948, d3485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3948, d3485, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30763 (p : Pattern) (guard : d5847 p = 1) : d3949 p ≤ (0 : Int) + d3486 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3949, d3486, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30619 p hg
    simpa only [d3949, d3486, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3949, d3486, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30762 p hg
    simpa only [d3949, d3486, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30764 (p : Pattern) (guard : d5847 p = 1) : d3950 p ≤ (0 : Int) + d3487 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3950, d3487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30762 p hg
    simpa only [d3950, d3487, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3950, d3487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3950, d3487, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30765 (p : Pattern) (guard : d5847 p = 1) : d3951 p ≤ (0 : Int) + d3488 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3951, d3488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30763 p hg
    simpa only [d3951, d3488, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3951, d3488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30764 p hg
    simpa only [d3951, d3488, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30766 (p : Pattern) (guard : d5847 p = 1) : d3952 p ≤ (0 : Int) + d3489 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3952, d3489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30761 p hg
    simpa only [d3952, d3489, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3952, d3489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30765 p hg
    simpa only [d3952, d3489, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30767 (p : Pattern) (guard : d5847 p = 1) : d3953 p ≤ (0 : Int) + d3490 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3953, d3490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30597 p hg
    simpa only [d3953, d3490, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3953, d3490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30766 p hg
    simpa only [d3953, d3490, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30768 (p : Pattern) (guard : d5847 p = 1) : d3954 p ≤ (0 : Int) + d3481 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3954, d3481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30641 p hg
    simpa only [d3954, d3481, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3954, d3481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3954, d3481, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30769 (p : Pattern) (guard : d5847 p = 1) : d3955 p ≤ (0 : Int) + d3491 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3955, d3491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30653 p hg
    simpa only [d3955, d3491, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3955, d3491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30768 p hg
    simpa only [d3955, d3491, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30770 (p : Pattern) (guard : d5847 p = 1) : d3956 p ≤ (0 : Int) + d3483 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3956, d3483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30768 p hg
    simpa only [d3956, d3483, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3956, d3483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3956, d3483, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30771 (p : Pattern) (guard : d5847 p = 1) : d3957 p ≤ (0 : Int) + d3492 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3957, d3492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30769 p hg
    simpa only [d3957, d3492, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3957, d3492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30770 p hg
    simpa only [d3957, d3492, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30772 (p : Pattern) (guard : d5847 p = 1) : d3958 p ≤ (0 : Int) + d3493 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3958, d3493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30771 p hg
    simpa only [d3958, d3493, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3958, d3493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30661 p hg
    simpa only [d3958, d3493, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30773 (p : Pattern) (guard : d5847 p = 1) : d3959 p ≤ (0 : Int) + d3494 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3959, d3494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30652 p hg
    simpa only [d3959, d3494, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3959, d3494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30772 p hg
    simpa only [d3959, d3494, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30774 (p : Pattern) (guard : d5847 p = 1) : d3960 p ≤ (0 : Int) + d3495 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3960, d3495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30767 p hg
    simpa only [d3960, d3495, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3960, d3495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30773 p hg
    simpa only [d3960, d3495, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30775 (p : Pattern) (guard : d5847 p = 1) : d3961 p ≤ (0 : Int) + d3496 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3961, d3496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30773 p hg
    simpa only [d3961, d3496, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3961, d3496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30668 p hg
    simpa only [d3961, d3496, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30776 (p : Pattern) (guard : d5847 p = 1) : d3962 p ≤ (0 : Int) + d3497 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3962, d3497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30774 p hg
    simpa only [d3962, d3497, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3962, d3497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30775 p hg
    simpa only [d3962, d3497, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30777 (p : Pattern) (guard : d5847 p = 1) : d3963 p ≤ (0 : Int) + d3358 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30530 p hg
    simpa only [d3963, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30634 p hg
    simpa only [d3963, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30778 (p : Pattern) (guard : d5847 p = 1) : d3964 p ≤ (0 : Int) + d3362 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3964, d3362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30628 p hg
    simpa only [d3964, d3362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3964, d3362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3964, d3362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30779 (p : Pattern) (guard : d5847 p = 1) : d3965 p ≤ (0 : Int) + d3364 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3965, d3364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30777 p hg
    simpa only [d3965, d3364, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3965, d3364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30778 p hg
    simpa only [d3965, d3364, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30780 (p : Pattern) (guard : d5847 p = 1) : d3966 p ≤ (0 : Int) + d3369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3966, d3369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30779 p hg
    simpa only [d3966, d3369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3966, d3369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30641 p hg
    simpa only [d3966, d3369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30781 (p : Pattern) (guard : d5847 p = 1) : d3967 p ≤ (0 : Int) + d3410 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3967, d3410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30631 p hg
    simpa only [d3967, d3410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3967, d3410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30780 p hg
    simpa only [d3967, d3410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30782 (p : Pattern) (guard : d5847 p = 1) : d3968 p ≤ (0 : Int) + d3369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3968, d3369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30636 p hg
    simpa only [d3968, d3369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3968, d3369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30641 p hg
    simpa only [d3968, d3369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30783 (p : Pattern) (guard : d5847 p = 1) : d3969 p ≤ (0 : Int) + d3372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3969, d3372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30782 p hg
    simpa only [d3969, d3372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3969, d3372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30557 p hg
    simpa only [d3969, d3372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30784 (p : Pattern) (guard : d5847 p = 1) : d3970 p ≤ (0 : Int) + d3411 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3970, d3411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30781 p hg
    simpa only [d3970, d3411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3970, d3411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30783 p hg
    simpa only [d3970, d3411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30785 (p : Pattern) (guard : d5847 p = 1) : d3971 p ≤ (0 : Int) + d3498 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3971, d3498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30617 p hg
    simpa only [d3971, d3498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3971, d3498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30581 p hg
    simpa only [d3971, d3498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30786 (p : Pattern) (guard : d5847 p = 1) : d3972 p ≤ (0 : Int) + d3499 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3972, d3499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30646 p hg
    simpa only [d3972, d3499, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3972, d3499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30785 p hg
    simpa only [d3972, d3499, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30787 (p : Pattern) (guard : d5847 p = 1) : d3973 p ≤ (0 : Int) + d3500 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3973, d3500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30786 p hg
    simpa only [d3973, d3500, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3973, d3500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30762 p hg
    simpa only [d3973, d3500, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30788 (p : Pattern) (guard : d5847 p = 1) : d3974 p ≤ (0 : Int) + d3501 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3974, d3501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30647 p hg
    simpa only [d3974, d3501, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3974, d3501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3974, d3501, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30789 (p : Pattern) (guard : d5847 p = 1) : d3975 p ≤ (0 : Int) + d3502 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3975, d3502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30788 p hg
    simpa only [d3975, d3502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3975, d3502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3975, d3502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30790 (p : Pattern) (guard : d5847 p = 1) : d3976 p ≤ (0 : Int) + d3503 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3976, d3503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30789 p hg
    simpa only [d3976, d3503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3976, d3503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3976, d3503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30791 (p : Pattern) (guard : d5847 p = 1) : d3977 p ≤ (0 : Int) + d3504 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3977, d3504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30787 p hg
    simpa only [d3977, d3504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3977, d3504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30790 p hg
    simpa only [d3977, d3504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30792 (p : Pattern) (guard : d5847 p = 1) : d3978 p ≤ (0 : Int) + d3505 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3978, d3505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30784 p hg
    simpa only [d3978, d3505, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3978, d3505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30791 p hg
    simpa only [d3978, d3505, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30793 (p : Pattern) (guard : d5847 p = 1) : d3979 p ≤ (0 : Int) + d3374 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30569 p hg
    simpa only [d3979, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30567 p hg
    simpa only [d3979, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30794 (p : Pattern) (guard : d5847 p = 1) : d3980 p ≤ (0 : Int) + d3374 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3980, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30568 p hg
    simpa only [d3980, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3980, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30793 p hg
    simpa only [d3980, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30795 (p : Pattern) (guard : d5847 p = 1) : d3981 p ≤ (0 : Int) + d3374 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30566 p hg
    simpa only [d3981, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30794 p hg
    simpa only [d3981, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30796 (p : Pattern) (guard : d5847 p = 1) : d3982 p ≤ (0 : Int) + d3375 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3982, d3375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30604 p hg
    simpa only [d3982, d3375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3982, d3375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3982, d3375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30797 (p : Pattern) (guard : d5847 p = 1) : d3983 p ≤ (0 : Int) + d3394 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3983, d3394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30795 p hg
    simpa only [d3983, d3394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3983, d3394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30796 p hg
    simpa only [d3983, d3394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30798 (p : Pattern) (guard : d5847 p = 1) : d3984 p ≤ (0 : Int) + d3417 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3984, d3417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30779 p hg
    simpa only [d3984, d3417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3984, d3417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30797 p hg
    simpa only [d3984, d3417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30799 (p : Pattern) (guard : d5847 p = 1) : d3985 p ≤ (0 : Int) + d3366 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30546 p hg
    simpa only [d3985, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30585 p hg
    simpa only [d3985, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
