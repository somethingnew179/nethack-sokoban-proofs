/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons196
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare27580 (p : Pattern) (guard : d5847 p = 1) : d3374 p ≤ (0 : Int) + d3768 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27578 p hg
    simpa only [d3768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27579 p hg
    simpa only [d3768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27581 (p : Pattern) (guard : d5847 p = 1) : d3374 p ≤ (0 : Int) + d3769 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3374, d3769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20197 p hg
    simpa only [d5847, d3374, d3769, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3374, d3769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20290 p hg
    simpa only [d5847, d3374, d3769, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27582 (p : Pattern) (guard : d5847 p = 1) : d3374 p ≤ (0 : Int) + d1896 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3374, d1896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20197 p hg
    simpa only [d5847, d3374, d1896, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3374, d1896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5847, d3374, d1896, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27583 (p : Pattern) (guard : d5847 p = 1) : d3374 p ≤ (0 : Int) + d3770 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27581 p hg
    simpa only [d3770, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27582 p hg
    simpa only [d3770, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27584 (p : Pattern) (guard : d5847 p = 1) : d3374 p ≤ (0 : Int) + d3771 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27580 p hg
    simpa only [d3771, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27583 p hg
    simpa only [d3771, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27585 (p : Pattern) (guard : d5847 p = 1) : d3375 p ≤ (0 : Int) + d3772 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3375, d3772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27584 p hg
    simpa only [d3375, d3772, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3375, d3772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3375, d3772, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27586 (p : Pattern) (guard : d5847 p = 1) : d3376 p ≤ (0 : Int) + d3773 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3376, d3773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27577 p hg
    simpa only [d3376, d3773, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3376, d3773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27585 p hg
    simpa only [d3376, d3773, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27587 (p : Pattern) (guard : d5847 p = 1) : d3377 p ≤ (0 : Int) + d119 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20208 p hg
    simpa only [d5847, d3377, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20290 p hg
    simpa only [d5847, d3377, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27588 (p : Pattern) (guard : d5847 p = 1) : d3377 p ≤ (0 : Int) + d317 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3377, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20208 p hg
    simpa only [d5847, d3377, d317, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3377, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5847, d3377, d317, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27589 (p : Pattern) (guard : d5847 p = 1) : d3377 p ≤ (0 : Int) + d3774 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27587 p hg
    simpa only [d3774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27588 p hg
    simpa only [d3774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27590 (p : Pattern) (guard : d5847 p = 1) : d3377 p ≤ (0 : Int) + d3775 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3377, d3775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20208 p hg
    simpa only [d5847, d3377, d3775, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3377, d3775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20007 p hg
    simpa only [d5847, d3377, d3775, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27591 (p : Pattern) (guard : d5847 p = 1) : d3377 p ≤ (0 : Int) + d3776 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27590 p hg
    simpa only [d3776, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27588 p hg
    simpa only [d3776, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27592 (p : Pattern) (guard : d5847 p = 1) : d3377 p ≤ (0 : Int) + d3777 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27589 p hg
    simpa only [d3777, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27591 p hg
    simpa only [d3777, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27593 (p : Pattern) (guard : d5847 p = 1) : d3378 p ≤ (0 : Int) + d3778 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3378, d3778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27592 p hg
    simpa only [d3378, d3778, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3378, d3778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3378, d3778, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27594 (p : Pattern) (guard : d5847 p = 1) : d3379 p ≤ (0 : Int) + d3779 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3379, d3779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27577 p hg
    simpa only [d3379, d3779, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3379, d3779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27593 p hg
    simpa only [d3379, d3779, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27595 (p : Pattern) (guard : d5847 p = 1) : d3380 p ≤ (0 : Int) + d3780 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3380, d3780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27586 p hg
    simpa only [d3380, d3780, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3380, d3780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27594 p hg
    simpa only [d3380, d3780, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27596 (p : Pattern) (guard : d5847 p = 1) : d3381 p ≤ (0 : Int) + d3781 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3381, d3781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27577 p hg
    simpa only [d3381, d3781, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3381, d3781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3381, d3781, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27597 (p : Pattern) (guard : d5847 p = 1) : d3366 p ≤ (0 : Int) + d3782 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3366, d3782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20165 p hg
    simpa only [d5847, d3366, d3782, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3366, d3782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20007 p hg
    simpa only [d5847, d3366, d3782, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27598 (p : Pattern) (guard : d5847 p = 1) : d3366 p ≤ (0 : Int) + d3783 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27557 p hg
    simpa only [d3783, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27597 p hg
    simpa only [d3783, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27599 (p : Pattern) (guard : d5847 p = 1) : d3366 p ≤ (0 : Int) + d348 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3366, d348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20165 p hg
    simpa only [d5847, d3366, d348, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3366, d348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5847, d3366, d348, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27600 (p : Pattern) (guard : d5847 p = 1) : d3366 p ≤ (0 : Int) + d3784 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27558 p hg
    simpa only [d3784, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27599 p hg
    simpa only [d3784, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27601 (p : Pattern) (guard : d5847 p = 1) : d3366 p ≤ (0 : Int) + d3785 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27598 p hg
    simpa only [d3785, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27600 p hg
    simpa only [d3785, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27602 (p : Pattern) (guard : d5847 p = 1) : d3366 p ≤ (0 : Int) + d3786 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27557 p hg
    simpa only [d3786, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27601 p hg
    simpa only [d3786, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27603 (p : Pattern) (guard : d5847 p = 1) : d3382 p ≤ (0 : Int) + d3787 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3382, d3787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27602 p hg
    simpa only [d3382, d3787, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3382, d3787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3382, d3787, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27604 (p : Pattern) (guard : d5847 p = 1) : d3383 p ≤ (0 : Int) + d3788 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3383, d3788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27596 p hg
    simpa only [d3383, d3788, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3383, d3788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27603 p hg
    simpa only [d3383, d3788, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27605 (p : Pattern) (guard : d5847 p = 1) : d3384 p ≤ (0 : Int) + d3789 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3384, d3789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27595 p hg
    simpa only [d3384, d3789, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3384, d3789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27604 p hg
    simpa only [d3384, d3789, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27606 (p : Pattern) (guard : d5847 p = 1) : d3385 p ≤ (0 : Int) + d3790 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3385, d3790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27445 p hg
    simpa only [d3385, d3790, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3385, d3790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3385, d3790, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27607 (p : Pattern) (guard : d5847 p = 1) : d3386 p ≤ (0 : Int) + d3791 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3386, d3791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27604 p hg
    simpa only [d3386, d3791, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3386, d3791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27606 p hg
    simpa only [d3386, d3791, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27608 (p : Pattern) (guard : d5847 p = 1) : d3387 p ≤ (0 : Int) + d3792 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3387, d3792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27605 p hg
    simpa only [d3387, d3792, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3387, d3792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27607 p hg
    simpa only [d3387, d3792, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27609 (p : Pattern) (guard : d5847 p = 1) : d3388 p ≤ (0 : Int) + d3793 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3388, d3793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27571 p hg
    simpa only [d3388, d3793, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3388, d3793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27608 p hg
    simpa only [d3388, d3793, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27610 (p : Pattern) (guard : d5847 p = 1) : d3389 p ≤ (0 : Int) + d102 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20135 p hg
    simpa only [d5847, d3389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26814 p hg
    simpa only [d5847, d3389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27611 (p : Pattern) (guard : d5847 p = 1) : d3390 p ≤ (0 : Int) + d102 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27610 p hg
    simpa only [d3390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27542 p hg
    simpa only [d3390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27612 (p : Pattern) (guard : d5847 p = 1) : d3391 p ≤ (0 : Int) + d102 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27611 p hg
    simpa only [d3391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27542 p hg
    simpa only [d3391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27613 (p : Pattern) (guard : d5847 p = 1) : d3392 p ≤ (0 : Int) + d3745 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3392, d3745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27612 p hg
    simpa only [d3392, d3745, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3392, d3745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27547 p hg
    simpa only [d3392, d3745, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27614 (p : Pattern) (guard : d5847 p = 1) : d3393 p ≤ (0 : Int) + d3746 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3393, d3746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27613 p hg
    simpa only [d3393, d3746, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3393, d3746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27552 p hg
    simpa only [d3393, d3746, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27615 (p : Pattern) (guard : d5847 p = 1) : d3374 p ≤ (0 : Int) + d3794 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27578 p hg
    simpa only [d3794, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27581 p hg
    simpa only [d3794, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27616 (p : Pattern) (guard : d5847 p = 1) : d3374 p ≤ (0 : Int) + d3795 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27615 p hg
    simpa only [d3795, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27581 p hg
    simpa only [d3795, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27617 (p : Pattern) (guard : d5847 p = 1) : d3374 p ≤ (0 : Int) + d3796 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27578 p hg
    simpa only [d3796, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27616 p hg
    simpa only [d3796, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27618 (p : Pattern) (guard : d5847 p = 1) : d3374 p ≤ (0 : Int) + d3797 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3374, d3797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20197 p hg
    simpa only [d5847, d3374, d3797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3374, d3797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20170 p hg
    simpa only [d5847, d3374, d3797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27619 (p : Pattern) (guard : d5847 p = 1) : d3374 p ≤ (0 : Int) + d3798 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27578 p hg
    simpa only [d3798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27618 p hg
    simpa only [d3798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27620 (p : Pattern) (guard : d5847 p = 1) : d3374 p ≤ (0 : Int) + d3799 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27619 p hg
    simpa only [d3799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27618 p hg
    simpa only [d3799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27621 (p : Pattern) (guard : d5847 p = 1) : d3375 p ≤ (0 : Int) + d3800 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3375, d3800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27620 p hg
    simpa only [d3375, d3800, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3375, d3800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3375, d3800, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27622 (p : Pattern) (guard : d5847 p = 1) : d3394 p ≤ (0 : Int) + d3801 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3394, d3801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27617 p hg
    simpa only [d3394, d3801, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3394, d3801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27621 p hg
    simpa only [d3394, d3801, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27623 (p : Pattern) (guard : d5847 p = 1) : d3395 p ≤ (0 : Int) + d3802 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3395, d3802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27614 p hg
    simpa only [d3395, d3802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3395, d3802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27622 p hg
    simpa only [d3395, d3802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27624 (p : Pattern) (guard : d5847 p = 1) : d3396 p ≤ (0 : Int) + d3803 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3396, d3803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27566 p hg
    simpa only [d3396, d3803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3396, d3803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27433 p hg
    simpa only [d3396, d3803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27625 (p : Pattern) (guard : d5847 p = 1) : d3397 p ≤ (0 : Int) + d3804 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3397, d3804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27623 p hg
    simpa only [d3397, d3804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3397, d3804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27624 p hg
    simpa only [d3397, d3804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27626 (p : Pattern) (guard : d5847 p = 1) : d3398 p ≤ (0 : Int) + d3805 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3398, d3805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27566 p hg
    simpa only [d3398, d3805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3398, d3805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27436 p hg
    simpa only [d3398, d3805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27627 (p : Pattern) (guard : d5847 p = 1) : d3399 p ≤ (0 : Int) + d3806 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3399, d3806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27626 p hg
    simpa only [d3399, d3806, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3399, d3806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3399, d3806, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27628 (p : Pattern) (guard : d5847 p = 1) : d3400 p ≤ (0 : Int) + d3807 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3400, d3807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27625 p hg
    simpa only [d3400, d3807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3400, d3807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27627 p hg
    simpa only [d3400, d3807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27629 (p : Pattern) (guard : d5847 p = 1) : d3374 p ≤ (0 : Int) + d3808 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27578 p hg
    simpa only [d3808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27584 p hg
    simpa only [d3808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27630 (p : Pattern) (guard : d5847 p = 1) : d3401 p ≤ (0 : Int) + d3809 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3401, d3809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27629 p hg
    simpa only [d3401, d3809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3401, d3809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3401, d3809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27631 (p : Pattern) (guard : d5847 p = 1) : d3402 p ≤ (0 : Int) + d3810 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3402, d3810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27594 p hg
    simpa only [d3402, d3810, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3402, d3810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27630 p hg
    simpa only [d3402, d3810, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27632 (p : Pattern) (guard : d5847 p = 1) : d3403 p ≤ (0 : Int) + d3811 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3403, d3811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27603 p hg
    simpa only [d3403, d3811, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3403, d3811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27445 p hg
    simpa only [d3403, d3811, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27633 (p : Pattern) (guard : d5847 p = 1) : d3404 p ≤ (0 : Int) + d3812 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3404, d3812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27631 p hg
    simpa only [d3404, d3812, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3404, d3812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27632 p hg
    simpa only [d3404, d3812, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27634 (p : Pattern) (guard : d5847 p = 1) : d3405 p ≤ (0 : Int) + d3813 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3405, d3813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27603 p hg
    simpa only [d3405, d3813, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3405, d3813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27447 p hg
    simpa only [d3405, d3813, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27635 (p : Pattern) (guard : d5847 p = 1) : d3406 p ≤ (0 : Int) + d3814 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3406, d3814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27634 p hg
    simpa only [d3406, d3814, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3406, d3814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3406, d3814, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27636 (p : Pattern) (guard : d5847 p = 1) : d3407 p ≤ (0 : Int) + d3815 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3407, d3815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27633 p hg
    simpa only [d3407, d3815, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3407, d3815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27635 p hg
    simpa only [d3407, d3815, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27637 (p : Pattern) (guard : d5847 p = 1) : d3408 p ≤ (0 : Int) + d3816 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3408, d3816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27628 p hg
    simpa only [d3408, d3816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3408, d3816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27636 p hg
    simpa only [d3408, d3816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27638 (p : Pattern) (guard : d5847 p = 1) : d3409 p ≤ (0 : Int) + d3817 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3409, d3817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27609 p hg
    simpa only [d3409, d3817, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3409, d3817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27637 p hg
    simpa only [d3409, d3817, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27639 (p : Pattern) (guard : d5847 p = 1) : d3358 p ≤ (0 : Int) + d3818 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27545 p hg
    simpa only [d3818, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27572 p hg
    simpa only [d3818, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27640 (p : Pattern) (guard : d5847 p = 1) : d3358 p ≤ (0 : Int) + d3819 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27573 p hg
    simpa only [d3819, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27639 p hg
    simpa only [d3819, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27641 (p : Pattern) (guard : d5847 p = 1) : d3358 p ≤ (0 : Int) + d3820 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27542 p hg
    simpa only [d3820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27640 p hg
    simpa only [d3820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27642 (p : Pattern) (guard : d5847 p = 1) : d3362 p ≤ (0 : Int) + d3821 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3362, d3821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27547 p hg
    simpa only [d3362, d3821, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3362, d3821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3362, d3821, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27643 (p : Pattern) (guard : d5847 p = 1) : d3364 p ≤ (0 : Int) + d3822 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3364, d3822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27641 p hg
    simpa only [d3364, d3822, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3364, d3822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27642 p hg
    simpa only [d3364, d3822, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27644 (p : Pattern) (guard : d5847 p = 1) : d3358 p ≤ (0 : Int) + d3823 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3358, d3823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20135 p hg
    simpa only [d5847, d3358, d3823, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3358, d3823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19893 p hg
    simpa only [d5847, d3358, d3823, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27645 (p : Pattern) (guard : d5847 p = 1) : d3358 p ≤ (0 : Int) + d3824 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27545 p hg
    simpa only [d3824, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27644 p hg
    simpa only [d3824, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27646 (p : Pattern) (guard : d5847 p = 1) : d3358 p ≤ (0 : Int) + d3825 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27573 p hg
    simpa only [d3825, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27645 p hg
    simpa only [d3825, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27647 (p : Pattern) (guard : d5847 p = 1) : d3362 p ≤ (0 : Int) + d3826 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3362, d3826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27646 p hg
    simpa only [d3362, d3826, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3362, d3826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3362, d3826, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27648 (p : Pattern) (guard : d5847 p = 1) : d3364 p ≤ (0 : Int) + d3827 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3364, d3827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27577 p hg
    simpa only [d3364, d3827, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3364, d3827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27647 p hg
    simpa only [d3364, d3827, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27649 (p : Pattern) (guard : d5847 p = 1) : d3364 p ≤ (0 : Int) + d3828 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27643 p hg
    simpa only [d3828, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27648 p hg
    simpa only [d3828, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27650 (p : Pattern) (guard : d5847 p = 1) : d3362 p ≤ (0 : Int) + d3829 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3362, d3829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27576 p hg
    simpa only [d3362, d3829, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3362, d3829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3362, d3829, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27651 (p : Pattern) (guard : d5847 p = 1) : d3364 p ≤ (0 : Int) + d3830 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3364, d3830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27577 p hg
    simpa only [d3364, d3830, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3364, d3830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27650 p hg
    simpa only [d3364, d3830, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27652 (p : Pattern) (guard : d5847 p = 1) : d3367 p ≤ (0 : Int) + d3831 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3367, d3831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27601 p hg
    simpa only [d3367, d3831, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3367, d3831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3367, d3831, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27653 (p : Pattern) (guard : d5847 p = 1) : d3368 p ≤ (0 : Int) + d3832 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3368, d3832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27602 p hg
    simpa only [d3368, d3832, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3368, d3832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27652 p hg
    simpa only [d3368, d3832, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27654 (p : Pattern) (guard : d5847 p = 1) : d3369 p ≤ (0 : Int) + d3833 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3369, d3833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27651 p hg
    simpa only [d3369, d3833, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3369, d3833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27653 p hg
    simpa only [d3369, d3833, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27655 (p : Pattern) (guard : d5847 p = 1) : d3410 p ≤ (0 : Int) + d3834 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3410, d3834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27649 p hg
    simpa only [d3410, d3834, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3410, d3834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27654 p hg
    simpa only [d3410, d3834, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27656 (p : Pattern) (guard : d5847 p = 1) : d3372 p ≤ (0 : Int) + d3835 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3372, d3835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27654 p hg
    simpa only [d3372, d3835, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3372, d3835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27569 p hg
    simpa only [d3372, d3835, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27657 (p : Pattern) (guard : d5847 p = 1) : d3411 p ≤ (0 : Int) + d3836 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3411, d3836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27655 p hg
    simpa only [d3411, d3836, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3411, d3836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27656 p hg
    simpa only [d3411, d3836, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27658 (p : Pattern) (guard : d5847 p = 1) : d3394 p ≤ (0 : Int) + d3837 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3394, d3837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27629 p hg
    simpa only [d3394, d3837, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3394, d3837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27585 p hg
    simpa only [d3394, d3837, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27659 (p : Pattern) (guard : d5847 p = 1) : d3377 p ≤ (0 : Int) + d3838 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27587 p hg
    simpa only [d3838, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27592 p hg
    simpa only [d3838, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27660 (p : Pattern) (guard : d5847 p = 1) : d3412 p ≤ (0 : Int) + d3839 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3412, d3839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27659 p hg
    simpa only [d3412, d3839, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3412, d3839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27593 p hg
    simpa only [d3412, d3839, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27661 (p : Pattern) (guard : d5847 p = 1) : d3413 p ≤ (0 : Int) + d3840 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3413, d3840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27658 p hg
    simpa only [d3413, d3840, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3413, d3840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27660 p hg
    simpa only [d3413, d3840, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27662 (p : Pattern) (guard : d5847 p = 1) : d3414 p ≤ (0 : Int) + d3841 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3414, d3841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27661 p hg
    simpa only [d3414, d3841, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3414, d3841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3414, d3841, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27663 (p : Pattern) (guard : d5847 p = 1) : d3415 p ≤ (0 : Int) + d3842 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3415, d3842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27662 p hg
    simpa only [d3415, d3842, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3415, d3842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3415, d3842, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27664 (p : Pattern) (guard : d5847 p = 1) : d3416 p ≤ (0 : Int) + d3843 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3416, d3843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27657 p hg
    simpa only [d3416, d3843, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3416, d3843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27663 p hg
    simpa only [d3416, d3843, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27665 (p : Pattern) (guard : d5847 p = 1) : d3417 p ≤ (0 : Int) + d3844 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3417, d3844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27648 p hg
    simpa only [d3417, d3844, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3417, d3844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27658 p hg
    simpa only [d3417, d3844, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27666 (p : Pattern) (guard : d5847 p = 1) : d3396 p ≤ (0 : Int) + d3845 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3396, d3845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27653 p hg
    simpa only [d3396, d3845, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3396, d3845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27433 p hg
    simpa only [d3396, d3845, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27667 (p : Pattern) (guard : d5847 p = 1) : d3418 p ≤ (0 : Int) + d3846 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3418, d3846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27665 p hg
    simpa only [d3418, d3846, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3418, d3846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27666 p hg
    simpa only [d3418, d3846, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27668 (p : Pattern) (guard : d5847 p = 1) : d3398 p ≤ (0 : Int) + d3847 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3398, d3847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27653 p hg
    simpa only [d3398, d3847, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3398, d3847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27436 p hg
    simpa only [d3398, d3847, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27669 (p : Pattern) (guard : d5847 p = 1) : d3399 p ≤ (0 : Int) + d3848 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3399, d3848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27668 p hg
    simpa only [d3399, d3848, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3399, d3848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3399, d3848, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27670 (p : Pattern) (guard : d5847 p = 1) : d3419 p ≤ (0 : Int) + d3849 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3419, d3849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27667 p hg
    simpa only [d3419, d3849, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3419, d3849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27669 p hg
    simpa only [d3419, d3849, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27671 (p : Pattern) (guard : d5847 p = 1) : d3420 p ≤ (0 : Int) + d3850 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3420, d3850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27660 p hg
    simpa only [d3420, d3850, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3420, d3850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3420, d3850, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27672 (p : Pattern) (guard : d5847 p = 1) : d3421 p ≤ (0 : Int) + d3851 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3421, d3851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27671 p hg
    simpa only [d3421, d3851, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3421, d3851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3421, d3851, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27673 (p : Pattern) (guard : d5847 p = 1) : d3422 p ≤ (0 : Int) + d3852 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3422, d3852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27672 p hg
    simpa only [d3422, d3852, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3422, d3852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3422, d3852, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27674 (p : Pattern) (guard : d5847 p = 1) : d3423 p ≤ (0 : Int) + d3853 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3423, d3853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27670 p hg
    simpa only [d3423, d3853, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3423, d3853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27673 p hg
    simpa only [d3423, d3853, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27675 (p : Pattern) (guard : d5847 p = 1) : d3424 p ≤ (0 : Int) + d3854 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3424, d3854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27664 p hg
    simpa only [d3424, d3854, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3424, d3854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27674 p hg
    simpa only [d3424, d3854, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27676 (p : Pattern) (guard : d5847 p = 1) : d3425 p ≤ (0 : Int) + d3855 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3425, d3855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27638 p hg
    simpa only [d3425, d3855, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3425, d3855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27675 p hg
    simpa only [d3425, d3855, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27677 (p : Pattern) (guard : d5847 p = 1) : d3426 p ≤ (0 : Int) + d3856 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3426, d3856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27569 p hg
    simpa only [d3426, d3856, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3426, d3856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3426, d3856, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27678 (p : Pattern) (guard : d5847 p = 1) : d3427 p ≤ (0 : Int) + d3857 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3427, d3857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27677 p hg
    simpa only [d3427, d3857, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3427, d3857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3427, d3857, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27679 (p : Pattern) (guard : d5847 p = 1) : d3428 p ≤ (0 : Int) + d3858 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3428, d3858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27678 p hg
    simpa only [d3428, d3858, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3428, d3858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3428, d3858, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27680 (p : Pattern) (guard : d5847 p = 1) : d3429 p ≤ (0 : Int) + d3859 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3429, d3859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27679 p hg
    simpa only [d3429, d3859, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3429, d3859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3429, d3859, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27681 (p : Pattern) (guard : d5847 p = 1) : d3430 p ≤ (0 : Int) + d3860 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3430, d3860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27675 p hg
    simpa only [d3430, d3860, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3430, d3860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27680 p hg
    simpa only [d3430, d3860, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27682 (p : Pattern) (guard : d5847 p = 1) : d3431 p ≤ (0 : Int) + d3861 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3431, d3861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27676 p hg
    simpa only [d3431, d3861, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3431, d3861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27681 p hg
    simpa only [d3431, d3861, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27683 (p : Pattern) (guard : d5847 p = 1) : d3410 p ≤ (0 : Int) + d3862 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3410, d3862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27555 p hg
    simpa only [d3410, d3862, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3410, d3862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27567 p hg
    simpa only [d3410, d3862, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27684 (p : Pattern) (guard : d5847 p = 1) : d3411 p ≤ (0 : Int) + d3863 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3411, d3863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27683 p hg
    simpa only [d3411, d3863, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3411, d3863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27570 p hg
    simpa only [d3411, d3863, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27685 (p : Pattern) (guard : d5847 p = 1) : d3432 p ≤ (0 : Int) + d3864 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3432, d3864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27684 p hg
    simpa only [d3432, d3864, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3432, d3864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27608 p hg
    simpa only [d3432, d3864, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27686 (p : Pattern) (guard : d5847 p = 1) : d3417 p ≤ (0 : Int) + d3802 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3417, d3802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27555 p hg
    simpa only [d3417, d3802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3417, d3802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27622 p hg
    simpa only [d3417, d3802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27687 (p : Pattern) (guard : d5847 p = 1) : d3418 p ≤ (0 : Int) + d3804 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3418, d3804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27686 p hg
    simpa only [d3418, d3804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3418, d3804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27624 p hg
    simpa only [d3418, d3804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27688 (p : Pattern) (guard : d5847 p = 1) : d3419 p ≤ (0 : Int) + d3807 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3419, d3807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27687 p hg
    simpa only [d3419, d3807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3419, d3807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27627 p hg
    simpa only [d3419, d3807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27689 (p : Pattern) (guard : d5847 p = 1) : d3433 p ≤ (0 : Int) + d3816 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3433, d3816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27688 p hg
    simpa only [d3433, d3816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3433, d3816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27636 p hg
    simpa only [d3433, d3816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27690 (p : Pattern) (guard : d5847 p = 1) : d3434 p ≤ (0 : Int) + d3865 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3434, d3865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27685 p hg
    simpa only [d3434, d3865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3434, d3865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27689 p hg
    simpa only [d3434, d3865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27691 (p : Pattern) (guard : d5847 p = 1) : d3435 p ≤ (0 : Int) + d3866 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3435, d3866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27690 p hg
    simpa only [d3435, d3866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3435, d3866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27675 p hg
    simpa only [d3435, d3866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27692 (p : Pattern) (guard : d5847 p = 1) : d3436 p ≤ (0 : Int) + d3867 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3436, d3867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27675 p hg
    simpa only [d3436, d3867, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3436, d3867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3436, d3867, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27693 (p : Pattern) (guard : d5847 p = 1) : d3437 p ≤ (0 : Int) + d3868 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3437, d3868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27691 p hg
    simpa only [d3437, d3868, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3437, d3868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27692 p hg
    simpa only [d3437, d3868, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27694 (p : Pattern) (guard : d5847 p = 1) : d3438 p ≤ (0 : Int) + d3869 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3438, d3869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27682 p hg
    simpa only [d3438, d3869, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3438, d3869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27693 p hg
    simpa only [d3438, d3869, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27695 (p : Pattern) (guard : d5847 p = 1) : d3439 p ≤ (0 : Int) + d3870 p := by
  cases selected : p 71 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3439, d3870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27516 p hg
    simpa only [d3439, d3870, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3439, d3870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27694 p hg
    simpa only [d3439, d3870, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27696 (p : Pattern) (guard : d5847 p = 1) : d3440 p ≤ (0 : Int) + d3871 p := by
  cases selected : p 49 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3440, d3871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27540 p hg
    simpa only [d3440, d3871, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3440, d3871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27695 p hg
    simpa only [d3440, d3871, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27697 (p : Pattern) (guard : d5847 p = 1) : d3239 p ≤ (0 : Int) + d3872 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27341 p hg
    simpa only [d3872, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27395 p hg
    simpa only [d3872, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27698 (p : Pattern) (guard : d5847 p = 1) : d3239 p ≤ (0 : Int) + d3873 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27396 p hg
    simpa only [d3873, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27697 p hg
    simpa only [d3873, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27699 (p : Pattern) (guard : d5847 p = 1) : d3239 p ≤ (0 : Int) + d3874 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27340 p hg
    simpa only [d3874, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27698 p hg
    simpa only [d3874, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27700 (p : Pattern) (guard : d5847 p = 1) : d3240 p ≤ (0 : Int) + d3875 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3240, d3875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27343 p hg
    simpa only [d3240, d3875, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3240, d3875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3240, d3875, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27701 (p : Pattern) (guard : d5847 p = 1) : d3241 p ≤ (0 : Int) + d3876 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3241, d3876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27699 p hg
    simpa only [d3241, d3876, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3241, d3876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27700 p hg
    simpa only [d3241, d3876, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27702 (p : Pattern) (guard : d5847 p = 1) : d3242 p ≤ (0 : Int) + d3877 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3242, d3877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27457 p hg
    simpa only [d3242, d3877, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3242, d3877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27701 p hg
    simpa only [d3242, d3877, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27703 (p : Pattern) (guard : d5847 p = 1) : d3299 p ≤ (0 : Int) + d3878 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3299, d3878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27457 p hg
    simpa only [d3299, d3878, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3299, d3878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27702 p hg
    simpa only [d3299, d3878, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27704 (p : Pattern) (guard : d5847 p = 1) : d3248 p ≤ (0 : Int) + d3879 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3248, d3879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27702 p hg
    simpa only [d3248, d3879, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3248, d3879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27472 p hg
    simpa only [d3248, d3879, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27705 (p : Pattern) (guard : d5847 p = 1) : d3300 p ≤ (0 : Int) + d3880 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3300, d3880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27703 p hg
    simpa only [d3300, d3880, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3300, d3880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27704 p hg
    simpa only [d3300, d3880, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27706 (p : Pattern) (guard : d5847 p = 1) : d3441 p ≤ (0 : Int) + d3881 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3441, d3881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27440 p hg
    simpa only [d3441, d3881, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3441, d3881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27386 p hg
    simpa only [d3441, d3881, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27707 (p : Pattern) (guard : d5847 p = 1) : d3442 p ≤ (0 : Int) + d3882 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3442, d3882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27475 p hg
    simpa only [d3442, d3882, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3442, d3882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27706 p hg
    simpa only [d3442, d3882, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27708 (p : Pattern) (guard : d5847 p = 1) : d3443 p ≤ (0 : Int) + d3883 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3443, d3883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27440 p hg
    simpa only [d3443, d3883, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3443, d3883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27393 p hg
    simpa only [d3443, d3883, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27709 (p : Pattern) (guard : d5847 p = 1) : d3444 p ≤ (0 : Int) + d3884 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3444, d3884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27476 p hg
    simpa only [d3444, d3884, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3444, d3884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3444, d3884, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27710 (p : Pattern) (guard : d5847 p = 1) : d3445 p ≤ (0 : Int) + d3885 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3445, d3885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27708 p hg
    simpa only [d3445, d3885, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3445, d3885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27709 p hg
    simpa only [d3445, d3885, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27711 (p : Pattern) (guard : d5847 p = 1) : d3446 p ≤ (0 : Int) + d3886 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3446, d3886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27707 p hg
    simpa only [d3446, d3886, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3446, d3886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27710 p hg
    simpa only [d3446, d3886, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27712 (p : Pattern) (guard : d5847 p = 1) : d3447 p ≤ (0 : Int) + d3887 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3447, d3887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27441 p hg
    simpa only [d3447, d3887, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3447, d3887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27709 p hg
    simpa only [d3447, d3887, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27713 (p : Pattern) (guard : d5847 p = 1) : d3448 p ≤ (0 : Int) + d3888 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3448, d3888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27712 p hg
    simpa only [d3448, d3888, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3448, d3888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27448 p hg
    simpa only [d3448, d3888, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27714 (p : Pattern) (guard : d5847 p = 1) : d3449 p ≤ (0 : Int) + d3889 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3449, d3889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27711 p hg
    simpa only [d3449, d3889, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3449, d3889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27713 p hg
    simpa only [d3449, d3889, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27715 (p : Pattern) (guard : d5847 p = 1) : d3450 p ≤ (0 : Int) + d3890 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3450, d3890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27705 p hg
    simpa only [d3450, d3890, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3450, d3890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27714 p hg
    simpa only [d3450, d3890, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27716 (p : Pattern) (guard : d5847 p = 1) : d3250 p ≤ (0 : Int) + d3891 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27374 p hg
    simpa only [d3891, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27372 p hg
    simpa only [d3891, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27717 (p : Pattern) (guard : d5847 p = 1) : d3250 p ≤ (0 : Int) + d3892 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27373 p hg
    simpa only [d3892, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27716 p hg
    simpa only [d3892, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27718 (p : Pattern) (guard : d5847 p = 1) : d3250 p ≤ (0 : Int) + d3893 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27371 p hg
    simpa only [d3893, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27717 p hg
    simpa only [d3893, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27719 (p : Pattern) (guard : d5847 p = 1) : d3251 p ≤ (0 : Int) + d3894 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3251, d3894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27417 p hg
    simpa only [d3251, d3894, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3251, d3894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3251, d3894, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
