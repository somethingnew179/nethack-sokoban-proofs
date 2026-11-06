/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons197
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare27720 (p : Pattern) (guard : d5847 p = 1) : d3275 p ≤ (0 : Int) + d3895 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3275, d3895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27718 p hg
    simpa only [d3275, d3895, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3275, d3895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27719 p hg
    simpa only [d3275, d3895, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27721 (p : Pattern) (guard : d5847 p = 1) : d3306 p ≤ (0 : Int) + d3896 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3306, d3896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27457 p hg
    simpa only [d3306, d3896, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3306, d3896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27720 p hg
    simpa only [d3306, d3896, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27722 (p : Pattern) (guard : d5847 p = 1) : d3277 p ≤ (0 : Int) + d3897 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3277, d3897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27701 p hg
    simpa only [d3277, d3897, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3277, d3897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27471 p hg
    simpa only [d3277, d3897, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27723 (p : Pattern) (guard : d5847 p = 1) : d3307 p ≤ (0 : Int) + d3898 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3307, d3898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27721 p hg
    simpa only [d3307, d3898, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3307, d3898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27722 p hg
    simpa only [d3307, d3898, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27724 (p : Pattern) (guard : d5847 p = 1) : d3282 p ≤ (0 : Int) + d3899 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3282, d3899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27701 p hg
    simpa only [d3282, d3899, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3282, d3899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27433 p hg
    simpa only [d3282, d3899, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27725 (p : Pattern) (guard : d5847 p = 1) : d3285 p ≤ (0 : Int) + d3900 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3285, d3900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27724 p hg
    simpa only [d3285, d3900, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3285, d3900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27437 p hg
    simpa only [d3285, d3900, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27726 (p : Pattern) (guard : d5847 p = 1) : d3308 p ≤ (0 : Int) + d3901 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3308, d3901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27723 p hg
    simpa only [d3308, d3901, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3308, d3901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27725 p hg
    simpa only [d3308, d3901, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27727 (p : Pattern) (guard : d5847 p = 1) : d3451 p ≤ (0 : Int) + d3902 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3451, d3902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27706 p hg
    simpa only [d3451, d3902, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3451, d3902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27401 p hg
    simpa only [d3451, d3902, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27728 (p : Pattern) (guard : d5847 p = 1) : d3452 p ≤ (0 : Int) + d3903 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3452, d3903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27709 p hg
    simpa only [d3452, d3903, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3452, d3903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27447 p hg
    simpa only [d3452, d3903, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27729 (p : Pattern) (guard : d5847 p = 1) : d3453 p ≤ (0 : Int) + d3904 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3453, d3904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27727 p hg
    simpa only [d3453, d3904, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3453, d3904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27728 p hg
    simpa only [d3453, d3904, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27730 (p : Pattern) (guard : d5847 p = 1) : d3454 p ≤ (0 : Int) + d3905 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3454, d3905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27709 p hg
    simpa only [d3454, d3905, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3454, d3905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3454, d3905, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27731 (p : Pattern) (guard : d5847 p = 1) : d3455 p ≤ (0 : Int) + d3906 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3455, d3906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27730 p hg
    simpa only [d3455, d3906, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3455, d3906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3455, d3906, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27732 (p : Pattern) (guard : d5847 p = 1) : d3456 p ≤ (0 : Int) + d3907 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3456, d3907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27729 p hg
    simpa only [d3456, d3907, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3456, d3907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27731 p hg
    simpa only [d3456, d3907, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27733 (p : Pattern) (guard : d5847 p = 1) : d3457 p ≤ (0 : Int) + d3908 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3457, d3908, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27726 p hg
    simpa only [d3457, d3908, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3457, d3908, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27732 p hg
    simpa only [d3457, d3908, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27734 (p : Pattern) (guard : d5847 p = 1) : d3458 p ≤ (0 : Int) + d3909 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3458, d3909, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27715 p hg
    simpa only [d3458, d3909, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3458, d3909, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27733 p hg
    simpa only [d3458, d3909, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27735 (p : Pattern) (guard : d5847 p = 1) : d3226 p ≤ (0 : Int) + d3910 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27319 p hg
    simpa only [d3910, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27460 p hg
    simpa only [d3910, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27736 (p : Pattern) (guard : d5847 p = 1) : d3230 p ≤ (0 : Int) + d3911 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3230, d3911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27454 p hg
    simpa only [d3230, d3911, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3230, d3911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3230, d3911, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27737 (p : Pattern) (guard : d5847 p = 1) : d3238 p ≤ (0 : Int) + d3912 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3238, d3912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27735 p hg
    simpa only [d3238, d3912, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3238, d3912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27736 p hg
    simpa only [d3238, d3912, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27738 (p : Pattern) (guard : d5847 p = 1) : d3238 p ≤ (0 : Int) + d3913 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27737 p hg
    simpa only [d3913, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27465 p hg
    simpa only [d3913, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27739 (p : Pattern) (guard : d5847 p = 1) : d3459 p ≤ (0 : Int) + d3914 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3459, d3914, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27738 p hg
    simpa only [d3459, d3914, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3459, d3914, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27478 p hg
    simpa only [d3459, d3914, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27740 (p : Pattern) (guard : d5847 p = 1) : d3460 p ≤ (0 : Int) + d3915 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3460, d3915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27739 p hg
    simpa only [d3460, d3915, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3460, d3915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27479 p hg
    simpa only [d3460, d3915, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27741 (p : Pattern) (guard : d5847 p = 1) : d3461 p ≤ (0 : Int) + d190 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20377 p hg
    simpa only [d5847, d3461, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20382 p hg
    simpa only [d5847, d3461, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27742 (p : Pattern) (guard : d5847 p = 1) : d3461 p ≤ (0 : Int) + d315 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3461, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20377 p hg
    simpa only [d5847, d3461, d315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3461, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5847, d3461, d315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27743 (p : Pattern) (guard : d5847 p = 1) : d3461 p ≤ (0 : Int) + d3916 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27741 p hg
    simpa only [d3916, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27742 p hg
    simpa only [d3916, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27744 (p : Pattern) (guard : d5847 p = 1) : d3461 p ≤ (0 : Int) + d3917 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27743 p hg
    simpa only [d3917, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27742 p hg
    simpa only [d3917, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27745 (p : Pattern) (guard : d5847 p = 1) : d3461 p ≤ (0 : Int) + d3918 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27741 p hg
    simpa only [d3918, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27744 p hg
    simpa only [d3918, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27746 (p : Pattern) (guard : d5847 p = 1) : d3462 p ≤ (0 : Int) + d3919 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3462, d3919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27744 p hg
    simpa only [d3462, d3919, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3462, d3919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3462, d3919, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27747 (p : Pattern) (guard : d5847 p = 1) : d3463 p ≤ (0 : Int) + d3920 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3463, d3920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27745 p hg
    simpa only [d3463, d3920, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3463, d3920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27746 p hg
    simpa only [d3463, d3920, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27748 (p : Pattern) (guard : d5847 p = 1) : d3464 p ≤ (0 : Int) + d3921 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3464, d3921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27467 p hg
    simpa only [d3464, d3921, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3464, d3921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27747 p hg
    simpa only [d3464, d3921, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27749 (p : Pattern) (guard : d5847 p = 1) : d3465 p ≤ (0 : Int) + d3922 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3465, d3922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27748 p hg
    simpa only [d3465, d3922, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3465, d3922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3465, d3922, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27750 (p : Pattern) (guard : d5847 p = 1) : d3466 p ≤ (0 : Int) + d3923 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3466, d3923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27749 p hg
    simpa only [d3466, d3923, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3466, d3923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3466, d3923, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27751 (p : Pattern) (guard : d5847 p = 1) : d3467 p ≤ (0 : Int) + d3924 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3467, d3924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27740 p hg
    simpa only [d3467, d3924, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3467, d3924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27750 p hg
    simpa only [d3467, d3924, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27752 (p : Pattern) (guard : d5847 p = 1) : d3250 p ≤ (0 : Int) + d3925 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3250, d3925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19916 p hg
    simpa only [d5847, d3250, d3925, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3250, d3925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19996 p hg
    simpa only [d5847, d3250, d3925, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27753 (p : Pattern) (guard : d5847 p = 1) : d3250 p ≤ (0 : Int) + d3926 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27374 p hg
    simpa only [d3926, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27752 p hg
    simpa only [d3926, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27754 (p : Pattern) (guard : d5847 p = 1) : d3250 p ≤ (0 : Int) + d3927 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27373 p hg
    simpa only [d3927, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27753 p hg
    simpa only [d3927, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27755 (p : Pattern) (guard : d5847 p = 1) : d3251 p ≤ (0 : Int) + d3928 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3251, d3928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27754 p hg
    simpa only [d3251, d3928, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3251, d3928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3251, d3928, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27756 (p : Pattern) (guard : d5847 p = 1) : d3275 p ≤ (0 : Int) + d3929 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3275, d3929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27440 p hg
    simpa only [d3275, d3929, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3275, d3929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27755 p hg
    simpa only [d3275, d3929, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27757 (p : Pattern) (guard : d5847 p = 1) : d3275 p ≤ (0 : Int) + d3930 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27756 p hg
    simpa only [d3930, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27475 p hg
    simpa only [d3930, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27758 (p : Pattern) (guard : d5847 p = 1) : d3468 p ≤ (0 : Int) + d3931 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3468, d3931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27467 p hg
    simpa only [d3468, d3931, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3468, d3931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27436 p hg
    simpa only [d3468, d3931, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27759 (p : Pattern) (guard : d5847 p = 1) : d3469 p ≤ (0 : Int) + d3932 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3469, d3932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27757 p hg
    simpa only [d3469, d3932, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3469, d3932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27758 p hg
    simpa only [d3469, d3932, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27760 (p : Pattern) (guard : d5847 p = 1) : d3470 p ≤ (0 : Int) + d3933 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3470, d3933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27759 p hg
    simpa only [d3470, d3933, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3470, d3933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27489 p hg
    simpa only [d3470, d3933, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27761 (p : Pattern) (guard : d5847 p = 1) : d3471 p ≤ (0 : Int) + d3934 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3471, d3934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27747 p hg
    simpa only [d3471, d3934, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3471, d3934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3471, d3934, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27762 (p : Pattern) (guard : d5847 p = 1) : d3472 p ≤ (0 : Int) + d3935 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3472, d3935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27761 p hg
    simpa only [d3472, d3935, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3472, d3935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3472, d3935, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27763 (p : Pattern) (guard : d5847 p = 1) : d3473 p ≤ (0 : Int) + d3936 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3473, d3936, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27762 p hg
    simpa only [d3473, d3936, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3473, d3936, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3473, d3936, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27764 (p : Pattern) (guard : d5847 p = 1) : d3474 p ≤ (0 : Int) + d3937 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3474, d3937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27760 p hg
    simpa only [d3474, d3937, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3474, d3937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27763 p hg
    simpa only [d3474, d3937, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27765 (p : Pattern) (guard : d5847 p = 1) : d3475 p ≤ (0 : Int) + d3938 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3475, d3938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27751 p hg
    simpa only [d3475, d3938, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3475, d3938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27764 p hg
    simpa only [d3475, d3938, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27766 (p : Pattern) (guard : d5847 p = 1) : d3476 p ≤ (0 : Int) + d3939 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3476, d3939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27734 p hg
    simpa only [d3476, d3939, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3476, d3939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27765 p hg
    simpa only [d3476, d3939, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27767 (p : Pattern) (guard : d5847 p = 1) : d3477 p ≤ (0 : Int) + d3940 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3477, d3940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27765 p hg
    simpa only [d3477, d3940, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3477, d3940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3477, d3940, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27768 (p : Pattern) (guard : d5847 p = 1) : d3478 p ≤ (0 : Int) + d3941 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3478, d3941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27766 p hg
    simpa only [d3478, d3941, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3478, d3941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27767 p hg
    simpa only [d3478, d3941, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27769 (p : Pattern) (guard : d5847 p = 1) : d3479 p ≤ (0 : Int) + d3942 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3479, d3942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27532 p hg
    simpa only [d3479, d3942, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3479, d3942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27768 p hg
    simpa only [d3479, d3942, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27770 (p : Pattern) (guard : d5847 p = 1) : d3480 p ≤ (0 : Int) + d3943 p := by
  cases selected : p 71 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3480, d3943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27516 p hg
    simpa only [d3480, d3943, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3480, d3943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27769 p hg
    simpa only [d3480, d3943, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27771 (p : Pattern) (guard : d5847 p = 1) : d3481 p ≤ (0 : Int) + d3944 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3481, d3944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27566 p hg
    simpa only [d3481, d3944, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3481, d3944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3481, d3944, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27772 (p : Pattern) (guard : d5847 p = 1) : d3482 p ≤ (0 : Int) + d3945 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3482, d3945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27623 p hg
    simpa only [d3482, d3945, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3482, d3945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27771 p hg
    simpa only [d3482, d3945, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27773 (p : Pattern) (guard : d5847 p = 1) : d3483 p ≤ (0 : Int) + d3946 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3483, d3946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27771 p hg
    simpa only [d3483, d3946, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3483, d3946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3483, d3946, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27774 (p : Pattern) (guard : d5847 p = 1) : d3484 p ≤ (0 : Int) + d3947 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3484, d3947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27772 p hg
    simpa only [d3484, d3947, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3484, d3947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27773 p hg
    simpa only [d3484, d3947, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27775 (p : Pattern) (guard : d5847 p = 1) : d3485 p ≤ (0 : Int) + d3948 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3485, d3948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27603 p hg
    simpa only [d3485, d3948, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3485, d3948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3485, d3948, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27776 (p : Pattern) (guard : d5847 p = 1) : d3486 p ≤ (0 : Int) + d3949 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3486, d3949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27631 p hg
    simpa only [d3486, d3949, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3486, d3949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27775 p hg
    simpa only [d3486, d3949, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27777 (p : Pattern) (guard : d5847 p = 1) : d3487 p ≤ (0 : Int) + d3950 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3487, d3950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27775 p hg
    simpa only [d3487, d3950, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3487, d3950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3487, d3950, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27778 (p : Pattern) (guard : d5847 p = 1) : d3488 p ≤ (0 : Int) + d3951 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3488, d3951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27776 p hg
    simpa only [d3488, d3951, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3488, d3951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27777 p hg
    simpa only [d3488, d3951, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27779 (p : Pattern) (guard : d5847 p = 1) : d3489 p ≤ (0 : Int) + d3952 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3489, d3952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27774 p hg
    simpa only [d3489, d3952, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3489, d3952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27778 p hg
    simpa only [d3489, d3952, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27780 (p : Pattern) (guard : d5847 p = 1) : d3490 p ≤ (0 : Int) + d3953 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3490, d3953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27609 p hg
    simpa only [d3490, d3953, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3490, d3953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27779 p hg
    simpa only [d3490, d3953, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27781 (p : Pattern) (guard : d5847 p = 1) : d3481 p ≤ (0 : Int) + d3954 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3481, d3954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27653 p hg
    simpa only [d3481, d3954, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3481, d3954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3481, d3954, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27782 (p : Pattern) (guard : d5847 p = 1) : d3491 p ≤ (0 : Int) + d3955 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3491, d3955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27665 p hg
    simpa only [d3491, d3955, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3491, d3955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27781 p hg
    simpa only [d3491, d3955, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27783 (p : Pattern) (guard : d5847 p = 1) : d3483 p ≤ (0 : Int) + d3956 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3483, d3956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27781 p hg
    simpa only [d3483, d3956, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3483, d3956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3483, d3956, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27784 (p : Pattern) (guard : d5847 p = 1) : d3492 p ≤ (0 : Int) + d3957 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3492, d3957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27782 p hg
    simpa only [d3492, d3957, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3492, d3957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27783 p hg
    simpa only [d3492, d3957, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27785 (p : Pattern) (guard : d5847 p = 1) : d3493 p ≤ (0 : Int) + d3958 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3493, d3958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27784 p hg
    simpa only [d3493, d3958, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3493, d3958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27673 p hg
    simpa only [d3493, d3958, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27786 (p : Pattern) (guard : d5847 p = 1) : d3494 p ≤ (0 : Int) + d3959 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3494, d3959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27664 p hg
    simpa only [d3494, d3959, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3494, d3959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27785 p hg
    simpa only [d3494, d3959, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27787 (p : Pattern) (guard : d5847 p = 1) : d3495 p ≤ (0 : Int) + d3960 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3495, d3960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27780 p hg
    simpa only [d3495, d3960, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3495, d3960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27786 p hg
    simpa only [d3495, d3960, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27788 (p : Pattern) (guard : d5847 p = 1) : d3496 p ≤ (0 : Int) + d3961 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3496, d3961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27786 p hg
    simpa only [d3496, d3961, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3496, d3961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27680 p hg
    simpa only [d3496, d3961, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27789 (p : Pattern) (guard : d5847 p = 1) : d3497 p ≤ (0 : Int) + d3962 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3497, d3962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27787 p hg
    simpa only [d3497, d3962, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3497, d3962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27788 p hg
    simpa only [d3497, d3962, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27790 (p : Pattern) (guard : d5847 p = 1) : d3358 p ≤ (0 : Int) + d3963 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27542 p hg
    simpa only [d3963, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27646 p hg
    simpa only [d3963, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27791 (p : Pattern) (guard : d5847 p = 1) : d3362 p ≤ (0 : Int) + d3964 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3362, d3964, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27640 p hg
    simpa only [d3362, d3964, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3362, d3964, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3362, d3964, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27792 (p : Pattern) (guard : d5847 p = 1) : d3364 p ≤ (0 : Int) + d3965 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3364, d3965, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27790 p hg
    simpa only [d3364, d3965, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3364, d3965, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27791 p hg
    simpa only [d3364, d3965, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27793 (p : Pattern) (guard : d5847 p = 1) : d3369 p ≤ (0 : Int) + d3966 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3369, d3966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27792 p hg
    simpa only [d3369, d3966, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3369, d3966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27653 p hg
    simpa only [d3369, d3966, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27794 (p : Pattern) (guard : d5847 p = 1) : d3410 p ≤ (0 : Int) + d3967 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3410, d3967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27643 p hg
    simpa only [d3410, d3967, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3410, d3967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27793 p hg
    simpa only [d3410, d3967, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27795 (p : Pattern) (guard : d5847 p = 1) : d3369 p ≤ (0 : Int) + d3968 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3369, d3968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27648 p hg
    simpa only [d3369, d3968, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3369, d3968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27653 p hg
    simpa only [d3369, d3968, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27796 (p : Pattern) (guard : d5847 p = 1) : d3372 p ≤ (0 : Int) + d3969 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3372, d3969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27795 p hg
    simpa only [d3372, d3969, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3372, d3969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27569 p hg
    simpa only [d3372, d3969, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27797 (p : Pattern) (guard : d5847 p = 1) : d3411 p ≤ (0 : Int) + d3970 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3411, d3970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27794 p hg
    simpa only [d3411, d3970, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3411, d3970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27796 p hg
    simpa only [d3411, d3970, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27798 (p : Pattern) (guard : d5847 p = 1) : d3498 p ≤ (0 : Int) + d3971 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3498, d3971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27629 p hg
    simpa only [d3498, d3971, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3498, d3971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27593 p hg
    simpa only [d3498, d3971, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27799 (p : Pattern) (guard : d5847 p = 1) : d3499 p ≤ (0 : Int) + d3972 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3499, d3972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27658 p hg
    simpa only [d3499, d3972, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3499, d3972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27798 p hg
    simpa only [d3499, d3972, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27800 (p : Pattern) (guard : d5847 p = 1) : d3500 p ≤ (0 : Int) + d3973 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3500, d3973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27799 p hg
    simpa only [d3500, d3973, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3500, d3973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27775 p hg
    simpa only [d3500, d3973, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27801 (p : Pattern) (guard : d5847 p = 1) : d3501 p ≤ (0 : Int) + d3974 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3501, d3974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27659 p hg
    simpa only [d3501, d3974, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3501, d3974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3501, d3974, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27802 (p : Pattern) (guard : d5847 p = 1) : d3502 p ≤ (0 : Int) + d3975 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3502, d3975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27801 p hg
    simpa only [d3502, d3975, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3502, d3975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3502, d3975, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27803 (p : Pattern) (guard : d5847 p = 1) : d3503 p ≤ (0 : Int) + d3976 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3503, d3976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27802 p hg
    simpa only [d3503, d3976, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3503, d3976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3503, d3976, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27804 (p : Pattern) (guard : d5847 p = 1) : d3504 p ≤ (0 : Int) + d3977 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3504, d3977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27800 p hg
    simpa only [d3504, d3977, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3504, d3977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27803 p hg
    simpa only [d3504, d3977, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27805 (p : Pattern) (guard : d5847 p = 1) : d3505 p ≤ (0 : Int) + d3978 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3505, d3978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27797 p hg
    simpa only [d3505, d3978, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3505, d3978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27804 p hg
    simpa only [d3505, d3978, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27806 (p : Pattern) (guard : d5847 p = 1) : d3374 p ≤ (0 : Int) + d3979 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27581 p hg
    simpa only [d3979, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27579 p hg
    simpa only [d3979, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27807 (p : Pattern) (guard : d5847 p = 1) : d3374 p ≤ (0 : Int) + d3980 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3980, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27580 p hg
    simpa only [d3980, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3980, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27806 p hg
    simpa only [d3980, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27808 (p : Pattern) (guard : d5847 p = 1) : d3374 p ≤ (0 : Int) + d3981 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27578 p hg
    simpa only [d3981, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27807 p hg
    simpa only [d3981, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27809 (p : Pattern) (guard : d5847 p = 1) : d3375 p ≤ (0 : Int) + d3982 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3375, d3982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27616 p hg
    simpa only [d3375, d3982, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3375, d3982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3375, d3982, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27810 (p : Pattern) (guard : d5847 p = 1) : d3394 p ≤ (0 : Int) + d3983 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3394, d3983, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27808 p hg
    simpa only [d3394, d3983, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3394, d3983, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27809 p hg
    simpa only [d3394, d3983, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27811 (p : Pattern) (guard : d5847 p = 1) : d3417 p ≤ (0 : Int) + d3984 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3417, d3984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27792 p hg
    simpa only [d3417, d3984, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3417, d3984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27810 p hg
    simpa only [d3417, d3984, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27812 (p : Pattern) (guard : d5847 p = 1) : d3366 p ≤ (0 : Int) + d3985 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27558 p hg
    simpa only [d3985, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27597 p hg
    simpa only [d3985, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27813 (p : Pattern) (guard : d5847 p = 1) : d3366 p ≤ (0 : Int) + d3986 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27598 p hg
    simpa only [d3986, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27812 p hg
    simpa only [d3986, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27814 (p : Pattern) (guard : d5847 p = 1) : d3366 p ≤ (0 : Int) + d3987 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3987, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27557 p hg
    simpa only [d3987, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3987, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27813 p hg
    simpa only [d3987, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27815 (p : Pattern) (guard : d5847 p = 1) : d3367 p ≤ (0 : Int) + d3988 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3367, d3988, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27560 p hg
    simpa only [d3367, d3988, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3367, d3988, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3367, d3988, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27816 (p : Pattern) (guard : d5847 p = 1) : d3368 p ≤ (0 : Int) + d3989 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3368, d3989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27814 p hg
    simpa only [d3368, d3989, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3368, d3989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27815 p hg
    simpa only [d3368, d3989, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27817 (p : Pattern) (guard : d5847 p = 1) : d3481 p ≤ (0 : Int) + d3990 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3481, d3990, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27816 p hg
    simpa only [d3481, d3990, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3481, d3990, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3481, d3990, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27818 (p : Pattern) (guard : d5847 p = 1) : d3491 p ≤ (0 : Int) + d3991 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3491, d3991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27811 p hg
    simpa only [d3491, d3991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3491, d3991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27817 p hg
    simpa only [d3491, d3991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27819 (p : Pattern) (guard : d5847 p = 1) : d3367 p ≤ (0 : Int) + d3992 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3367, d3992, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27813 p hg
    simpa only [d3367, d3992, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3367, d3992, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3367, d3992, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27820 (p : Pattern) (guard : d5847 p = 1) : d3368 p ≤ (0 : Int) + d3993 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3368, d3993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27602 p hg
    simpa only [d3368, d3993, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3368, d3993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27819 p hg
    simpa only [d3368, d3993, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27821 (p : Pattern) (guard : d5847 p = 1) : d3481 p ≤ (0 : Int) + d3994 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3481, d3994, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27820 p hg
    simpa only [d3481, d3994, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3481, d3994, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3481, d3994, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27822 (p : Pattern) (guard : d5847 p = 1) : d3483 p ≤ (0 : Int) + d3995 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3483, d3995, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27821 p hg
    simpa only [d3483, d3995, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3483, d3995, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3483, d3995, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27823 (p : Pattern) (guard : d5847 p = 1) : d3492 p ≤ (0 : Int) + d3996 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3492, d3996, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27818 p hg
    simpa only [d3492, d3996, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3492, d3996, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27822 p hg
    simpa only [d3492, d3996, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27824 (p : Pattern) (guard : d5847 p = 1) : d3506 p ≤ (0 : Int) + d3997 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3506, d3997, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27602 p hg
    simpa only [d3506, d3997, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3506, d3997, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27593 p hg
    simpa only [d3506, d3997, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27825 (p : Pattern) (guard : d5847 p = 1) : d3507 p ≤ (0 : Int) + d3998 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3507, d3998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27824 p hg
    simpa only [d3507, d3998, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3507, d3998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27603 p hg
    simpa only [d3507, d3998, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27826 (p : Pattern) (guard : d5847 p = 1) : d3508 p ≤ (0 : Int) + d3999 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3508, d3999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27825 p hg
    simpa only [d3508, d3999, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3508, d3999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27802 p hg
    simpa only [d3508, d3999, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27827 (p : Pattern) (guard : d5847 p = 1) : d3509 p ≤ (0 : Int) + d4000 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3509, d4000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27407 p hg
    simpa only [d3509, d4000, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3509, d4000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3509, d4000, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27828 (p : Pattern) (guard : d5847 p = 1) : d3510 p ≤ (0 : Int) + d4001 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3510, d4001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27826 p hg
    simpa only [d3510, d4001, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3510, d4001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27827 p hg
    simpa only [d3510, d4001, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27829 (p : Pattern) (guard : d5847 p = 1) : d3511 p ≤ (0 : Int) + d4002 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3511, d4002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27823 p hg
    simpa only [d3511, d4002, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3511, d4002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27828 p hg
    simpa only [d3511, d4002, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27830 (p : Pattern) (guard : d5847 p = 1) : d3512 p ≤ (0 : Int) + d4003 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3512, d4003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27805 p hg
    simpa only [d3512, d4003, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3512, d4003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27829 p hg
    simpa only [d3512, d4003, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27831 (p : Pattern) (guard : d5847 p = 1) : d3364 p ≤ (0 : Int) + d4004 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d4004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27648 p hg
    simpa only [d4004, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d4004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27651 p hg
    simpa only [d4004, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27832 (p : Pattern) (guard : d5847 p = 1) : d3513 p ≤ (0 : Int) + d4005 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3513, d4005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27658 p hg
    simpa only [d3513, d4005, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3513, d4005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27436 p hg
    simpa only [d3513, d4005, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27833 (p : Pattern) (guard : d5847 p = 1) : d3514 p ≤ (0 : Int) + d4006 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3514, d4006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27831 p hg
    simpa only [d3514, d4006, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3514, d4006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27832 p hg
    simpa only [d3514, d4006, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27834 (p : Pattern) (guard : d5847 p = 1) : d3515 p ≤ (0 : Int) + d4007 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3515, d4007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27833 p hg
    simpa only [d3515, d4007, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3515, d4007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27669 p hg
    simpa only [d3515, d4007, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27835 (p : Pattern) (guard : d5847 p = 1) : d3516 p ≤ (0 : Int) + d4008 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3516, d4008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27834 p hg
    simpa only [d3516, d4008, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3516, d4008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27673 p hg
    simpa only [d3516, d4008, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27836 (p : Pattern) (guard : d5847 p = 1) : d3374 p ≤ (0 : Int) + d326 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3374, d326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20197 p hg
    simpa only [d5847, d3374, d326, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3374, d326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20007 p hg
    simpa only [d5847, d3374, d326, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27837 (p : Pattern) (guard : d5847 p = 1) : d3374 p ≤ (0 : Int) + d4009 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d4009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27581 p hg
    simpa only [d4009, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d4009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27836 p hg
    simpa only [d4009, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27838 (p : Pattern) (guard : d5847 p = 1) : d3374 p ≤ (0 : Int) + d4010 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d4010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27580 p hg
    simpa only [d4010, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d4010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27837 p hg
    simpa only [d4010, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27839 (p : Pattern) (guard : d5847 p = 1) : d3375 p ≤ (0 : Int) + d4011 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3375, d4011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27838 p hg
    simpa only [d3375, d4011, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3375, d4011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3375, d4011, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27840 (p : Pattern) (guard : d5847 p = 1) : d3394 p ≤ (0 : Int) + d4012 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3394, d4012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27629 p hg
    simpa only [d3394, d4012, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3394, d4012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27839 p hg
    simpa only [d3394, d4012, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27841 (p : Pattern) (guard : d5847 p = 1) : d3394 p ≤ (0 : Int) + d4013 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d4013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27840 p hg
    simpa only [d4013, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d4013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27658 p hg
    simpa only [d4013, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27842 (p : Pattern) (guard : d5847 p = 1) : d3517 p ≤ (0 : Int) + d4014 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3517, d4014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27841 p hg
    simpa only [d3517, d4014, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3517, d4014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27781 p hg
    simpa only [d3517, d4014, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27843 (p : Pattern) (guard : d5847 p = 1) : d3518 p ≤ (0 : Int) + d4015 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3518, d4015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27842 p hg
    simpa only [d3518, d4015, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3518, d4015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27672 p hg
    simpa only [d3518, d4015, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27844 (p : Pattern) (guard : d5847 p = 1) : d3519 p ≤ (0 : Int) + d4016 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3519, d4016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27472 p hg
    simpa only [d3519, d4016, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3519, d4016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3519, d4016, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27845 (p : Pattern) (guard : d5847 p = 1) : d3520 p ≤ (0 : Int) + d4017 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3520, d4017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27844 p hg
    simpa only [d3520, d4017, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3520, d4017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3520, d4017, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27846 (p : Pattern) (guard : d5847 p = 1) : d3521 p ≤ (0 : Int) + d4018 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3521, d4018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27843 p hg
    simpa only [d3521, d4018, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3521, d4018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27845 p hg
    simpa only [d3521, d4018, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27847 (p : Pattern) (guard : d5847 p = 1) : d3522 p ≤ (0 : Int) + d4019 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3522, d4019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27835 p hg
    simpa only [d3522, d4019, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3522, d4019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27846 p hg
    simpa only [d3522, d4019, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27848 (p : Pattern) (guard : d5847 p = 1) : d3523 p ≤ (0 : Int) + d4020 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3523, d4020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27830 p hg
    simpa only [d3523, d4020, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3523, d4020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27847 p hg
    simpa only [d3523, d4020, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27849 (p : Pattern) (guard : d5847 p = 1) : d3524 p ≤ (0 : Int) + d4021 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3524, d4021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27658 p hg
    simpa only [d3524, d4021, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3524, d4021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27471 p hg
    simpa only [d3524, d4021, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27850 (p : Pattern) (guard : d5847 p = 1) : d3525 p ≤ (0 : Int) + d4022 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3525, d4022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27831 p hg
    simpa only [d3525, d4022, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3525, d4022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27849 p hg
    simpa only [d3525, d4022, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27851 (p : Pattern) (guard : d5847 p = 1) : d3526 p ≤ (0 : Int) + d4023 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3526, d4023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27653 p hg
    simpa only [d3526, d4023, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3526, d4023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27471 p hg
    simpa only [d3526, d4023, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27852 (p : Pattern) (guard : d5847 p = 1) : d3527 p ≤ (0 : Int) + d4024 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3527, d4024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27851 p hg
    simpa only [d3527, d4024, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3527, d4024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3527, d4024, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27853 (p : Pattern) (guard : d5847 p = 1) : d3528 p ≤ (0 : Int) + d4025 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3528, d4025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27850 p hg
    simpa only [d3528, d4025, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3528, d4025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27852 p hg
    simpa only [d3528, d4025, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27854 (p : Pattern) (guard : d5847 p = 1) : d3529 p ≤ (0 : Int) + d4026 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3529, d4026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27660 p hg
    simpa only [d3529, d4026, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3529, d4026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27436 p hg
    simpa only [d3529, d4026, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27855 (p : Pattern) (guard : d5847 p = 1) : d3530 p ≤ (0 : Int) + d4027 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3530, d4027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27854 p hg
    simpa only [d3530, d4027, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3530, d4027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3530, d4027, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27856 (p : Pattern) (guard : d5847 p = 1) : d3531 p ≤ (0 : Int) + d4028 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3531, d4028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27855 p hg
    simpa only [d3531, d4028, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3531, d4028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3531, d4028, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27857 (p : Pattern) (guard : d5847 p = 1) : d3532 p ≤ (0 : Int) + d4029 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3532, d4029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27853 p hg
    simpa only [d3532, d4029, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3532, d4029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27856 p hg
    simpa only [d3532, d4029, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27858 (p : Pattern) (guard : d5847 p = 1) : d3533 p ≤ (0 : Int) + d4030 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3533, d4030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27857 p hg
    simpa only [d3533, d4030, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3533, d4030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27846 p hg
    simpa only [d3533, d4030, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27859 (p : Pattern) (guard : d5847 p = 1) : d3534 p ≤ (0 : Int) + d4031 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3534, d4031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27858 p hg
    simpa only [d3534, d4031, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3534, d4031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3534, d4031, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
