/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons211
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare29680 (p : Pattern) (guard : d5850 p = 1) : d3913 p ≤ (0 : Int) + d2601 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29679 p hg
    simpa only [d3913, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29381 p hg
    simpa only [d3913, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29681 (p : Pattern) (guard : d5850 p = 1) : d3914 p ≤ (0 : Int) + d2810 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3914, d2810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29680 p hg
    simpa only [d3914, d2810, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3914, d2810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29395 p hg
    simpa only [d3914, d2810, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29682 (p : Pattern) (guard : d5850 p = 1) : d3915 p ≤ (0 : Int) + d2811 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3915, d2811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29681 p hg
    simpa only [d3915, d2811, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3915, d2811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29396 p hg
    simpa only [d3915, d2811, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29683 (p : Pattern) (guard : d5843 p = 1) : d190 p ≤ (0 : Int) + d191 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23785 p hg
    simpa only [d191, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20378 p hg
    simpa only [d191, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29684 (p : Pattern) (guard : d5850 p = 1) : d190 p ≤ (0 : Int) + d2812 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d2812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29683 p hg
    simpa only [d5850, d2812, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d2812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17896 p hg
    simpa only [d5850, d2812, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29685 (p : Pattern) (guard : d5850 p = 1) : d3916 p ≤ (0 : Int) + d2812 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d3916, d2812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29683 p hg
    simpa only [d5850, d3916, d2812, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d3916, d2812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17512 p hg
    simpa only [d5850, d3916, d2812, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29686 (p : Pattern) (guard : d5850 p = 1) : d315 p ≤ (0 : Int) + d320 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20964 p hg
    simpa only [d5850, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17512 p hg
    simpa only [d5850, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29687 (p : Pattern) (guard : d5850 p = 1) : d3917 p ≤ (0 : Int) + d2813 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3917, d2813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29685 p hg
    simpa only [d3917, d2813, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3917, d2813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29686 p hg
    simpa only [d3917, d2813, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29688 (p : Pattern) (guard : d5850 p = 1) : d3918 p ≤ (0 : Int) + d2814 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3918, d2814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29684 p hg
    simpa only [d3918, d2814, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3918, d2814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29687 p hg
    simpa only [d3918, d2814, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29689 (p : Pattern) (guard : d5850 p = 1) : d3919 p ≤ (0 : Int) + d2815 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3919, d2815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29687 p hg
    simpa only [d3919, d2815, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3919, d2815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d3919, d2815, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29690 (p : Pattern) (guard : d5850 p = 1) : d3920 p ≤ (0 : Int) + d2816 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3920, d2816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29688 p hg
    simpa only [d3920, d2816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3920, d2816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29689 p hg
    simpa only [d3920, d2816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29691 (p : Pattern) (guard : d5850 p = 1) : d3921 p ≤ (0 : Int) + d2817 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3921, d2817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29383 p hg
    simpa only [d3921, d2817, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3921, d2817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29690 p hg
    simpa only [d3921, d2817, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29692 (p : Pattern) (guard : d5850 p = 1) : d3922 p ≤ (0 : Int) + d2818 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3922, d2818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29691 p hg
    simpa only [d3922, d2818, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3922, d2818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d3922, d2818, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29693 (p : Pattern) (guard : d5850 p = 1) : d3923 p ≤ (0 : Int) + d2819 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3923, d2819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29692 p hg
    simpa only [d3923, d2819, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3923, d2819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d3923, d2819, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29694 (p : Pattern) (guard : d5850 p = 1) : d3924 p ≤ (0 : Int) + d2820 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3924, d2820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29682 p hg
    simpa only [d3924, d2820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3924, d2820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29693 p hg
    simpa only [d3924, d2820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29695 (p : Pattern) (guard : d0 p = 1) : d3925 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare29696 (p : Pattern) (guard : d5850 p = 1) : d3926 p ≤ (0 : Int) + d2541 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d3926, d2541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29281 p hg
    simpa only [d5850, d3926, d2541, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d3926, d2541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29695 p hg
    simpa only [d5850, d3926, d2541, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29697 (p : Pattern) (guard : d5850 p = 1) : d3927 p ≤ (0 : Int) + d2542 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3927, d2542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29279 p hg
    simpa only [d3927, d2542, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3927, d2542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29696 p hg
    simpa only [d3927, d2542, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29698 (p : Pattern) (guard : d5850 p = 1) : d3928 p ≤ (0 : Int) + d2543 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3928, d2543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29697 p hg
    simpa only [d3928, d2543, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3928, d2543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d3928, d2543, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29699 (p : Pattern) (guard : d5850 p = 1) : d3929 p ≤ (0 : Int) + d2611 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3929, d2611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29356 p hg
    simpa only [d3929, d2611, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3929, d2611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29698 p hg
    simpa only [d3929, d2611, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29700 (p : Pattern) (guard : d5850 p = 1) : d3930 p ≤ (0 : Int) + d2611 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29699 p hg
    simpa only [d3930, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29391 p hg
    simpa only [d3930, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29701 (p : Pattern) (guard : d5850 p = 1) : d3931 p ≤ (0 : Int) + d2821 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3931, d2821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29383 p hg
    simpa only [d3931, d2821, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3931, d2821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29352 p hg
    simpa only [d3931, d2821, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29702 (p : Pattern) (guard : d5850 p = 1) : d3932 p ≤ (0 : Int) + d2822 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3932, d2822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29700 p hg
    simpa only [d3932, d2822, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3932, d2822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29701 p hg
    simpa only [d3932, d2822, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29703 (p : Pattern) (guard : d5850 p = 1) : d3933 p ≤ (0 : Int) + d2823 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3933, d2823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29702 p hg
    simpa only [d3933, d2823, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3933, d2823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29406 p hg
    simpa only [d3933, d2823, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29704 (p : Pattern) (guard : d5850 p = 1) : d3934 p ≤ (0 : Int) + d2824 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3934, d2824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29690 p hg
    simpa only [d3934, d2824, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3934, d2824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d3934, d2824, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29705 (p : Pattern) (guard : d5850 p = 1) : d3935 p ≤ (0 : Int) + d2825 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3935, d2825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29704 p hg
    simpa only [d3935, d2825, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3935, d2825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d3935, d2825, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29706 (p : Pattern) (guard : d5850 p = 1) : d3936 p ≤ (0 : Int) + d2826 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3936, d2826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29705 p hg
    simpa only [d3936, d2826, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3936, d2826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d3936, d2826, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29707 (p : Pattern) (guard : d5850 p = 1) : d3937 p ≤ (0 : Int) + d2827 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3937, d2827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29703 p hg
    simpa only [d3937, d2827, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3937, d2827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29706 p hg
    simpa only [d3937, d2827, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29708 (p : Pattern) (guard : d5850 p = 1) : d3938 p ≤ (0 : Int) + d2828 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3938, d2828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29694 p hg
    simpa only [d3938, d2828, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3938, d2828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29707 p hg
    simpa only [d3938, d2828, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29709 (p : Pattern) (guard : d5850 p = 1) : d3939 p ≤ (0 : Int) + d2829 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3939, d2829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29676 p hg
    simpa only [d3939, d2829, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3939, d2829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29708 p hg
    simpa only [d3939, d2829, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29710 (p : Pattern) (guard : d5850 p = 1) : d3940 p ≤ (0 : Int) + d2830 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3940, d2830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29708 p hg
    simpa only [d3940, d2830, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3940, d2830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d3940, d2830, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29711 (p : Pattern) (guard : d5850 p = 1) : d3941 p ≤ (0 : Int) + d2831 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3941, d2831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29709 p hg
    simpa only [d3941, d2831, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3941, d2831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29710 p hg
    simpa only [d3941, d2831, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29712 (p : Pattern) (guard : d5850 p = 1) : d3942 p ≤ (0 : Int) + d2832 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3942, d2832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29452 p hg
    simpa only [d3942, d2832, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3942, d2832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29711 p hg
    simpa only [d3942, d2832, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29713 (p : Pattern) (guard : d5850 p = 1) : d3943 p ≤ (0 : Int) + d2833 p := by
  cases selected : p 71 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3943, d2833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29433 p hg
    simpa only [d3943, d2833, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3943, d2833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29712 p hg
    simpa only [d3943, d2833, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29714 (p : Pattern) (guard : d5850 p = 1) : d3944 p ≤ (0 : Int) + d2834 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3944, d2834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29503 p hg
    simpa only [d3944, d2834, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3944, d2834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d3944, d2834, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29715 (p : Pattern) (guard : d5850 p = 1) : d3945 p ≤ (0 : Int) + d2835 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3945, d2835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29564 p hg
    simpa only [d3945, d2835, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3945, d2835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29714 p hg
    simpa only [d3945, d2835, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29716 (p : Pattern) (guard : d5850 p = 1) : d3946 p ≤ (0 : Int) + d2836 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3946, d2836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29714 p hg
    simpa only [d3946, d2836, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3946, d2836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d3946, d2836, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29717 (p : Pattern) (guard : d5850 p = 1) : d3947 p ≤ (0 : Int) + d2837 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3947, d2837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29715 p hg
    simpa only [d3947, d2837, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3947, d2837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29716 p hg
    simpa only [d3947, d2837, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29718 (p : Pattern) (guard : d5850 p = 1) : d3948 p ≤ (0 : Int) + d2838 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3948, d2838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29538 p hg
    simpa only [d3948, d2838, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3948, d2838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d3948, d2838, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29719 (p : Pattern) (guard : d5850 p = 1) : d3949 p ≤ (0 : Int) + d2839 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3949, d2839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29572 p hg
    simpa only [d3949, d2839, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3949, d2839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29718 p hg
    simpa only [d3949, d2839, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29720 (p : Pattern) (guard : d5850 p = 1) : d3950 p ≤ (0 : Int) + d2840 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3950, d2840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29718 p hg
    simpa only [d3950, d2840, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3950, d2840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d3950, d2840, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29721 (p : Pattern) (guard : d5850 p = 1) : d3951 p ≤ (0 : Int) + d2841 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3951, d2841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29719 p hg
    simpa only [d3951, d2841, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3951, d2841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29720 p hg
    simpa only [d3951, d2841, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29722 (p : Pattern) (guard : d5850 p = 1) : d3952 p ≤ (0 : Int) + d2842 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3952, d2842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29717 p hg
    simpa only [d3952, d2842, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3952, d2842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29721 p hg
    simpa only [d3952, d2842, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29723 (p : Pattern) (guard : d5850 p = 1) : d3953 p ≤ (0 : Int) + d2843 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3953, d2843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29544 p hg
    simpa only [d3953, d2843, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3953, d2843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29722 p hg
    simpa only [d3953, d2843, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29724 (p : Pattern) (guard : d5850 p = 1) : d3954 p ≤ (0 : Int) + d2844 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3954, d2844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29594 p hg
    simpa only [d3954, d2844, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3954, d2844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d3954, d2844, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29725 (p : Pattern) (guard : d5850 p = 1) : d3955 p ≤ (0 : Int) + d2845 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3955, d2845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29607 p hg
    simpa only [d3955, d2845, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3955, d2845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29724 p hg
    simpa only [d3955, d2845, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29726 (p : Pattern) (guard : d5850 p = 1) : d3956 p ≤ (0 : Int) + d2846 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3956, d2846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29724 p hg
    simpa only [d3956, d2846, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3956, d2846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d3956, d2846, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29727 (p : Pattern) (guard : d5850 p = 1) : d3957 p ≤ (0 : Int) + d2847 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3957, d2847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29725 p hg
    simpa only [d3957, d2847, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3957, d2847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29726 p hg
    simpa only [d3957, d2847, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29728 (p : Pattern) (guard : d5850 p = 1) : d3958 p ≤ (0 : Int) + d2848 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3958, d2848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29727 p hg
    simpa only [d3958, d2848, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3958, d2848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29615 p hg
    simpa only [d3958, d2848, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29729 (p : Pattern) (guard : d5850 p = 1) : d3959 p ≤ (0 : Int) + d2849 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3959, d2849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29606 p hg
    simpa only [d3959, d2849, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3959, d2849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29728 p hg
    simpa only [d3959, d2849, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29730 (p : Pattern) (guard : d5850 p = 1) : d3960 p ≤ (0 : Int) + d2850 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3960, d2850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29723 p hg
    simpa only [d3960, d2850, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3960, d2850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29729 p hg
    simpa only [d3960, d2850, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29731 (p : Pattern) (guard : d5850 p = 1) : d3961 p ≤ (0 : Int) + d2851 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3961, d2851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29729 p hg
    simpa only [d3961, d2851, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3961, d2851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29622 p hg
    simpa only [d3961, d2851, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29732 (p : Pattern) (guard : d5850 p = 1) : d3962 p ≤ (0 : Int) + d2852 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3962, d2852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29730 p hg
    simpa only [d3962, d2852, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3962, d2852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29731 p hg
    simpa only [d3962, d2852, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29733 (p : Pattern) (guard : d5850 p = 1) : d3963 p ≤ (0 : Int) + d2686 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3963, d2686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29467 p hg
    simpa only [d3963, d2686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3963, d2686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29587 p hg
    simpa only [d3963, d2686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29734 (p : Pattern) (guard : d5850 p = 1) : d3964 p ≤ (0 : Int) + d2745 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3964, d2745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29581 p hg
    simpa only [d3964, d2745, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3964, d2745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d3964, d2745, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29735 (p : Pattern) (guard : d5850 p = 1) : d3965 p ≤ (0 : Int) + d2746 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3965, d2746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29733 p hg
    simpa only [d3965, d2746, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3965, d2746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29734 p hg
    simpa only [d3965, d2746, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29736 (p : Pattern) (guard : d5850 p = 1) : d3966 p ≤ (0 : Int) + d2749 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3966, d2749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29735 p hg
    simpa only [d3966, d2749, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3966, d2749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29594 p hg
    simpa only [d3966, d2749, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29737 (p : Pattern) (guard : d5850 p = 1) : d3967 p ≤ (0 : Int) + d2750 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3967, d2750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29584 p hg
    simpa only [d3967, d2750, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3967, d2750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29736 p hg
    simpa only [d3967, d2750, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29738 (p : Pattern) (guard : d5850 p = 1) : d3968 p ≤ (0 : Int) + d2749 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3968, d2749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29589 p hg
    simpa only [d3968, d2749, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3968, d2749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29594 p hg
    simpa only [d3968, d2749, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29739 (p : Pattern) (guard : d5850 p = 1) : d3969 p ≤ (0 : Int) + d2751 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3969, d2751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29738 p hg
    simpa only [d3969, d2751, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3969, d2751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29506 p hg
    simpa only [d3969, d2751, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29740 (p : Pattern) (guard : d5850 p = 1) : d3970 p ≤ (0 : Int) + d2752 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3970, d2752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29737 p hg
    simpa only [d3970, d2752, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3970, d2752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29739 p hg
    simpa only [d3970, d2752, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29741 (p : Pattern) (guard : d5850 p = 1) : d3971 p ≤ (0 : Int) + d2853 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3971, d2853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29570 p hg
    simpa only [d3971, d2853, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3971, d2853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29529 p hg
    simpa only [d3971, d2853, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29742 (p : Pattern) (guard : d5850 p = 1) : d3972 p ≤ (0 : Int) + d2854 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3972, d2854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29599 p hg
    simpa only [d3972, d2854, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3972, d2854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29741 p hg
    simpa only [d3972, d2854, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29743 (p : Pattern) (guard : d5850 p = 1) : d3973 p ≤ (0 : Int) + d2855 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3973, d2855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29742 p hg
    simpa only [d3973, d2855, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3973, d2855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29718 p hg
    simpa only [d3973, d2855, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29744 (p : Pattern) (guard : d5850 p = 1) : d3974 p ≤ (0 : Int) + d2856 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3974, d2856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29601 p hg
    simpa only [d3974, d2856, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3974, d2856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d3974, d2856, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29745 (p : Pattern) (guard : d5850 p = 1) : d3975 p ≤ (0 : Int) + d2857 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3975, d2857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29744 p hg
    simpa only [d3975, d2857, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3975, d2857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d3975, d2857, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29746 (p : Pattern) (guard : d5850 p = 1) : d3976 p ≤ (0 : Int) + d2858 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3976, d2858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29745 p hg
    simpa only [d3976, d2858, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3976, d2858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d3976, d2858, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29747 (p : Pattern) (guard : d5850 p = 1) : d3977 p ≤ (0 : Int) + d2859 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3977, d2859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29743 p hg
    simpa only [d3977, d2859, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3977, d2859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29746 p hg
    simpa only [d3977, d2859, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29748 (p : Pattern) (guard : d5850 p = 1) : d3978 p ≤ (0 : Int) + d2860 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3978, d2860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29740 p hg
    simpa only [d3978, d2860, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3978, d2860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29747 p hg
    simpa only [d3978, d2860, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29749 (p : Pattern) (guard : d5850 p = 1) : d3979 p ≤ (0 : Int) + d2703 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d3979, d2703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29518 p hg
    simpa only [d5850, d3979, d2703, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d3979, d2703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29515 p hg
    simpa only [d5850, d3979, d2703, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29750 (p : Pattern) (guard : d5850 p = 1) : d3980 p ≤ (0 : Int) + d2704 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3980, d2704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29516 p hg
    simpa only [d3980, d2704, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3980, d2704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29749 p hg
    simpa only [d3980, d2704, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29751 (p : Pattern) (guard : d5850 p = 1) : d3981 p ≤ (0 : Int) + d2725 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3981, d2725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29550 p hg
    simpa only [d3981, d2725, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3981, d2725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29750 p hg
    simpa only [d3981, d2725, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29752 (p : Pattern) (guard : d5850 p = 1) : d3982 p ≤ (0 : Int) + d2705 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3982, d2705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29554 p hg
    simpa only [d3982, d2705, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3982, d2705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d3982, d2705, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29753 (p : Pattern) (guard : d5850 p = 1) : d3983 p ≤ (0 : Int) + d2753 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3983, d2753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29751 p hg
    simpa only [d3983, d2753, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3983, d2753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29752 p hg
    simpa only [d3983, d2753, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29754 (p : Pattern) (guard : d5850 p = 1) : d3984 p ≤ (0 : Int) + d2760 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3984, d2760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29735 p hg
    simpa only [d3984, d2760, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3984, d2760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29753 p hg
    simpa only [d3984, d2760, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29755 (p : Pattern) (guard : d5850 p = 1) : d3985 p ≤ (0 : Int) + d2690 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d3985, d2690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29492 p hg
    simpa only [d5850, d3985, d2690, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d3985, d2690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29533 p hg
    simpa only [d5850, d3985, d2690, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29756 (p : Pattern) (guard : d5850 p = 1) : d3986 p ≤ (0 : Int) + d2691 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3986, d2691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29534 p hg
    simpa only [d3986, d2691, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3986, d2691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29755 p hg
    simpa only [d3986, d2691, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29757 (p : Pattern) (guard : d5850 p = 1) : d3987 p ≤ (0 : Int) + d2692 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3987, d2692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29488 p hg
    simpa only [d3987, d2692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3987, d2692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29756 p hg
    simpa only [d3987, d2692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29758 (p : Pattern) (guard : d5850 p = 1) : d3988 p ≤ (0 : Int) + d2747 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3988, d2747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29494 p hg
    simpa only [d3988, d2747, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3988, d2747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d3988, d2747, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29759 (p : Pattern) (guard : d5850 p = 1) : d3989 p ≤ (0 : Int) + d2748 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3989, d2748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29757 p hg
    simpa only [d3989, d2748, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3989, d2748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29758 p hg
    simpa only [d3989, d2748, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29760 (p : Pattern) (guard : d5850 p = 1) : d3990 p ≤ (0 : Int) + d2844 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3990, d2844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29759 p hg
    simpa only [d3990, d2844, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3990, d2844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d3990, d2844, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29761 (p : Pattern) (guard : d5850 p = 1) : d3991 p ≤ (0 : Int) + d2845 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3991, d2845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29754 p hg
    simpa only [d3991, d2845, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3991, d2845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29760 p hg
    simpa only [d3991, d2845, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29762 (p : Pattern) (guard : d5850 p = 1) : d3992 p ≤ (0 : Int) + d2747 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3992, d2747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29756 p hg
    simpa only [d3992, d2747, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3992, d2747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d3992, d2747, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29763 (p : Pattern) (guard : d5850 p = 1) : d3993 p ≤ (0 : Int) + d2748 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3993, d2748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29537 p hg
    simpa only [d3993, d2748, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3993, d2748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29762 p hg
    simpa only [d3993, d2748, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29764 (p : Pattern) (guard : d5850 p = 1) : d3994 p ≤ (0 : Int) + d2844 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3994, d2844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29763 p hg
    simpa only [d3994, d2844, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3994, d2844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d3994, d2844, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29765 (p : Pattern) (guard : d5850 p = 1) : d3995 p ≤ (0 : Int) + d2846 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3995, d2846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29764 p hg
    simpa only [d3995, d2846, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3995, d2846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d3995, d2846, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29766 (p : Pattern) (guard : d5850 p = 1) : d3996 p ≤ (0 : Int) + d2847 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3996, d2847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29761 p hg
    simpa only [d3996, d2847, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3996, d2847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29765 p hg
    simpa only [d3996, d2847, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29767 (p : Pattern) (guard : d5850 p = 1) : d3997 p ≤ (0 : Int) + d2861 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3997, d2861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29537 p hg
    simpa only [d3997, d2861, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3997, d2861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29529 p hg
    simpa only [d3997, d2861, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29768 (p : Pattern) (guard : d5850 p = 1) : d3998 p ≤ (0 : Int) + d2862 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3998, d2862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29767 p hg
    simpa only [d3998, d2862, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3998, d2862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29538 p hg
    simpa only [d3998, d2862, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29769 (p : Pattern) (guard : d5850 p = 1) : d3999 p ≤ (0 : Int) + d2863 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3999, d2863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29768 p hg
    simpa only [d3999, d2863, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3999, d2863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29745 p hg
    simpa only [d3999, d2863, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29770 (p : Pattern) (guard : d5850 p = 1) : d4000 p ≤ (0 : Int) + d2864 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d4000, d2864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29312 p hg
    simpa only [d4000, d2864, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d4000, d2864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d4000, d2864, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29771 (p : Pattern) (guard : d5850 p = 1) : d4001 p ≤ (0 : Int) + d2865 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d4001, d2865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29769 p hg
    simpa only [d4001, d2865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d4001, d2865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29770 p hg
    simpa only [d4001, d2865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29772 (p : Pattern) (guard : d5850 p = 1) : d4002 p ≤ (0 : Int) + d2866 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d4002, d2866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29766 p hg
    simpa only [d4002, d2866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d4002, d2866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29771 p hg
    simpa only [d4002, d2866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29773 (p : Pattern) (guard : d5850 p = 1) : d4003 p ≤ (0 : Int) + d2867 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d4003, d2867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29748 p hg
    simpa only [d4003, d2867, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d4003, d2867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29772 p hg
    simpa only [d4003, d2867, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29774 (p : Pattern) (guard : d5850 p = 1) : d4004 p ≤ (0 : Int) + d2746 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d4004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29589 p hg
    simpa only [d4004, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d4004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29592 p hg
    simpa only [d4004, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29775 (p : Pattern) (guard : d5850 p = 1) : d4005 p ≤ (0 : Int) + d2868 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d4005, d2868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29599 p hg
    simpa only [d4005, d2868, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d4005, d2868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29352 p hg
    simpa only [d4005, d2868, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29776 (p : Pattern) (guard : d5850 p = 1) : d4006 p ≤ (0 : Int) + d2869 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d4006, d2869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29774 p hg
    simpa only [d4006, d2869, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d4006, d2869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29775 p hg
    simpa only [d4006, d2869, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29777 (p : Pattern) (guard : d5850 p = 1) : d4007 p ≤ (0 : Int) + d2870 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d4007, d2870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29776 p hg
    simpa only [d4007, d2870, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d4007, d2870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29611 p hg
    simpa only [d4007, d2870, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29778 (p : Pattern) (guard : d5850 p = 1) : d4008 p ≤ (0 : Int) + d2871 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d4008, d2871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29777 p hg
    simpa only [d4008, d2871, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d4008, d2871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29615 p hg
    simpa only [d4008, d2871, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29779 (p : Pattern) (guard : d0 p = 1) : d326 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare29780 (p : Pattern) (guard : d5850 p = 1) : d4009 p ≤ (0 : Int) + d2703 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d4009, d2703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29518 p hg
    simpa only [d5850, d4009, d2703, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d4009, d2703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29779 p hg
    simpa only [d5850, d4009, d2703, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29781 (p : Pattern) (guard : d5850 p = 1) : d4010 p ≤ (0 : Int) + d2704 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d4010, d2704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29516 p hg
    simpa only [d4010, d2704, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d4010, d2704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29780 p hg
    simpa only [d4010, d2704, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29782 (p : Pattern) (guard : d5850 p = 1) : d4011 p ≤ (0 : Int) + d2705 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d4011, d2705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29781 p hg
    simpa only [d4011, d2705, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d4011, d2705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d4011, d2705, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29783 (p : Pattern) (guard : d5850 p = 1) : d4012 p ≤ (0 : Int) + d2753 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d4012, d2753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29570 p hg
    simpa only [d4012, d2753, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d4012, d2753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29782 p hg
    simpa only [d4012, d2753, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29784 (p : Pattern) (guard : d5850 p = 1) : d4013 p ≤ (0 : Int) + d2753 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d4013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29783 p hg
    simpa only [d4013, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d4013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29599 p hg
    simpa only [d4013, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29785 (p : Pattern) (guard : d5850 p = 1) : d4014 p ≤ (0 : Int) + d2872 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d4014, d2872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29784 p hg
    simpa only [d4014, d2872, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d4014, d2872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29724 p hg
    simpa only [d4014, d2872, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29786 (p : Pattern) (guard : d5850 p = 1) : d4015 p ≤ (0 : Int) + d2873 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d4015, d2873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29785 p hg
    simpa only [d4015, d2873, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d4015, d2873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29614 p hg
    simpa only [d4015, d2873, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29787 (p : Pattern) (guard : d5850 p = 1) : d4016 p ≤ (0 : Int) + d2874 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d4016, d2874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29388 p hg
    simpa only [d4016, d2874, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d4016, d2874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d4016, d2874, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29788 (p : Pattern) (guard : d5850 p = 1) : d4017 p ≤ (0 : Int) + d2875 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d4017, d2875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29787 p hg
    simpa only [d4017, d2875, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d4017, d2875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d4017, d2875, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29789 (p : Pattern) (guard : d5850 p = 1) : d4018 p ≤ (0 : Int) + d2876 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d4018, d2876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29786 p hg
    simpa only [d4018, d2876, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d4018, d2876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29788 p hg
    simpa only [d4018, d2876, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29790 (p : Pattern) (guard : d5850 p = 1) : d4019 p ≤ (0 : Int) + d2877 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d4019, d2877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29778 p hg
    simpa only [d4019, d2877, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d4019, d2877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29789 p hg
    simpa only [d4019, d2877, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29791 (p : Pattern) (guard : d5850 p = 1) : d4020 p ≤ (0 : Int) + d2878 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d4020, d2878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29773 p hg
    simpa only [d4020, d2878, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d4020, d2878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29790 p hg
    simpa only [d4020, d2878, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29792 (p : Pattern) (guard : d5850 p = 1) : d4021 p ≤ (0 : Int) + d2879 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d4021, d2879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29599 p hg
    simpa only [d4021, d2879, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d4021, d2879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29387 p hg
    simpa only [d4021, d2879, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29793 (p : Pattern) (guard : d5850 p = 1) : d4022 p ≤ (0 : Int) + d2880 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d4022, d2880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29774 p hg
    simpa only [d4022, d2880, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d4022, d2880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29792 p hg
    simpa only [d4022, d2880, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29794 (p : Pattern) (guard : d5850 p = 1) : d4023 p ≤ (0 : Int) + d2881 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d4023, d2881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29594 p hg
    simpa only [d4023, d2881, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d4023, d2881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29387 p hg
    simpa only [d4023, d2881, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29795 (p : Pattern) (guard : d5850 p = 1) : d4024 p ≤ (0 : Int) + d2882 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d4024, d2882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29794 p hg
    simpa only [d4024, d2882, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d4024, d2882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d4024, d2882, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29796 (p : Pattern) (guard : d5850 p = 1) : d4025 p ≤ (0 : Int) + d2883 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d4025, d2883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29793 p hg
    simpa only [d4025, d2883, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d4025, d2883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29795 p hg
    simpa only [d4025, d2883, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29797 (p : Pattern) (guard : d5850 p = 1) : d4026 p ≤ (0 : Int) + d2884 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d4026, d2884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29602 p hg
    simpa only [d4026, d2884, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d4026, d2884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29352 p hg
    simpa only [d4026, d2884, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29798 (p : Pattern) (guard : d5850 p = 1) : d4027 p ≤ (0 : Int) + d2885 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d4027, d2885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29797 p hg
    simpa only [d4027, d2885, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d4027, d2885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d4027, d2885, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29799 (p : Pattern) (guard : d5850 p = 1) : d4028 p ≤ (0 : Int) + d2886 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d4028, d2886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29798 p hg
    simpa only [d4028, d2886, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d4028, d2886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d4028, d2886, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29800 (p : Pattern) (guard : d5850 p = 1) : d4029 p ≤ (0 : Int) + d2887 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d4029, d2887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29796 p hg
    simpa only [d4029, d2887, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d4029, d2887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29799 p hg
    simpa only [d4029, d2887, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29801 (p : Pattern) (guard : d5850 p = 1) : d4030 p ≤ (0 : Int) + d2888 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d4030, d2888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29800 p hg
    simpa only [d4030, d2888, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d4030, d2888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29789 p hg
    simpa only [d4030, d2888, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29802 (p : Pattern) (guard : d5850 p = 1) : d4031 p ≤ (0 : Int) + d2889 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d4031, d2889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29801 p hg
    simpa only [d4031, d2889, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d4031, d2889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d4031, d2889, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29803 (p : Pattern) (guard : d5850 p = 1) : d4032 p ≤ (0 : Int) + d2890 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d4032, d2890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29791 p hg
    simpa only [d4032, d2890, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d4032, d2890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29802 p hg
    simpa only [d4032, d2890, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29804 (p : Pattern) (guard : d5850 p = 1) : d4033 p ≤ (0 : Int) + d2891 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d4033, d2891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29732 p hg
    simpa only [d4033, d2891, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d4033, d2891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29803 p hg
    simpa only [d4033, d2891, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29805 (p : Pattern) (guard : d5850 p = 1) : d4034 p ≤ (0 : Int) + d2892 p := by
  cases selected : p 71 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d4034, d2892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29433 p hg
    simpa only [d4034, d2892, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d4034, d2892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29804 p hg
    simpa only [d4034, d2892, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29806 (p : Pattern) (guard : d5850 p = 1) : d4035 p ≤ (0 : Int) + d2893 p := by
  cases selected : p 49 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d4035, d2893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29713 p hg
    simpa only [d4035, d2893, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d4035, d2893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29805 p hg
    simpa only [d4035, d2893, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29807 (p : Pattern) (guard : d5850 p = 1) : d4036 p ≤ (0 : Int) + d2894 p := by
  cases selected : p 48 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d4036, d2894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29638 p hg
    simpa only [d4036, d2894, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d4036, d2894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29806 p hg
    simpa only [d4036, d2894, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29808 (p : Pattern) (guard : d5843 p = 1) : d3541 p ≤ (0 : Int) + d14 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29206 p hg
    simpa only [d3541, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29209 p hg
    simpa only [d3541, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29809 (p : Pattern) (guard : d5843 p = 1) : d3542 p ≤ (0 : Int) + d14 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29808 p hg
    simpa only [d3542, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29209 p hg
    simpa only [d3542, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29810 (p : Pattern) (guard : d5843 p = 1) : d3544 p ≤ (0 : Int) + d1771 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3544, d1771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29209 p hg
    simpa only [d3544, d1771, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3544, d1771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29215 p hg
    simpa only [d3544, d1771, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29811 (p : Pattern) (guard : d5843 p = 1) : d3545 p ≤ (0 : Int) + d1772 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3545, d1772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29810 p hg
    simpa only [d3545, d1772, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3545, d1772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29215 p hg
    simpa only [d3545, d1772, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29812 (p : Pattern) (guard : d5843 p = 1) : d3546 p ≤ (0 : Int) + d2895 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3546, d2895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29809 p hg
    simpa only [d3546, d2895, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3546, d2895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29811 p hg
    simpa only [d3546, d2895, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29813 (p : Pattern) (guard : d5843 p = 1) : d3548 p ≤ (0 : Int) + d1685 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3548, d1685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29209 p hg
    simpa only [d3548, d1685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3548, d1685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29222 p hg
    simpa only [d3548, d1685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29814 (p : Pattern) (guard : d5843 p = 1) : d3549 p ≤ (0 : Int) + d1686 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3549, d1686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29813 p hg
    simpa only [d3549, d1686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3549, d1686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29222 p hg
    simpa only [d3549, d1686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29815 (p : Pattern) (guard : d5843 p = 1) : d3550 p ≤ (0 : Int) + d1687 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3550, d1687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29814 p hg
    simpa only [d3550, d1687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3550, d1687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3550, d1687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29816 (p : Pattern) (guard : d5843 p = 1) : d3551 p ≤ (0 : Int) + d2896 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3551, d2896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29812 p hg
    simpa only [d3551, d2896, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3551, d2896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29815 p hg
    simpa only [d3551, d2896, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29817 (p : Pattern) (guard : d5843 p = 1) : d3552 p ≤ (0 : Int) + d2895 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3552, d2895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29209 p hg
    simpa only [d3552, d2895, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3552, d2895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29811 p hg
    simpa only [d3552, d2895, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29818 (p : Pattern) (guard : d5843 p = 1) : d3553 p ≤ (0 : Int) + d2896 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3553, d2896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29817 p hg
    simpa only [d3553, d2896, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3553, d2896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29815 p hg
    simpa only [d3553, d2896, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29819 (p : Pattern) (guard : d5843 p = 1) : d3554 p ≤ (0 : Int) + d2896 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29816 p hg
    simpa only [d3554, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29818 p hg
    simpa only [d3554, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
