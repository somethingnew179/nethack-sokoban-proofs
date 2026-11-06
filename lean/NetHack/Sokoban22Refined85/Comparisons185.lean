/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons184
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare25900 (p : Pattern) (guard : d5843 p = 1) : d2896 p ≤ (0 : Int) + d3620 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2896, d3620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25899 p hg
    simpa only [d2896, d3620, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2896, d3620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25829 p hg
    simpa only [d2896, d3620, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25901 (p : Pattern) (guard : d5843 p = 1) : d2029 p ≤ (0 : Int) + d3621 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2029, d3621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19918 p hg
    simpa only [d2029, d3621, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2029, d3621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20575 p hg
    simpa only [d2029, d3621, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25902 (p : Pattern) (guard : d5843 p = 1) : d2030 p ≤ (0 : Int) + d3622 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2030, d3622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25901 p hg
    simpa only [d2030, d3622, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2030, d3622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20575 p hg
    simpa only [d2030, d3622, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25903 (p : Pattern) (guard : d5843 p = 1) : d2922 p ≤ (0 : Int) + d3623 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2922, d3623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19918 p hg
    simpa only [d2922, d3623, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2922, d3623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25902 p hg
    simpa only [d2922, d3623, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25904 (p : Pattern) (guard : d5843 p = 1) : d1744 p ≤ (0 : Int) + d3625 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1744, d3625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19918 p hg
    simpa only [d1744, d3625, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1744, d3625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20624 p hg
    simpa only [d1744, d3625, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25905 (p : Pattern) (guard : d5843 p = 1) : d1745 p ≤ (0 : Int) + d3626 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1745, d3626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25904 p hg
    simpa only [d1745, d3626, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1745, d3626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20624 p hg
    simpa only [d1745, d3626, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25906 (p : Pattern) (guard : d5843 p = 1) : d1746 p ≤ (0 : Int) + d3627 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1746, d3627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25905 p hg
    simpa only [d1746, d3627, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1746, d3627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d1746, d3627, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25907 (p : Pattern) (guard : d5843 p = 1) : d2923 p ≤ (0 : Int) + d3628 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2923, d3628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25903 p hg
    simpa only [d2923, d3628, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2923, d3628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25906 p hg
    simpa only [d2923, d3628, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25908 (p : Pattern) (guard : d5843 p = 1) : d2924 p ≤ (0 : Int) + d3629 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2924, d3629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25900 p hg
    simpa only [d2924, d3629, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2924, d3629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25907 p hg
    simpa only [d2924, d3629, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25909 (p : Pattern) (guard : d5843 p = 1) : d2925 p ≤ (0 : Int) + d3630 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2925, d3630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25840 p hg
    simpa only [d2925, d3630, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2925, d3630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25849 p hg
    simpa only [d2925, d3630, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25910 (p : Pattern) (guard : d5843 p = 1) : d2926 p ≤ (0 : Int) + d3631 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2926, d3631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25908 p hg
    simpa only [d2926, d3631, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2926, d3631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25909 p hg
    simpa only [d2926, d3631, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25911 (p : Pattern) (guard : d5843 p = 1) : d1751 p ≤ (0 : Int) + d3632 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1751, d3632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19993 p hg
    simpa only [d1751, d3632, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1751, d3632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20634 p hg
    simpa only [d1751, d3632, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25912 (p : Pattern) (guard : d5843 p = 1) : d1752 p ≤ (0 : Int) + d3633 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1752, d3633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25911 p hg
    simpa only [d1752, d3633, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1752, d3633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20634 p hg
    simpa only [d1752, d3633, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25913 (p : Pattern) (guard : d5843 p = 1) : d2927 p ≤ (0 : Int) + d3634 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2927, d3634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19993 p hg
    simpa only [d2927, d3634, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2927, d3634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25912 p hg
    simpa only [d2927, d3634, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25914 (p : Pattern) (guard : d5843 p = 1) : d1753 p ≤ (0 : Int) + d3635 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1753, d3635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25912 p hg
    simpa only [d1753, d3635, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1753, d3635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d1753, d3635, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25915 (p : Pattern) (guard : d5843 p = 1) : d2928 p ≤ (0 : Int) + d3636 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2928, d3636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25913 p hg
    simpa only [d2928, d3636, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2928, d3636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25914 p hg
    simpa only [d2928, d3636, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25916 (p : Pattern) (guard : d5843 p = 1) : d2929 p ≤ (0 : Int) + d3637 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2929, d3637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25840 p hg
    simpa only [d2929, d3637, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2929, d3637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25915 p hg
    simpa only [d2929, d3637, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25917 (p : Pattern) (guard : d5843 p = 1) : d2930 p ≤ (0 : Int) + d3638 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2930, d3638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19940 p hg
    simpa only [d2930, d3638, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2930, d3638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25877 p hg
    simpa only [d2930, d3638, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25918 (p : Pattern) (guard : d5843 p = 1) : d2931 p ≤ (0 : Int) + d3639 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2931, d3639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25917 p hg
    simpa only [d2931, d3639, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2931, d3639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25878 p hg
    simpa only [d2931, d3639, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25919 (p : Pattern) (guard : d5843 p = 1) : d2932 p ≤ (0 : Int) + d3640 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2932, d3640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25918 p hg
    simpa only [d2932, d3640, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2932, d3640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d2932, d3640, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25920 (p : Pattern) (guard : d5843 p = 1) : d2933 p ≤ (0 : Int) + d3641 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2933, d3641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25916 p hg
    simpa only [d2933, d3641, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2933, d3641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25919 p hg
    simpa only [d2933, d3641, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25921 (p : Pattern) (guard : d5843 p = 1) : d2934 p ≤ (0 : Int) + d3642 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2934, d3642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25910 p hg
    simpa only [d2934, d3642, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2934, d3642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25920 p hg
    simpa only [d2934, d3642, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25922 (p : Pattern) (guard : d5843 p = 1) : d2935 p ≤ (0 : Int) + d3643 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2935, d3643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19918 p hg
    simpa only [d2935, d3643, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2935, d3643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25866 p hg
    simpa only [d2935, d3643, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25923 (p : Pattern) (guard : d5843 p = 1) : d2936 p ≤ (0 : Int) + d3644 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2936, d3644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25922 p hg
    simpa only [d2936, d3644, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2936, d3644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d2936, d3644, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25924 (p : Pattern) (guard : d5843 p = 1) : d2937 p ≤ (0 : Int) + d3645 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2937, d3645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25874 p hg
    simpa only [d2937, d3645, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2937, d3645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25923 p hg
    simpa only [d2937, d3645, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25925 (p : Pattern) (guard : d5843 p = 1) : d2938 p ≤ (0 : Int) + d3646 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2938, d3646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25887 p hg
    simpa only [d2938, d3646, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2938, d3646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25892 p hg
    simpa only [d2938, d3646, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25926 (p : Pattern) (guard : d5843 p = 1) : d2939 p ≤ (0 : Int) + d3647 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2939, d3647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25924 p hg
    simpa only [d2939, d3647, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2939, d3647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25925 p hg
    simpa only [d2939, d3647, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25927 (p : Pattern) (guard : d5843 p = 1) : d2940 p ≤ (0 : Int) + d3648 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2940, d3648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25913 p hg
    simpa only [d2940, d3648, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2940, d3648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d2940, d3648, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25928 (p : Pattern) (guard : d5843 p = 1) : d2941 p ≤ (0 : Int) + d3649 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2941, d3649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25887 p hg
    simpa only [d2941, d3649, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2941, d3649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25927 p hg
    simpa only [d2941, d3649, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25929 (p : Pattern) (guard : d5843 p = 1) : d2942 p ≤ (0 : Int) + d3650 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2942, d3650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25917 p hg
    simpa only [d2942, d3650, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2942, d3650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d2942, d3650, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25930 (p : Pattern) (guard : d5843 p = 1) : d2943 p ≤ (0 : Int) + d3651 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2943, d3651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25929 p hg
    simpa only [d2943, d3651, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2943, d3651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d2943, d3651, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25931 (p : Pattern) (guard : d5843 p = 1) : d2944 p ≤ (0 : Int) + d3652 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2944, d3652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25928 p hg
    simpa only [d2944, d3652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2944, d3652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25930 p hg
    simpa only [d2944, d3652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25932 (p : Pattern) (guard : d5843 p = 1) : d2945 p ≤ (0 : Int) + d3653 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2945, d3653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25926 p hg
    simpa only [d2945, d3653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2945, d3653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25931 p hg
    simpa only [d2945, d3653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25933 (p : Pattern) (guard : d5843 p = 1) : d2946 p ≤ (0 : Int) + d3654 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2946, d3654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25921 p hg
    simpa only [d2946, d3654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2946, d3654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25932 p hg
    simpa only [d2946, d3654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25934 (p : Pattern) (guard : d5843 p = 1) : d2947 p ≤ (0 : Int) + d3655 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2947, d3655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25896 p hg
    simpa only [d2947, d3655, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2947, d3655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25933 p hg
    simpa only [d2947, d3655, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25935 (p : Pattern) (guard : d5843 p = 1) : d2047 p ≤ (0 : Int) + d3656 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2047, d3656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20514 p hg
    simpa only [d2047, d3656, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2047, d3656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25854 p hg
    simpa only [d2047, d3656, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25936 (p : Pattern) (guard : d5843 p = 1) : d2048 p ≤ (0 : Int) + d3657 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2048, d3657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25855 p hg
    simpa only [d2048, d3657, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2048, d3657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25935 p hg
    simpa only [d2048, d3657, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25937 (p : Pattern) (guard : d5843 p = 1) : d2948 p ≤ (0 : Int) + d3658 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2948, d3658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19834 p hg
    simpa only [d2948, d3658, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2948, d3658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25936 p hg
    simpa only [d2948, d3658, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25938 (p : Pattern) (guard : d5843 p = 1) : d1773 p ≤ (0 : Int) + d3659 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1773, d3659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25824 p hg
    simpa only [d1773, d3659, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1773, d3659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d1773, d3659, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25939 (p : Pattern) (guard : d5843 p = 1) : d2949 p ≤ (0 : Int) + d3660 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2949, d3660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25937 p hg
    simpa only [d2949, d3660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2949, d3660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25938 p hg
    simpa only [d2949, d3660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25940 (p : Pattern) (guard : d5843 p = 1) : d2051 p ≤ (0 : Int) + d13 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d2051, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1086 p hg
    simpa only [d5843, d2051, d13, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d2051, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19990 p hg
    simpa only [d5843, d2051, d13, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25941 (p : Pattern) (guard : d5843 p = 1) : d2052 p ≤ (0 : Int) + d3579 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2052, d3579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25940 p hg
    simpa only [d2052, d3579, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2052, d3579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19889 p hg
    simpa only [d2052, d3579, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25942 (p : Pattern) (guard : d5843 p = 1) : d2053 p ≤ (0 : Int) + d3580 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2053, d3580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20514 p hg
    simpa only [d2053, d3580, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2053, d3580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25941 p hg
    simpa only [d2053, d3580, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25943 (p : Pattern) (guard : d5843 p = 1) : d2054 p ≤ (0 : Int) + d3581 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2054, d3581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25855 p hg
    simpa only [d2054, d3581, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2054, d3581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25942 p hg
    simpa only [d2054, d3581, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25944 (p : Pattern) (guard : d5843 p = 1) : d2950 p ≤ (0 : Int) + d3582 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2950, d3582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19834 p hg
    simpa only [d2950, d3582, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2950, d3582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25943 p hg
    simpa only [d2950, d3582, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25945 (p : Pattern) (guard : d5843 p = 1) : d1778 p ≤ (0 : Int) + d13 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d1778, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1086 p hg
    simpa only [d5843, d1778, d13, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d1778, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20376 p hg
    simpa only [d5843, d1778, d13, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25946 (p : Pattern) (guard : d5843 p = 1) : d1779 p ≤ (0 : Int) + d3661 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1779, d3661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25945 p hg
    simpa only [d1779, d3661, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1779, d3661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20378 p hg
    simpa only [d1779, d3661, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25947 (p : Pattern) (guard : d5843 p = 1) : d1780 p ≤ (0 : Int) + d3662 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1780, d3662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20514 p hg
    simpa only [d1780, d3662, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1780, d3662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25946 p hg
    simpa only [d1780, d3662, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25948 (p : Pattern) (guard : d5843 p = 1) : d1781 p ≤ (0 : Int) + d3663 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1781, d3663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25855 p hg
    simpa only [d1781, d3663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1781, d3663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25947 p hg
    simpa only [d1781, d3663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25949 (p : Pattern) (guard : d5843 p = 1) : d1782 p ≤ (0 : Int) + d3664 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1782, d3664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25948 p hg
    simpa only [d1782, d3664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1782, d3664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d1782, d3664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25950 (p : Pattern) (guard : d5843 p = 1) : d2951 p ≤ (0 : Int) + d3665 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2951, d3665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25944 p hg
    simpa only [d2951, d3665, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2951, d3665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25949 p hg
    simpa only [d2951, d3665, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25951 (p : Pattern) (guard : d5843 p = 1) : d2952 p ≤ (0 : Int) + d3666 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2952, d3666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25939 p hg
    simpa only [d2952, d3666, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2952, d3666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25950 p hg
    simpa only [d2952, d3666, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25952 (p : Pattern) (guard : d5843 p = 1) : d1789 p ≤ (0 : Int) + d3667 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1789, d3667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25859 p hg
    simpa only [d1789, d3667, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1789, d3667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d1789, d3667, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25953 (p : Pattern) (guard : d5843 p = 1) : d2953 p ≤ (0 : Int) + d3668 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2953, d3668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25860 p hg
    simpa only [d2953, d3668, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2953, d3668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25952 p hg
    simpa only [d2953, d3668, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25954 (p : Pattern) (guard : d5843 p = 1) : d1798 p ≤ (0 : Int) + d3669 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1798, d3669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25885 p hg
    simpa only [d1798, d3669, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1798, d3669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d1798, d3669, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25955 (p : Pattern) (guard : d5843 p = 1) : d2954 p ≤ (0 : Int) + d3670 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2954, d3670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25886 p hg
    simpa only [d2954, d3670, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2954, d3670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25954 p hg
    simpa only [d2954, d3670, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25956 (p : Pattern) (guard : d5843 p = 1) : d2955 p ≤ (0 : Int) + d3671 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2955, d3671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25953 p hg
    simpa only [d2955, d3671, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2955, d3671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25955 p hg
    simpa only [d2955, d3671, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25957 (p : Pattern) (guard : d5843 p = 1) : d2956 p ≤ (0 : Int) + d3672 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2956, d3672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25951 p hg
    simpa only [d2956, d3672, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2956, d3672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25956 p hg
    simpa only [d2956, d3672, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25958 (p : Pattern) (guard : d5843 p = 1) : d1804 p ≤ (0 : Int) + d3673 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1804, d3673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25844 p hg
    simpa only [d1804, d3673, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1804, d3673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d1804, d3673, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25959 (p : Pattern) (guard : d5843 p = 1) : d2957 p ≤ (0 : Int) + d3674 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2957, d3674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25845 p hg
    simpa only [d2957, d3674, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2957, d3674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25958 p hg
    simpa only [d2957, d3674, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25960 (p : Pattern) (guard : d5843 p = 1) : d2958 p ≤ (0 : Int) + d3675 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2958, d3675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25959 p hg
    simpa only [d2958, d3675, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2958, d3675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d2958, d3675, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25961 (p : Pattern) (guard : d5843 p = 1) : d2959 p ≤ (0 : Int) + d3676 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2959, d3676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25956 p hg
    simpa only [d2959, d3676, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2959, d3676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25960 p hg
    simpa only [d2959, d3676, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25962 (p : Pattern) (guard : d5843 p = 1) : d2960 p ≤ (0 : Int) + d3677 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2960, d3677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25957 p hg
    simpa only [d2960, d3677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2960, d3677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25961 p hg
    simpa only [d2960, d3677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25963 (p : Pattern) (guard : d5843 p = 1) : d2961 p ≤ (0 : Int) + d3678 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2961, d3678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25922 p hg
    simpa only [d2961, d3678, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2961, d3678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25867 p hg
    simpa only [d2961, d3678, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25964 (p : Pattern) (guard : d5843 p = 1) : d2962 p ≤ (0 : Int) + d3679 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2962, d3679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19929 p hg
    simpa only [d2962, d3679, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2962, d3679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25872 p hg
    simpa only [d2962, d3679, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25965 (p : Pattern) (guard : d5843 p = 1) : d2963 p ≤ (0 : Int) + d3680 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2963, d3680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25964 p hg
    simpa only [d2963, d3680, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2963, d3680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25873 p hg
    simpa only [d2963, d3680, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25966 (p : Pattern) (guard : d5843 p = 1) : d2964 p ≤ (0 : Int) + d3681 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2964, d3681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25963 p hg
    simpa only [d2964, d3681, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2964, d3681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25965 p hg
    simpa only [d2964, d3681, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25967 (p : Pattern) (guard : d5843 p = 1) : d2965 p ≤ (0 : Int) + d3682 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2965, d3682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25966 p hg
    simpa only [d2965, d3682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2965, d3682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25919 p hg
    simpa only [d2965, d3682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25968 (p : Pattern) (guard : d5843 p = 1) : d2966 p ≤ (0 : Int) + d3683 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2966, d3683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25967 p hg
    simpa only [d2966, d3683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2966, d3683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d2966, d3683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25969 (p : Pattern) (guard : d5843 p = 1) : d2967 p ≤ (0 : Int) + d3684 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2967, d3684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25962 p hg
    simpa only [d2967, d3684, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2967, d3684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25968 p hg
    simpa only [d2967, d3684, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25970 (p : Pattern) (guard : d5843 p = 1) : d2968 p ≤ (0 : Int) + d3685 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2968, d3685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25950 p hg
    simpa only [d2968, d3685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2968, d3685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25963 p hg
    simpa only [d2968, d3685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25971 (p : Pattern) (guard : d5843 p = 1) : d2969 p ≤ (0 : Int) + d3686 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2969, d3686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25955 p hg
    simpa only [d2969, d3686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2969, d3686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25959 p hg
    simpa only [d2969, d3686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25972 (p : Pattern) (guard : d5843 p = 1) : d2970 p ≤ (0 : Int) + d3687 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2970, d3687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25970 p hg
    simpa only [d2970, d3687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2970, d3687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25971 p hg
    simpa only [d2970, d3687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25973 (p : Pattern) (guard : d5843 p = 1) : d2971 p ≤ (0 : Int) + d3688 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2971, d3688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25955 p hg
    simpa only [d2971, d3688, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2971, d3688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25915 p hg
    simpa only [d2971, d3688, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25974 (p : Pattern) (guard : d5843 p = 1) : d2972 p ≤ (0 : Int) + d3689 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2972, d3689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25973 p hg
    simpa only [d2972, d3689, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2972, d3689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25919 p hg
    simpa only [d2972, d3689, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25975 (p : Pattern) (guard : d5843 p = 1) : d2973 p ≤ (0 : Int) + d3690 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2973, d3690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25972 p hg
    simpa only [d2973, d3690, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2973, d3690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25974 p hg
    simpa only [d2973, d3690, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25976 (p : Pattern) (guard : d5843 p = 1) : d2974 p ≤ (0 : Int) + d3691 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2974, d3691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25965 p hg
    simpa only [d2974, d3691, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2974, d3691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d2974, d3691, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25977 (p : Pattern) (guard : d5843 p = 1) : d2975 p ≤ (0 : Int) + d3692 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2975, d3692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25976 p hg
    simpa only [d2975, d3692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2975, d3692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d2975, d3692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25978 (p : Pattern) (guard : d5843 p = 1) : d2976 p ≤ (0 : Int) + d3693 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2976, d3693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25977 p hg
    simpa only [d2976, d3693, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2976, d3693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d2976, d3693, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25979 (p : Pattern) (guard : d5843 p = 1) : d2977 p ≤ (0 : Int) + d3694 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2977, d3694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25975 p hg
    simpa only [d2977, d3694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2977, d3694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25978 p hg
    simpa only [d2977, d3694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25980 (p : Pattern) (guard : d5843 p = 1) : d2978 p ≤ (0 : Int) + d3695 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2978, d3695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25969 p hg
    simpa only [d2978, d3695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2978, d3695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25979 p hg
    simpa only [d2978, d3695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25981 (p : Pattern) (guard : d5843 p = 1) : d2979 p ≤ (0 : Int) + d3696 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2979, d3696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25934 p hg
    simpa only [d2979, d3696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2979, d3696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25980 p hg
    simpa only [d2979, d3696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25982 (p : Pattern) (guard : d5843 p = 1) : d2980 p ≤ (0 : Int) + d3697 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2980, d3697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25959 p hg
    simpa only [d2980, d3697, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2980, d3697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25918 p hg
    simpa only [d2980, d3697, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25983 (p : Pattern) (guard : d5843 p = 1) : d2981 p ≤ (0 : Int) + d3698 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2981, d3698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25982 p hg
    simpa only [d2981, d3698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2981, d3698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25919 p hg
    simpa only [d2981, d3698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25984 (p : Pattern) (guard : d5843 p = 1) : d2982 p ≤ (0 : Int) + d3699 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2982, d3699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25919 p hg
    simpa only [d2982, d3699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2982, d3699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d2982, d3699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25985 (p : Pattern) (guard : d5843 p = 1) : d2983 p ≤ (0 : Int) + d3700 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2983, d3700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25983 p hg
    simpa only [d2983, d3700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2983, d3700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25984 p hg
    simpa only [d2983, d3700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25986 (p : Pattern) (guard : d5843 p = 1) : d2984 p ≤ (0 : Int) + d3701 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2984, d3701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25984 p hg
    simpa only [d2984, d3701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2984, d3701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d2984, d3701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25987 (p : Pattern) (guard : d5843 p = 1) : d2985 p ≤ (0 : Int) + d3702 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2985, d3702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25985 p hg
    simpa only [d2985, d3702, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2985, d3702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25986 p hg
    simpa only [d2985, d3702, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25988 (p : Pattern) (guard : d5843 p = 1) : d2986 p ≤ (0 : Int) + d3703 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2986, d3703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25986 p hg
    simpa only [d2986, d3703, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2986, d3703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d2986, d3703, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25989 (p : Pattern) (guard : d5843 p = 1) : d2987 p ≤ (0 : Int) + d3704 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2987, d3704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25987 p hg
    simpa only [d2987, d3704, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2987, d3704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25988 p hg
    simpa only [d2987, d3704, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25990 (p : Pattern) (guard : d5843 p = 1) : d2988 p ≤ (0 : Int) + d3705 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2988, d3705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25980 p hg
    simpa only [d2988, d3705, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2988, d3705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25989 p hg
    simpa only [d2988, d3705, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25991 (p : Pattern) (guard : d5843 p = 1) : d2989 p ≤ (0 : Int) + d3706 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2989, d3706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25981 p hg
    simpa only [d2989, d3706, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2989, d3706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25990 p hg
    simpa only [d2989, d3706, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25992 (p : Pattern) (guard : d5843 p = 1) : d2900 p ≤ (0 : Int) + d3707 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2900, d3707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25832 p hg
    simpa only [d2900, d3707, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2900, d3707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25841 p hg
    simpa only [d2900, d3707, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25993 (p : Pattern) (guard : d5843 p = 1) : d2905 p ≤ (0 : Int) + d3708 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2905, d3708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25992 p hg
    simpa only [d2905, d3708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2905, d3708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25851 p hg
    simpa only [d2905, d3708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25994 (p : Pattern) (guard : d5843 p = 1) : d2921 p ≤ (0 : Int) + d3709 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2921, d3709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25993 p hg
    simpa only [d2921, d3709, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2921, d3709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25895 p hg
    simpa only [d2921, d3709, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25995 (p : Pattern) (guard : d5843 p = 1) : d2924 p ≤ (0 : Int) + d3710 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2924, d3710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25832 p hg
    simpa only [d2924, d3710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2924, d3710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25907 p hg
    simpa only [d2924, d3710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25996 (p : Pattern) (guard : d5843 p = 1) : d2926 p ≤ (0 : Int) + d3711 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2926, d3711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25995 p hg
    simpa only [d2926, d3711, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2926, d3711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25909 p hg
    simpa only [d2926, d3711, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25997 (p : Pattern) (guard : d5843 p = 1) : d2934 p ≤ (0 : Int) + d3712 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2934, d3712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25996 p hg
    simpa only [d2934, d3712, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2934, d3712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25920 p hg
    simpa only [d2934, d3712, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25998 (p : Pattern) (guard : d5843 p = 1) : d2946 p ≤ (0 : Int) + d3713 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2946, d3713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25997 p hg
    simpa only [d2946, d3713, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2946, d3713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25932 p hg
    simpa only [d2946, d3713, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25999 (p : Pattern) (guard : d5843 p = 1) : d2947 p ≤ (0 : Int) + d3714 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2947, d3714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25994 p hg
    simpa only [d2947, d3714, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2947, d3714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25998 p hg
    simpa only [d2947, d3714, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26000 (p : Pattern) (guard : d5843 p = 1) : d2979 p ≤ (0 : Int) + d3715 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2979, d3715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25999 p hg
    simpa only [d2979, d3715, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2979, d3715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25980 p hg
    simpa only [d2979, d3715, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26001 (p : Pattern) (guard : d5843 p = 1) : d2990 p ≤ (0 : Int) + d3716 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2990, d3716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25980 p hg
    simpa only [d2990, d3716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2990, d3716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d2990, d3716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26002 (p : Pattern) (guard : d5843 p = 1) : d2991 p ≤ (0 : Int) + d3717 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2991, d3717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26000 p hg
    simpa only [d2991, d3717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2991, d3717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26001 p hg
    simpa only [d2991, d3717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26003 (p : Pattern) (guard : d5843 p = 1) : d2992 p ≤ (0 : Int) + d3718 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2992, d3718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25991 p hg
    simpa only [d2992, d3718, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2992, d3718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26002 p hg
    simpa only [d2992, d3718, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26004 (p : Pattern) (guard : d5843 p = 1) : d14 p ≤ (0 : Int) + d3720 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20103 p hg
    simpa only [d3720, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19834 p hg
    simpa only [d3720, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26005 (p : Pattern) (guard : d5843 p = 1) : d14 p ≤ (0 : Int) + d3721 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26004 p hg
    simpa only [d3721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19834 p hg
    simpa only [d3721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26006 (p : Pattern) (guard : d5843 p = 1) : d2895 p ≤ (0 : Int) + d3722 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2895, d3722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26005 p hg
    simpa only [d2895, d3722, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2895, d3722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25824 p hg
    simpa only [d2895, d3722, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26007 (p : Pattern) (guard : d5843 p = 1) : d2896 p ≤ (0 : Int) + d3723 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2896, d3723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26006 p hg
    simpa only [d2896, d3723, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2896, d3723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25829 p hg
    simpa only [d2896, d3723, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26008 (p : Pattern) (guard : d5843 p = 1) : d2896 p ≤ (0 : Int) + d3724 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26007 p hg
    simpa only [d3724, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25832 p hg
    simpa only [d3724, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26009 (p : Pattern) (guard : d5843 p = 1) : d2900 p ≤ (0 : Int) + d3725 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2900, d3725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26008 p hg
    simpa only [d2900, d3725, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2900, d3725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25841 p hg
    simpa only [d2900, d3725, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26010 (p : Pattern) (guard : d5843 p = 1) : d2905 p ≤ (0 : Int) + d3726 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2905, d3726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26009 p hg
    simpa only [d2905, d3726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2905, d3726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25851 p hg
    simpa only [d2905, d3726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26011 (p : Pattern) (guard : d5843 p = 1) : d2921 p ≤ (0 : Int) + d3727 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2921, d3727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26010 p hg
    simpa only [d2921, d3727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2921, d3727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25895 p hg
    simpa only [d2921, d3727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26012 (p : Pattern) (guard : d5843 p = 1) : d2947 p ≤ (0 : Int) + d3728 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2947, d3728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26011 p hg
    simpa only [d2947, d3728, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2947, d3728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25998 p hg
    simpa only [d2947, d3728, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26013 (p : Pattern) (guard : d5843 p = 1) : d2979 p ≤ (0 : Int) + d3729 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2979, d3729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26012 p hg
    simpa only [d2979, d3729, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2979, d3729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25980 p hg
    simpa only [d2979, d3729, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26014 (p : Pattern) (guard : d5843 p = 1) : d2989 p ≤ (0 : Int) + d3730 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2989, d3730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26013 p hg
    simpa only [d2989, d3730, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2989, d3730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25990 p hg
    simpa only [d2989, d3730, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26015 (p : Pattern) (guard : d5843 p = 1) : d2992 p ≤ (0 : Int) + d3731 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2992, d3731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26014 p hg
    simpa only [d2992, d3731, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2992, d3731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26002 p hg
    simpa only [d2992, d3731, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26016 (p : Pattern) (guard : d5843 p = 1) : d2992 p ≤ (0 : Int) + d3732 p := by
  cases selected : p 71 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26003 p hg
    simpa only [d3732, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26015 p hg
    simpa only [d3732, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26017 (p : Pattern) (guard : d5843 p = 1) : d103 p ≤ (0 : Int) + d3734 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20133 p hg
    simpa only [d3734, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20140 p hg
    simpa only [d3734, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26018 (p : Pattern) (guard : d5843 p = 1) : d103 p ≤ (0 : Int) + d3735 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26017 p hg
    simpa only [d3735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20140 p hg
    simpa only [d3735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26019 (p : Pattern) (guard : d5843 p = 1) : d1941 p ≤ (0 : Int) + d3737 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1941, d3737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20140 p hg
    simpa only [d1941, d3737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1941, d3737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20755 p hg
    simpa only [d1941, d3737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26020 (p : Pattern) (guard : d5843 p = 1) : d1942 p ≤ (0 : Int) + d3738 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1942, d3738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26019 p hg
    simpa only [d1942, d3738, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1942, d3738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20755 p hg
    simpa only [d1942, d3738, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26021 (p : Pattern) (guard : d5843 p = 1) : d2993 p ≤ (0 : Int) + d3739 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2993, d3739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26018 p hg
    simpa only [d2993, d3739, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2993, d3739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26020 p hg
    simpa only [d2993, d3739, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26022 (p : Pattern) (guard : d5843 p = 1) : d1874 p ≤ (0 : Int) + d3741 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1874, d3741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20140 p hg
    simpa only [d1874, d3741, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1874, d3741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20761 p hg
    simpa only [d1874, d3741, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26023 (p : Pattern) (guard : d5843 p = 1) : d1875 p ≤ (0 : Int) + d3742 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1875, d3742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26022 p hg
    simpa only [d1875, d3742, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1875, d3742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20761 p hg
    simpa only [d1875, d3742, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26024 (p : Pattern) (guard : d5843 p = 1) : d1876 p ≤ (0 : Int) + d3743 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1876, d3743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26023 p hg
    simpa only [d1876, d3743, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1876, d3743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d1876, d3743, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26025 (p : Pattern) (guard : d5843 p = 1) : d2994 p ≤ (0 : Int) + d3744 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2994, d3744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26021 p hg
    simpa only [d2994, d3744, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2994, d3744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26024 p hg
    simpa only [d2994, d3744, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26026 (p : Pattern) (guard : d5843 p = 1) : d2993 p ≤ (0 : Int) + d3745 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2993, d3745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20140 p hg
    simpa only [d2993, d3745, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2993, d3745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26020 p hg
    simpa only [d2993, d3745, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26027 (p : Pattern) (guard : d5843 p = 1) : d2994 p ≤ (0 : Int) + d3746 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2994, d3746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26026 p hg
    simpa only [d2994, d3746, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2994, d3746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26024 p hg
    simpa only [d2994, d3746, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26028 (p : Pattern) (guard : d5843 p = 1) : d2994 p ≤ (0 : Int) + d3747 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26025 p hg
    simpa only [d3747, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26027 p hg
    simpa only [d3747, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26029 (p : Pattern) (guard : d5843 p = 1) : d2129 p ≤ (0 : Int) + d3749 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2129, d3749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20167 p hg
    simpa only [d2129, d3749, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2129, d3749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20772 p hg
    simpa only [d2129, d3749, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26030 (p : Pattern) (guard : d5843 p = 1) : d2130 p ≤ (0 : Int) + d3750 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2130, d3750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26029 p hg
    simpa only [d2130, d3750, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2130, d3750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20772 p hg
    simpa only [d2130, d3750, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26031 (p : Pattern) (guard : d5843 p = 1) : d2995 p ≤ (0 : Int) + d3751 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2995, d3751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20167 p hg
    simpa only [d2995, d3751, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2995, d3751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26030 p hg
    simpa only [d2995, d3751, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26032 (p : Pattern) (guard : d5843 p = 1) : d1882 p ≤ (0 : Int) + d3753 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1882, d3753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20167 p hg
    simpa only [d1882, d3753, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1882, d3753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20778 p hg
    simpa only [d1882, d3753, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26033 (p : Pattern) (guard : d5843 p = 1) : d1883 p ≤ (0 : Int) + d3754 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1883, d3754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26032 p hg
    simpa only [d1883, d3754, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1883, d3754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20778 p hg
    simpa only [d1883, d3754, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26034 (p : Pattern) (guard : d5843 p = 1) : d1884 p ≤ (0 : Int) + d3755 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1884, d3755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26033 p hg
    simpa only [d1884, d3755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1884, d3755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d1884, d3755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26035 (p : Pattern) (guard : d5843 p = 1) : d2996 p ≤ (0 : Int) + d3756 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2996, d3756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26031 p hg
    simpa only [d2996, d3756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2996, d3756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26034 p hg
    simpa only [d2996, d3756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26036 (p : Pattern) (guard : d5843 p = 1) : d2997 p ≤ (0 : Int) + d3757 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2997, d3757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26027 p hg
    simpa only [d2997, d3757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2997, d3757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26035 p hg
    simpa only [d2997, d3757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26037 (p : Pattern) (guard : d5843 p = 1) : d2998 p ≤ (0 : Int) + d3758 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2998, d3758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26028 p hg
    simpa only [d2998, d3758, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2998, d3758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26036 p hg
    simpa only [d2998, d3758, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26038 (p : Pattern) (guard : d5843 p = 1) : d2999 p ≤ (0 : Int) + d3759 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2999, d3759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25915 p hg
    simpa only [d2999, d3759, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2999, d3759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d2999, d3759, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26039 (p : Pattern) (guard : d5843 p = 1) : d3000 p ≤ (0 : Int) + d3760 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3000, d3760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26036 p hg
    simpa only [d3000, d3760, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3000, d3760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26038 p hg
    simpa only [d3000, d3760, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
