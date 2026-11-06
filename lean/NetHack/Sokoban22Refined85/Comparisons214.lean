/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons213
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare29960 (p : Pattern) (guard : d5843 p = 1) : d3692 p ≤ (0 : Int) + d2975 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3692, d2975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29959 p hg
    simpa only [d3692, d2975, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3692, d2975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3692, d2975, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29961 (p : Pattern) (guard : d5843 p = 1) : d3693 p ≤ (0 : Int) + d2976 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3693, d2976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29960 p hg
    simpa only [d3693, d2976, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3693, d2976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3693, d2976, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29962 (p : Pattern) (guard : d5843 p = 1) : d3694 p ≤ (0 : Int) + d2977 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3694, d2977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29958 p hg
    simpa only [d3694, d2977, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3694, d2977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29961 p hg
    simpa only [d3694, d2977, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29963 (p : Pattern) (guard : d5843 p = 1) : d3695 p ≤ (0 : Int) + d2978 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3695, d2978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29952 p hg
    simpa only [d3695, d2978, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3695, d2978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29962 p hg
    simpa only [d3695, d2978, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29964 (p : Pattern) (guard : d5843 p = 1) : d3696 p ≤ (0 : Int) + d2979 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3696, d2979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29917 p hg
    simpa only [d3696, d2979, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3696, d2979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29963 p hg
    simpa only [d3696, d2979, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29965 (p : Pattern) (guard : d5843 p = 1) : d3697 p ≤ (0 : Int) + d2980 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3697, d2980, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29942 p hg
    simpa only [d3697, d2980, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3697, d2980, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29901 p hg
    simpa only [d3697, d2980, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29966 (p : Pattern) (guard : d5843 p = 1) : d3698 p ≤ (0 : Int) + d2981 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3698, d2981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29965 p hg
    simpa only [d3698, d2981, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3698, d2981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29902 p hg
    simpa only [d3698, d2981, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29967 (p : Pattern) (guard : d5843 p = 1) : d3699 p ≤ (0 : Int) + d2982 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3699, d2982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29902 p hg
    simpa only [d3699, d2982, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3699, d2982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3699, d2982, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29968 (p : Pattern) (guard : d5843 p = 1) : d3700 p ≤ (0 : Int) + d2983 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3700, d2983, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29966 p hg
    simpa only [d3700, d2983, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3700, d2983, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29967 p hg
    simpa only [d3700, d2983, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29969 (p : Pattern) (guard : d5843 p = 1) : d3701 p ≤ (0 : Int) + d2984 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3701, d2984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29967 p hg
    simpa only [d3701, d2984, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3701, d2984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3701, d2984, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29970 (p : Pattern) (guard : d5843 p = 1) : d3702 p ≤ (0 : Int) + d2985 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3702, d2985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29968 p hg
    simpa only [d3702, d2985, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3702, d2985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29969 p hg
    simpa only [d3702, d2985, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29971 (p : Pattern) (guard : d5843 p = 1) : d3703 p ≤ (0 : Int) + d2986 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3703, d2986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29969 p hg
    simpa only [d3703, d2986, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3703, d2986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3703, d2986, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29972 (p : Pattern) (guard : d5843 p = 1) : d3704 p ≤ (0 : Int) + d2987 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3704, d2987, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29970 p hg
    simpa only [d3704, d2987, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3704, d2987, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29971 p hg
    simpa only [d3704, d2987, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29973 (p : Pattern) (guard : d5843 p = 1) : d3705 p ≤ (0 : Int) + d2988 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3705, d2988, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29963 p hg
    simpa only [d3705, d2988, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3705, d2988, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29972 p hg
    simpa only [d3705, d2988, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29974 (p : Pattern) (guard : d5843 p = 1) : d3706 p ≤ (0 : Int) + d2989 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3706, d2989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29964 p hg
    simpa only [d3706, d2989, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3706, d2989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29973 p hg
    simpa only [d3706, d2989, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29975 (p : Pattern) (guard : d5843 p = 1) : d3707 p ≤ (0 : Int) + d2900 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3707, d2900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29818 p hg
    simpa only [d3707, d2900, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3707, d2900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29827 p hg
    simpa only [d3707, d2900, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29976 (p : Pattern) (guard : d5843 p = 1) : d3708 p ≤ (0 : Int) + d2905 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3708, d2905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29975 p hg
    simpa only [d3708, d2905, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3708, d2905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29837 p hg
    simpa only [d3708, d2905, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29977 (p : Pattern) (guard : d5843 p = 1) : d3709 p ≤ (0 : Int) + d2921 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3709, d2921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29976 p hg
    simpa only [d3709, d2921, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3709, d2921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29878 p hg
    simpa only [d3709, d2921, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29978 (p : Pattern) (guard : d5843 p = 1) : d3710 p ≤ (0 : Int) + d2924 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3710, d2924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29818 p hg
    simpa only [d3710, d2924, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3710, d2924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29890 p hg
    simpa only [d3710, d2924, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29979 (p : Pattern) (guard : d5843 p = 1) : d3711 p ≤ (0 : Int) + d2926 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3711, d2926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29978 p hg
    simpa only [d3711, d2926, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3711, d2926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29892 p hg
    simpa only [d3711, d2926, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29980 (p : Pattern) (guard : d5843 p = 1) : d3712 p ≤ (0 : Int) + d2934 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3712, d2934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29979 p hg
    simpa only [d3712, d2934, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3712, d2934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29903 p hg
    simpa only [d3712, d2934, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29981 (p : Pattern) (guard : d5843 p = 1) : d3713 p ≤ (0 : Int) + d2946 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3713, d2946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29980 p hg
    simpa only [d3713, d2946, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3713, d2946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29915 p hg
    simpa only [d3713, d2946, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29982 (p : Pattern) (guard : d5843 p = 1) : d3714 p ≤ (0 : Int) + d2947 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3714, d2947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29977 p hg
    simpa only [d3714, d2947, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3714, d2947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29981 p hg
    simpa only [d3714, d2947, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29983 (p : Pattern) (guard : d5843 p = 1) : d3715 p ≤ (0 : Int) + d2979 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3715, d2979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29982 p hg
    simpa only [d3715, d2979, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3715, d2979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29963 p hg
    simpa only [d3715, d2979, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29984 (p : Pattern) (guard : d5843 p = 1) : d3716 p ≤ (0 : Int) + d2990 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3716, d2990, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29963 p hg
    simpa only [d3716, d2990, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3716, d2990, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3716, d2990, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29985 (p : Pattern) (guard : d5843 p = 1) : d3717 p ≤ (0 : Int) + d2991 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3717, d2991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29983 p hg
    simpa only [d3717, d2991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3717, d2991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29984 p hg
    simpa only [d3717, d2991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29986 (p : Pattern) (guard : d5843 p = 1) : d3718 p ≤ (0 : Int) + d2992 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3718, d2992, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29974 p hg
    simpa only [d3718, d2992, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3718, d2992, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29985 p hg
    simpa only [d3718, d2992, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29987 (p : Pattern) (guard : d5843 p = 1) : d3720 p ≤ (0 : Int) + d14 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29436 p hg
    simpa only [d3720, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29209 p hg
    simpa only [d3720, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29988 (p : Pattern) (guard : d5843 p = 1) : d3721 p ≤ (0 : Int) + d14 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29987 p hg
    simpa only [d3721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29209 p hg
    simpa only [d3721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29989 (p : Pattern) (guard : d5843 p = 1) : d3722 p ≤ (0 : Int) + d2895 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3722, d2895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29988 p hg
    simpa only [d3722, d2895, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3722, d2895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29811 p hg
    simpa only [d3722, d2895, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29990 (p : Pattern) (guard : d5843 p = 1) : d3723 p ≤ (0 : Int) + d2896 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3723, d2896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29989 p hg
    simpa only [d3723, d2896, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3723, d2896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29815 p hg
    simpa only [d3723, d2896, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29991 (p : Pattern) (guard : d5843 p = 1) : d3724 p ≤ (0 : Int) + d2896 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29990 p hg
    simpa only [d3724, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29818 p hg
    simpa only [d3724, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29992 (p : Pattern) (guard : d5843 p = 1) : d3725 p ≤ (0 : Int) + d2900 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3725, d2900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29991 p hg
    simpa only [d3725, d2900, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3725, d2900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29827 p hg
    simpa only [d3725, d2900, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29993 (p : Pattern) (guard : d5843 p = 1) : d3726 p ≤ (0 : Int) + d2905 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3726, d2905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29992 p hg
    simpa only [d3726, d2905, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3726, d2905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29837 p hg
    simpa only [d3726, d2905, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29994 (p : Pattern) (guard : d5843 p = 1) : d3727 p ≤ (0 : Int) + d2921 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3727, d2921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29993 p hg
    simpa only [d3727, d2921, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3727, d2921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29878 p hg
    simpa only [d3727, d2921, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29995 (p : Pattern) (guard : d5843 p = 1) : d3728 p ≤ (0 : Int) + d2947 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3728, d2947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29994 p hg
    simpa only [d3728, d2947, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3728, d2947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29981 p hg
    simpa only [d3728, d2947, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29996 (p : Pattern) (guard : d5843 p = 1) : d3729 p ≤ (0 : Int) + d2979 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3729, d2979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29995 p hg
    simpa only [d3729, d2979, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3729, d2979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29963 p hg
    simpa only [d3729, d2979, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29997 (p : Pattern) (guard : d5843 p = 1) : d3730 p ≤ (0 : Int) + d2989 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3730, d2989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29996 p hg
    simpa only [d3730, d2989, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3730, d2989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29973 p hg
    simpa only [d3730, d2989, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29998 (p : Pattern) (guard : d5843 p = 1) : d3731 p ≤ (0 : Int) + d2992 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3731, d2992, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29997 p hg
    simpa only [d3731, d2992, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3731, d2992, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29985 p hg
    simpa only [d3731, d2992, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29999 (p : Pattern) (guard : d5843 p = 1) : d3732 p ≤ (0 : Int) + d2992 p := by
  cases selected : p 71 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29986 p hg
    simpa only [d3732, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29998 p hg
    simpa only [d3732, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30000 (p : Pattern) (guard : d5843 p = 1) : d3734 p ≤ (0 : Int) + d103 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29463 p hg
    simpa only [d3734, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29466 p hg
    simpa only [d3734, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30001 (p : Pattern) (guard : d5843 p = 1) : d3735 p ≤ (0 : Int) + d103 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30000 p hg
    simpa only [d3735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29466 p hg
    simpa only [d3735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30002 (p : Pattern) (guard : d5843 p = 1) : d3737 p ≤ (0 : Int) + d1941 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3737, d1941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29466 p hg
    simpa only [d3737, d1941, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3737, d1941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29472 p hg
    simpa only [d3737, d1941, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30003 (p : Pattern) (guard : d5843 p = 1) : d3738 p ≤ (0 : Int) + d1942 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3738, d1942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30002 p hg
    simpa only [d3738, d1942, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3738, d1942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29472 p hg
    simpa only [d3738, d1942, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30004 (p : Pattern) (guard : d5843 p = 1) : d3739 p ≤ (0 : Int) + d2993 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3739, d2993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30001 p hg
    simpa only [d3739, d2993, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3739, d2993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30003 p hg
    simpa only [d3739, d2993, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30005 (p : Pattern) (guard : d5843 p = 1) : d3741 p ≤ (0 : Int) + d1874 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3741, d1874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29466 p hg
    simpa only [d3741, d1874, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3741, d1874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29479 p hg
    simpa only [d3741, d1874, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30006 (p : Pattern) (guard : d5843 p = 1) : d3742 p ≤ (0 : Int) + d1875 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3742, d1875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30005 p hg
    simpa only [d3742, d1875, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3742, d1875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29479 p hg
    simpa only [d3742, d1875, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30007 (p : Pattern) (guard : d5843 p = 1) : d3743 p ≤ (0 : Int) + d1876 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3743, d1876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30006 p hg
    simpa only [d3743, d1876, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3743, d1876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3743, d1876, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30008 (p : Pattern) (guard : d5843 p = 1) : d3744 p ≤ (0 : Int) + d2994 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3744, d2994, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30004 p hg
    simpa only [d3744, d2994, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3744, d2994, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30007 p hg
    simpa only [d3744, d2994, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30009 (p : Pattern) (guard : d5843 p = 1) : d3745 p ≤ (0 : Int) + d2993 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3745, d2993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29466 p hg
    simpa only [d3745, d2993, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3745, d2993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30003 p hg
    simpa only [d3745, d2993, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30010 (p : Pattern) (guard : d5843 p = 1) : d3746 p ≤ (0 : Int) + d2994 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3746, d2994, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30009 p hg
    simpa only [d3746, d2994, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3746, d2994, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30007 p hg
    simpa only [d3746, d2994, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30011 (p : Pattern) (guard : d5843 p = 1) : d3747 p ≤ (0 : Int) + d2994 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30008 p hg
    simpa only [d3747, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30010 p hg
    simpa only [d3747, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30012 (p : Pattern) (guard : d5843 p = 1) : d3749 p ≤ (0 : Int) + d2129 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3749, d2129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29487 p hg
    simpa only [d3749, d2129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3749, d2129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29492 p hg
    simpa only [d3749, d2129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30013 (p : Pattern) (guard : d5843 p = 1) : d3750 p ≤ (0 : Int) + d2130 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3750, d2130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30012 p hg
    simpa only [d3750, d2130, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3750, d2130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29492 p hg
    simpa only [d3750, d2130, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30014 (p : Pattern) (guard : d5843 p = 1) : d3751 p ≤ (0 : Int) + d2995 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3751, d2995, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29487 p hg
    simpa only [d3751, d2995, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3751, d2995, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30013 p hg
    simpa only [d3751, d2995, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30015 (p : Pattern) (guard : d5843 p = 1) : d3753 p ≤ (0 : Int) + d1882 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3753, d1882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29487 p hg
    simpa only [d3753, d1882, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3753, d1882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29499 p hg
    simpa only [d3753, d1882, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30016 (p : Pattern) (guard : d5843 p = 1) : d3754 p ≤ (0 : Int) + d1883 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3754, d1883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30015 p hg
    simpa only [d3754, d1883, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3754, d1883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29499 p hg
    simpa only [d3754, d1883, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30017 (p : Pattern) (guard : d5843 p = 1) : d3755 p ≤ (0 : Int) + d1884 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3755, d1884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30016 p hg
    simpa only [d3755, d1884, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3755, d1884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3755, d1884, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30018 (p : Pattern) (guard : d5843 p = 1) : d3756 p ≤ (0 : Int) + d2996 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3756, d2996, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30014 p hg
    simpa only [d3756, d2996, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3756, d2996, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30017 p hg
    simpa only [d3756, d2996, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30019 (p : Pattern) (guard : d5843 p = 1) : d3757 p ≤ (0 : Int) + d2997 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3757, d2997, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30010 p hg
    simpa only [d3757, d2997, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3757, d2997, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30018 p hg
    simpa only [d3757, d2997, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30020 (p : Pattern) (guard : d5843 p = 1) : d3758 p ≤ (0 : Int) + d2998 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3758, d2998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30011 p hg
    simpa only [d3758, d2998, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3758, d2998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30019 p hg
    simpa only [d3758, d2998, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30021 (p : Pattern) (guard : d5843 p = 1) : d3759 p ≤ (0 : Int) + d2999 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3759, d2999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29898 p hg
    simpa only [d3759, d2999, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3759, d2999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3759, d2999, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30022 (p : Pattern) (guard : d5843 p = 1) : d3760 p ≤ (0 : Int) + d3000 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3760, d3000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30019 p hg
    simpa only [d3760, d3000, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3760, d3000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30021 p hg
    simpa only [d3760, d3000, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30023 (p : Pattern) (guard : d5843 p = 1) : d3761 p ≤ (0 : Int) + d3001 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3761, d3001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30020 p hg
    simpa only [d3761, d3001, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3761, d3001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30022 p hg
    simpa only [d3761, d3001, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30024 (p : Pattern) (guard : d5843 p = 1) : d102 p ≤ (0 : Int) + d1945 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d102, d1945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14646 p hg
    simpa only [d5843, d102, d1945, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d102, d1945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26453 p hg
    simpa only [d5843, d102, d1945, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30025 (p : Pattern) (guard : d5843 p = 1) : d3762 p ≤ (0 : Int) + d1946 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3762, d1946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30024 p hg
    simpa only [d3762, d1946, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3762, d1946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20209 p hg
    simpa only [d3762, d1946, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30026 (p : Pattern) (guard : d5843 p = 1) : d3763 p ≤ (0 : Int) + d1947 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3763, d1947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29466 p hg
    simpa only [d3763, d1947, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3763, d1947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30025 p hg
    simpa only [d3763, d1947, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30027 (p : Pattern) (guard : d5843 p = 1) : d3764 p ≤ (0 : Int) + d1956 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3764, d1956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29472 p hg
    simpa only [d3764, d1956, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3764, d1956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26044 p hg
    simpa only [d3764, d1956, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30028 (p : Pattern) (guard : d5843 p = 1) : d3765 p ≤ (0 : Int) + d1957 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3765, d1957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30026 p hg
    simpa only [d3765, d1957, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3765, d1957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30027 p hg
    simpa only [d3765, d1957, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30029 (p : Pattern) (guard : d5843 p = 1) : d3766 p ≤ (0 : Int) + d3002 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3766, d3002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29466 p hg
    simpa only [d3766, d3002, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3766, d3002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30028 p hg
    simpa only [d3766, d3002, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30030 (p : Pattern) (guard : d5843 p = 1) : d115 p ≤ (0 : Int) + d1891 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d115, d1891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14667 p hg
    simpa only [d5843, d115, d1891, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d115, d1891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23417 p hg
    simpa only [d5843, d115, d1891, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30031 (p : Pattern) (guard : d5843 p = 1) : d3767 p ≤ (0 : Int) + d1892 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3767, d1892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30030 p hg
    simpa only [d3767, d1892, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3767, d1892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19889 p hg
    simpa only [d3767, d1892, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30032 (p : Pattern) (guard : d5843 p = 1) : d3768 p ≤ (0 : Int) + d1893 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3768, d1893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29514 p hg
    simpa only [d3768, d1893, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3768, d1893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30031 p hg
    simpa only [d3768, d1893, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30033 (p : Pattern) (guard : d5843 p = 1) : d3770 p ≤ (0 : Int) + d1897 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3770, d1897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29518 p hg
    simpa only [d3770, d1897, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3770, d1897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26051 p hg
    simpa only [d3770, d1897, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30034 (p : Pattern) (guard : d5843 p = 1) : d3771 p ≤ (0 : Int) + d1898 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3771, d1898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30032 p hg
    simpa only [d3771, d1898, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3771, d1898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30033 p hg
    simpa only [d3771, d1898, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30035 (p : Pattern) (guard : d5843 p = 1) : d3772 p ≤ (0 : Int) + d1899 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3772, d1899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30034 p hg
    simpa only [d3772, d1899, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3772, d1899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3772, d1899, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30036 (p : Pattern) (guard : d5843 p = 1) : d3773 p ≤ (0 : Int) + d3003 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3773, d3003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30029 p hg
    simpa only [d3773, d3003, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3773, d3003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30035 p hg
    simpa only [d3773, d3003, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30037 (p : Pattern) (guard : d5843 p = 1) : d3774 p ≤ (0 : Int) + d1901 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3774, d1901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29523 p hg
    simpa only [d3774, d1901, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3774, d1901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26056 p hg
    simpa only [d3774, d1901, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30038 (p : Pattern) (guard : d5843 p = 1) : d3776 p ≤ (0 : Int) + d1904 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3776, d1904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29526 p hg
    simpa only [d3776, d1904, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3776, d1904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26056 p hg
    simpa only [d3776, d1904, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30039 (p : Pattern) (guard : d5843 p = 1) : d3777 p ≤ (0 : Int) + d1905 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3777, d1905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30037 p hg
    simpa only [d3777, d1905, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3777, d1905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30038 p hg
    simpa only [d3777, d1905, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30040 (p : Pattern) (guard : d5843 p = 1) : d3778 p ≤ (0 : Int) + d1906 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3778, d1906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30039 p hg
    simpa only [d3778, d1906, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3778, d1906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3778, d1906, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30041 (p : Pattern) (guard : d5843 p = 1) : d3779 p ≤ (0 : Int) + d3004 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3779, d3004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30029 p hg
    simpa only [d3779, d3004, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3779, d3004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30040 p hg
    simpa only [d3779, d3004, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30042 (p : Pattern) (guard : d5843 p = 1) : d3780 p ≤ (0 : Int) + d3005 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3780, d3005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30036 p hg
    simpa only [d3780, d3005, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3780, d3005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30041 p hg
    simpa only [d3780, d3005, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30043 (p : Pattern) (guard : d5843 p = 1) : d3781 p ≤ (0 : Int) + d3006 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3781, d3006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30029 p hg
    simpa only [d3781, d3006, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3781, d3006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3781, d3006, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30044 (p : Pattern) (guard : d5843 p = 1) : d106 p ≤ (0 : Int) + d1960 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d106, d1960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14654 p hg
    simpa only [d5843, d106, d1960, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d106, d1960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23451 p hg
    simpa only [d5843, d106, d1960, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30045 (p : Pattern) (guard : d5843 p = 1) : d3782 p ≤ (0 : Int) + d1961 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3782, d1961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30044 p hg
    simpa only [d3782, d1961, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3782, d1961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19939 p hg
    simpa only [d3782, d1961, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30046 (p : Pattern) (guard : d5843 p = 1) : d3783 p ≤ (0 : Int) + d1962 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3783, d1962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29487 p hg
    simpa only [d3783, d1962, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3783, d1962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30045 p hg
    simpa only [d3783, d1962, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30047 (p : Pattern) (guard : d5843 p = 1) : d3784 p ≤ (0 : Int) + d1965 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3784, d1965, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29492 p hg
    simpa only [d3784, d1965, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3784, d1965, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26067 p hg
    simpa only [d3784, d1965, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30048 (p : Pattern) (guard : d5843 p = 1) : d3785 p ≤ (0 : Int) + d1966 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3785, d1966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30046 p hg
    simpa only [d3785, d1966, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3785, d1966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30047 p hg
    simpa only [d3785, d1966, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30049 (p : Pattern) (guard : d5843 p = 1) : d3786 p ≤ (0 : Int) + d3007 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3786, d3007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29487 p hg
    simpa only [d3786, d3007, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3786, d3007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30048 p hg
    simpa only [d3786, d3007, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30050 (p : Pattern) (guard : d5843 p = 1) : d3787 p ≤ (0 : Int) + d3008 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3787, d3008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30049 p hg
    simpa only [d3787, d3008, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3787, d3008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3787, d3008, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30051 (p : Pattern) (guard : d5843 p = 1) : d3788 p ≤ (0 : Int) + d3009 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3788, d3009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30043 p hg
    simpa only [d3788, d3009, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3788, d3009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30050 p hg
    simpa only [d3788, d3009, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30052 (p : Pattern) (guard : d5843 p = 1) : d3789 p ≤ (0 : Int) + d3010 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3789, d3010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30042 p hg
    simpa only [d3789, d3010, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3789, d3010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30051 p hg
    simpa only [d3789, d3010, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30053 (p : Pattern) (guard : d5843 p = 1) : d3790 p ≤ (0 : Int) + d3011 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3790, d3011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29910 p hg
    simpa only [d3790, d3011, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3790, d3011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3790, d3011, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30054 (p : Pattern) (guard : d5843 p = 1) : d3791 p ≤ (0 : Int) + d3012 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3791, d3012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30051 p hg
    simpa only [d3791, d3012, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3791, d3012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30053 p hg
    simpa only [d3791, d3012, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30055 (p : Pattern) (guard : d5843 p = 1) : d3792 p ≤ (0 : Int) + d3013 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3792, d3013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30052 p hg
    simpa only [d3792, d3013, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3792, d3013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30054 p hg
    simpa only [d3792, d3013, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30056 (p : Pattern) (guard : d5843 p = 1) : d3793 p ≤ (0 : Int) + d3014 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3793, d3014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30023 p hg
    simpa only [d3793, d3014, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3793, d3014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30055 p hg
    simpa only [d3793, d3014, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30057 (p : Pattern) (guard : d5843 p = 1) : d3794 p ≤ (0 : Int) + d2124 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3794, d2124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29514 p hg
    simpa only [d3794, d2124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3794, d2124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29518 p hg
    simpa only [d3794, d2124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30058 (p : Pattern) (guard : d5843 p = 1) : d3795 p ≤ (0 : Int) + d2125 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3795, d2125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30057 p hg
    simpa only [d3795, d2125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3795, d2125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29518 p hg
    simpa only [d3795, d2125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30059 (p : Pattern) (guard : d5843 p = 1) : d3796 p ≤ (0 : Int) + d3015 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3796, d3015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29514 p hg
    simpa only [d3796, d3015, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3796, d3015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30058 p hg
    simpa only [d3796, d3015, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30060 (p : Pattern) (guard : d5843 p = 1) : d3798 p ≤ (0 : Int) + d1920 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3798, d1920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29514 p hg
    simpa only [d3798, d1920, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3798, d1920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29559 p hg
    simpa only [d3798, d1920, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30061 (p : Pattern) (guard : d5843 p = 1) : d3799 p ≤ (0 : Int) + d1921 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3799, d1921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30060 p hg
    simpa only [d3799, d1921, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3799, d1921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29559 p hg
    simpa only [d3799, d1921, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30062 (p : Pattern) (guard : d5843 p = 1) : d3800 p ≤ (0 : Int) + d1922 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3800, d1922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30061 p hg
    simpa only [d3800, d1922, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3800, d1922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3800, d1922, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30063 (p : Pattern) (guard : d5843 p = 1) : d3801 p ≤ (0 : Int) + d3016 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3801, d3016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30059 p hg
    simpa only [d3801, d3016, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3801, d3016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30062 p hg
    simpa only [d3801, d3016, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30064 (p : Pattern) (guard : d5843 p = 1) : d3802 p ≤ (0 : Int) + d3017 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3802, d3017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30010 p hg
    simpa only [d3802, d3017, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3802, d3017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30063 p hg
    simpa only [d3802, d3017, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30065 (p : Pattern) (guard : d5843 p = 1) : d3803 p ≤ (0 : Int) + d3018 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3803, d3018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30018 p hg
    simpa only [d3803, d3018, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3803, d3018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29898 p hg
    simpa only [d3803, d3018, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30066 (p : Pattern) (guard : d5843 p = 1) : d3804 p ≤ (0 : Int) + d3019 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3804, d3019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30064 p hg
    simpa only [d3804, d3019, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3804, d3019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30065 p hg
    simpa only [d3804, d3019, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30067 (p : Pattern) (guard : d5843 p = 1) : d3805 p ≤ (0 : Int) + d3020 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3805, d3020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30018 p hg
    simpa only [d3805, d3020, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3805, d3020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29901 p hg
    simpa only [d3805, d3020, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30068 (p : Pattern) (guard : d5843 p = 1) : d3806 p ≤ (0 : Int) + d3021 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3806, d3021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30067 p hg
    simpa only [d3806, d3021, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3806, d3021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3806, d3021, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30069 (p : Pattern) (guard : d5843 p = 1) : d3807 p ≤ (0 : Int) + d3022 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3807, d3022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30066 p hg
    simpa only [d3807, d3022, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3807, d3022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30068 p hg
    simpa only [d3807, d3022, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30070 (p : Pattern) (guard : d5843 p = 1) : d3808 p ≤ (0 : Int) + d3023 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3808, d3023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29514 p hg
    simpa only [d3808, d3023, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3808, d3023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30034 p hg
    simpa only [d3808, d3023, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30071 (p : Pattern) (guard : d5843 p = 1) : d3809 p ≤ (0 : Int) + d3024 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3809, d3024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30070 p hg
    simpa only [d3809, d3024, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3809, d3024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3809, d3024, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30072 (p : Pattern) (guard : d5843 p = 1) : d3810 p ≤ (0 : Int) + d3025 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3810, d3025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30041 p hg
    simpa only [d3810, d3025, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3810, d3025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30071 p hg
    simpa only [d3810, d3025, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30073 (p : Pattern) (guard : d5843 p = 1) : d3811 p ≤ (0 : Int) + d3026 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3811, d3026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30050 p hg
    simpa only [d3811, d3026, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3811, d3026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29910 p hg
    simpa only [d3811, d3026, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30074 (p : Pattern) (guard : d5843 p = 1) : d3812 p ≤ (0 : Int) + d3027 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3812, d3027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30072 p hg
    simpa only [d3812, d3027, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3812, d3027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30073 p hg
    simpa only [d3812, d3027, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30075 (p : Pattern) (guard : d5843 p = 1) : d3813 p ≤ (0 : Int) + d3028 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3813, d3028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30050 p hg
    simpa only [d3813, d3028, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3813, d3028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29912 p hg
    simpa only [d3813, d3028, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30076 (p : Pattern) (guard : d5843 p = 1) : d3814 p ≤ (0 : Int) + d3029 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3814, d3029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30075 p hg
    simpa only [d3814, d3029, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3814, d3029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3814, d3029, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30077 (p : Pattern) (guard : d5843 p = 1) : d3815 p ≤ (0 : Int) + d3030 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3815, d3030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30074 p hg
    simpa only [d3815, d3030, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3815, d3030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30076 p hg
    simpa only [d3815, d3030, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30078 (p : Pattern) (guard : d5843 p = 1) : d3816 p ≤ (0 : Int) + d3031 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3816, d3031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30069 p hg
    simpa only [d3816, d3031, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3816, d3031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30077 p hg
    simpa only [d3816, d3031, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30079 (p : Pattern) (guard : d5843 p = 1) : d3817 p ≤ (0 : Int) + d3032 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3817, d3032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30056 p hg
    simpa only [d3817, d3032, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3817, d3032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30078 p hg
    simpa only [d3817, d3032, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30080 (p : Pattern) (guard : d5843 p = 1) : d3818 p ≤ (0 : Int) + d2107 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3818, d2107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29472 p hg
    simpa only [d3818, d2107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3818, d2107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30025 p hg
    simpa only [d3818, d2107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30081 (p : Pattern) (guard : d5843 p = 1) : d3819 p ≤ (0 : Int) + d2108 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3819, d2108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30026 p hg
    simpa only [d3819, d2108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3819, d2108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30080 p hg
    simpa only [d3819, d2108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30082 (p : Pattern) (guard : d5843 p = 1) : d3820 p ≤ (0 : Int) + d3033 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3820, d3033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29466 p hg
    simpa only [d3820, d3033, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3820, d3033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30081 p hg
    simpa only [d3820, d3033, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30083 (p : Pattern) (guard : d5843 p = 1) : d3821 p ≤ (0 : Int) + d1943 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3821, d1943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30003 p hg
    simpa only [d3821, d1943, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3821, d1943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3821, d1943, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30084 (p : Pattern) (guard : d5843 p = 1) : d3822 p ≤ (0 : Int) + d3034 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3822, d3034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30082 p hg
    simpa only [d3822, d3034, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3822, d3034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30083 p hg
    simpa only [d3822, d3034, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30085 (p : Pattern) (guard : d5843 p = 1) : d102 p ≤ (0 : Int) + d3035 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d102, d3035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14646 p hg
    simpa only [d5843, d102, d3035, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d102, d3035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23451 p hg
    simpa only [d5843, d102, d3035, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30086 (p : Pattern) (guard : d5843 p = 1) : d1955 p ≤ (0 : Int) + d3036 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1955, d3036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30085 p hg
    simpa only [d1955, d3036, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1955, d3036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19992 p hg
    simpa only [d1955, d3036, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30087 (p : Pattern) (guard : d5843 p = 1) : d3764 p ≤ (0 : Int) + d3037 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3764, d3037, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29472 p hg
    simpa only [d3764, d3037, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3764, d3037, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30086 p hg
    simpa only [d3764, d3037, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30088 (p : Pattern) (guard : d5843 p = 1) : d3765 p ≤ (0 : Int) + d3038 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3765, d3038, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30026 p hg
    simpa only [d3765, d3038, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3765, d3038, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30087 p hg
    simpa only [d3765, d3038, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30089 (p : Pattern) (guard : d5843 p = 1) : d3766 p ≤ (0 : Int) + d3039 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3766, d3039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29466 p hg
    simpa only [d3766, d3039, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3766, d3039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30088 p hg
    simpa only [d3766, d3039, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30090 (p : Pattern) (guard : d5843 p = 1) : d102 p ≤ (0 : Int) + d1948 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d102, d1948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14646 p hg
    simpa only [d5843, d102, d1948, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d102, d1948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23417 p hg
    simpa only [d5843, d102, d1948, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30091 (p : Pattern) (guard : d5843 p = 1) : d3823 p ≤ (0 : Int) + d1949 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3823, d1949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30090 p hg
    simpa only [d3823, d1949, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3823, d1949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19889 p hg
    simpa only [d3823, d1949, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30092 (p : Pattern) (guard : d5843 p = 1) : d3824 p ≤ (0 : Int) + d1950 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3824, d1950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29472 p hg
    simpa only [d3824, d1950, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3824, d1950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30091 p hg
    simpa only [d3824, d1950, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30093 (p : Pattern) (guard : d5843 p = 1) : d3825 p ≤ (0 : Int) + d1951 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3825, d1951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30026 p hg
    simpa only [d3825, d1951, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3825, d1951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30092 p hg
    simpa only [d3825, d1951, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30094 (p : Pattern) (guard : d5843 p = 1) : d3826 p ≤ (0 : Int) + d1952 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3826, d1952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30093 p hg
    simpa only [d3826, d1952, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3826, d1952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3826, d1952, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30095 (p : Pattern) (guard : d5843 p = 1) : d3827 p ≤ (0 : Int) + d3040 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3827, d3040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30089 p hg
    simpa only [d3827, d3040, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3827, d3040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30094 p hg
    simpa only [d3827, d3040, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30096 (p : Pattern) (guard : d5843 p = 1) : d3828 p ≤ (0 : Int) + d3041 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3828, d3041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30084 p hg
    simpa only [d3828, d3041, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3828, d3041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30095 p hg
    simpa only [d3828, d3041, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30097 (p : Pattern) (guard : d5843 p = 1) : d3829 p ≤ (0 : Int) + d1958 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3829, d1958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30028 p hg
    simpa only [d3829, d1958, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3829, d1958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3829, d1958, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30098 (p : Pattern) (guard : d5843 p = 1) : d3830 p ≤ (0 : Int) + d3042 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3830, d3042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30029 p hg
    simpa only [d3830, d3042, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3830, d3042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30097 p hg
    simpa only [d3830, d3042, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30099 (p : Pattern) (guard : d5843 p = 1) : d3831 p ≤ (0 : Int) + d1967 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3831, d1967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30048 p hg
    simpa only [d3831, d1967, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3831, d1967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3831, d1967, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
