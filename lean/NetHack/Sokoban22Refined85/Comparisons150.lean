/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons149
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare21000 (p : Pattern) (guard : d5850 p = 1) : d2841 p ≤ (0 : Int) + d3951 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2841, d3951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20998 p hg
    simpa only [d2841, d3951, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2841, d3951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20999 p hg
    simpa only [d2841, d3951, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21001 (p : Pattern) (guard : d5850 p = 1) : d2842 p ≤ (0 : Int) + d3952 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2842, d3952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20996 p hg
    simpa only [d2842, d3952, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2842, d3952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21000 p hg
    simpa only [d2842, d3952, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21002 (p : Pattern) (guard : d5850 p = 1) : d2843 p ≤ (0 : Int) + d3953 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2843, d3953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20825 p hg
    simpa only [d2843, d3953, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2843, d3953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21001 p hg
    simpa only [d2843, d3953, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21003 (p : Pattern) (guard : d5850 p = 1) : d2844 p ≤ (0 : Int) + d3954 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2844, d3954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20873 p hg
    simpa only [d2844, d3954, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2844, d3954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d2844, d3954, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21004 (p : Pattern) (guard : d5850 p = 1) : d2845 p ≤ (0 : Int) + d3955 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2845, d3955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20886 p hg
    simpa only [d2845, d3955, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2845, d3955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21003 p hg
    simpa only [d2845, d3955, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21005 (p : Pattern) (guard : d5850 p = 1) : d2846 p ≤ (0 : Int) + d3956 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2846, d3956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21003 p hg
    simpa only [d2846, d3956, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2846, d3956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d2846, d3956, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21006 (p : Pattern) (guard : d5850 p = 1) : d2847 p ≤ (0 : Int) + d3957 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2847, d3957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21004 p hg
    simpa only [d2847, d3957, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2847, d3957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21005 p hg
    simpa only [d2847, d3957, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21007 (p : Pattern) (guard : d5850 p = 1) : d2848 p ≤ (0 : Int) + d3958 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2848, d3958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21006 p hg
    simpa only [d2848, d3958, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2848, d3958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20894 p hg
    simpa only [d2848, d3958, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21008 (p : Pattern) (guard : d5850 p = 1) : d2849 p ≤ (0 : Int) + d3959 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2849, d3959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20885 p hg
    simpa only [d2849, d3959, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2849, d3959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21007 p hg
    simpa only [d2849, d3959, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21009 (p : Pattern) (guard : d5850 p = 1) : d2850 p ≤ (0 : Int) + d3960 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2850, d3960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21002 p hg
    simpa only [d2850, d3960, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2850, d3960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21008 p hg
    simpa only [d2850, d3960, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21010 (p : Pattern) (guard : d5850 p = 1) : d2851 p ≤ (0 : Int) + d3961 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2851, d3961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21008 p hg
    simpa only [d2851, d3961, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2851, d3961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20901 p hg
    simpa only [d2851, d3961, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21011 (p : Pattern) (guard : d5850 p = 1) : d2852 p ≤ (0 : Int) + d3962 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2852, d3962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21009 p hg
    simpa only [d2852, d3962, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2852, d3962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21010 p hg
    simpa only [d2852, d3962, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21012 (p : Pattern) (guard : d5850 p = 1) : d2686 p ≤ (0 : Int) + d3963 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2686, d3963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20751 p hg
    simpa only [d2686, d3963, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2686, d3963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20866 p hg
    simpa only [d2686, d3963, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21013 (p : Pattern) (guard : d5850 p = 1) : d2745 p ≤ (0 : Int) + d3964 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2745, d3964, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20860 p hg
    simpa only [d2745, d3964, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2745, d3964, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d2745, d3964, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21014 (p : Pattern) (guard : d5850 p = 1) : d2746 p ≤ (0 : Int) + d3965 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2746, d3965, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21012 p hg
    simpa only [d2746, d3965, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2746, d3965, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21013 p hg
    simpa only [d2746, d3965, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21015 (p : Pattern) (guard : d5850 p = 1) : d2749 p ≤ (0 : Int) + d3966 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2749, d3966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21014 p hg
    simpa only [d2749, d3966, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2749, d3966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20873 p hg
    simpa only [d2749, d3966, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21016 (p : Pattern) (guard : d5850 p = 1) : d2750 p ≤ (0 : Int) + d3967 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2750, d3967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20863 p hg
    simpa only [d2750, d3967, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2750, d3967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21015 p hg
    simpa only [d2750, d3967, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21017 (p : Pattern) (guard : d5850 p = 1) : d2749 p ≤ (0 : Int) + d3968 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2749, d3968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20868 p hg
    simpa only [d2749, d3968, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2749, d3968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20873 p hg
    simpa only [d2749, d3968, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21018 (p : Pattern) (guard : d5850 p = 1) : d2751 p ≤ (0 : Int) + d3969 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2751, d3969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21017 p hg
    simpa only [d2751, d3969, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2751, d3969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20785 p hg
    simpa only [d2751, d3969, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21019 (p : Pattern) (guard : d5850 p = 1) : d2752 p ≤ (0 : Int) + d3970 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2752, d3970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21016 p hg
    simpa only [d2752, d3970, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2752, d3970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21018 p hg
    simpa only [d2752, d3970, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21020 (p : Pattern) (guard : d5850 p = 1) : d2853 p ≤ (0 : Int) + d3971 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2853, d3971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20849 p hg
    simpa only [d2853, d3971, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2853, d3971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20809 p hg
    simpa only [d2853, d3971, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21021 (p : Pattern) (guard : d5850 p = 1) : d2854 p ≤ (0 : Int) + d3972 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2854, d3972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20878 p hg
    simpa only [d2854, d3972, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2854, d3972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21020 p hg
    simpa only [d2854, d3972, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21022 (p : Pattern) (guard : d5850 p = 1) : d2855 p ≤ (0 : Int) + d3973 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2855, d3973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21021 p hg
    simpa only [d2855, d3973, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2855, d3973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20997 p hg
    simpa only [d2855, d3973, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21023 (p : Pattern) (guard : d5850 p = 1) : d2856 p ≤ (0 : Int) + d3974 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2856, d3974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20880 p hg
    simpa only [d2856, d3974, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2856, d3974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d2856, d3974, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21024 (p : Pattern) (guard : d5850 p = 1) : d2857 p ≤ (0 : Int) + d3975 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2857, d3975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21023 p hg
    simpa only [d2857, d3975, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2857, d3975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d2857, d3975, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21025 (p : Pattern) (guard : d5850 p = 1) : d2858 p ≤ (0 : Int) + d3976 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2858, d3976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21024 p hg
    simpa only [d2858, d3976, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2858, d3976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d2858, d3976, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21026 (p : Pattern) (guard : d5850 p = 1) : d2859 p ≤ (0 : Int) + d3977 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2859, d3977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21022 p hg
    simpa only [d2859, d3977, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2859, d3977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21025 p hg
    simpa only [d2859, d3977, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21027 (p : Pattern) (guard : d5850 p = 1) : d2860 p ≤ (0 : Int) + d3978 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2860, d3978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21019 p hg
    simpa only [d2860, d3978, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2860, d3978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21026 p hg
    simpa only [d2860, d3978, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21028 (p : Pattern) (guard : d5850 p = 1) : d2703 p ≤ (0 : Int) + d3979 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d2703, d3979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20797 p hg
    simpa only [d5850, d2703, d3979, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d2703, d3979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20794 p hg
    simpa only [d5850, d2703, d3979, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21029 (p : Pattern) (guard : d5850 p = 1) : d2704 p ≤ (0 : Int) + d3980 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2704, d3980, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20795 p hg
    simpa only [d2704, d3980, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2704, d3980, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21028 p hg
    simpa only [d2704, d3980, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21030 (p : Pattern) (guard : d5850 p = 1) : d2725 p ≤ (0 : Int) + d3981 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2725, d3981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20831 p hg
    simpa only [d2725, d3981, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2725, d3981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21029 p hg
    simpa only [d2725, d3981, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21031 (p : Pattern) (guard : d5850 p = 1) : d2705 p ≤ (0 : Int) + d3982 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2705, d3982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20834 p hg
    simpa only [d2705, d3982, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2705, d3982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d2705, d3982, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21032 (p : Pattern) (guard : d5850 p = 1) : d2753 p ≤ (0 : Int) + d3983 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2753, d3983, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21030 p hg
    simpa only [d2753, d3983, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2753, d3983, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21031 p hg
    simpa only [d2753, d3983, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21033 (p : Pattern) (guard : d5850 p = 1) : d2760 p ≤ (0 : Int) + d3984 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2760, d3984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21014 p hg
    simpa only [d2760, d3984, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2760, d3984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21032 p hg
    simpa only [d2760, d3984, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21034 (p : Pattern) (guard : d5850 p = 1) : d2690 p ≤ (0 : Int) + d3985 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d2690, d3985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20772 p hg
    simpa only [d5850, d2690, d3985, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d2690, d3985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20813 p hg
    simpa only [d5850, d2690, d3985, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21035 (p : Pattern) (guard : d5850 p = 1) : d2691 p ≤ (0 : Int) + d3986 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2691, d3986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20814 p hg
    simpa only [d2691, d3986, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2691, d3986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21034 p hg
    simpa only [d2691, d3986, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21036 (p : Pattern) (guard : d5850 p = 1) : d2692 p ≤ (0 : Int) + d3987 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2692, d3987, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20769 p hg
    simpa only [d2692, d3987, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2692, d3987, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21035 p hg
    simpa only [d2692, d3987, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21037 (p : Pattern) (guard : d5850 p = 1) : d2747 p ≤ (0 : Int) + d3988 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2747, d3988, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20774 p hg
    simpa only [d2747, d3988, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2747, d3988, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d2747, d3988, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21038 (p : Pattern) (guard : d5850 p = 1) : d2748 p ≤ (0 : Int) + d3989 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2748, d3989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21036 p hg
    simpa only [d2748, d3989, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2748, d3989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21037 p hg
    simpa only [d2748, d3989, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21039 (p : Pattern) (guard : d5850 p = 1) : d2844 p ≤ (0 : Int) + d3990 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2844, d3990, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21038 p hg
    simpa only [d2844, d3990, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2844, d3990, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d2844, d3990, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21040 (p : Pattern) (guard : d5850 p = 1) : d2845 p ≤ (0 : Int) + d3991 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2845, d3991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21033 p hg
    simpa only [d2845, d3991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2845, d3991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21039 p hg
    simpa only [d2845, d3991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21041 (p : Pattern) (guard : d5850 p = 1) : d2747 p ≤ (0 : Int) + d3992 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2747, d3992, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21035 p hg
    simpa only [d2747, d3992, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2747, d3992, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d2747, d3992, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21042 (p : Pattern) (guard : d5850 p = 1) : d2748 p ≤ (0 : Int) + d3993 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2748, d3993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20818 p hg
    simpa only [d2748, d3993, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2748, d3993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21041 p hg
    simpa only [d2748, d3993, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21043 (p : Pattern) (guard : d5850 p = 1) : d2844 p ≤ (0 : Int) + d3994 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2844, d3994, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21042 p hg
    simpa only [d2844, d3994, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2844, d3994, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d2844, d3994, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21044 (p : Pattern) (guard : d5850 p = 1) : d2846 p ≤ (0 : Int) + d3995 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2846, d3995, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21043 p hg
    simpa only [d2846, d3995, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2846, d3995, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d2846, d3995, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21045 (p : Pattern) (guard : d5850 p = 1) : d2847 p ≤ (0 : Int) + d3996 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2847, d3996, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21040 p hg
    simpa only [d2847, d3996, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2847, d3996, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21044 p hg
    simpa only [d2847, d3996, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21046 (p : Pattern) (guard : d5850 p = 1) : d2861 p ≤ (0 : Int) + d3997 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2861, d3997, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20818 p hg
    simpa only [d2861, d3997, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2861, d3997, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20809 p hg
    simpa only [d2861, d3997, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21047 (p : Pattern) (guard : d5850 p = 1) : d2862 p ≤ (0 : Int) + d3998 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2862, d3998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21046 p hg
    simpa only [d2862, d3998, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2862, d3998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20819 p hg
    simpa only [d2862, d3998, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21048 (p : Pattern) (guard : d5850 p = 1) : d2863 p ≤ (0 : Int) + d3999 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2863, d3999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21047 p hg
    simpa only [d2863, d3999, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2863, d3999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21024 p hg
    simpa only [d2863, d3999, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21049 (p : Pattern) (guard : d5850 p = 1) : d2864 p ≤ (0 : Int) + d4000 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2864, d4000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20608 p hg
    simpa only [d2864, d4000, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2864, d4000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d2864, d4000, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21050 (p : Pattern) (guard : d5850 p = 1) : d2865 p ≤ (0 : Int) + d4001 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2865, d4001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21048 p hg
    simpa only [d2865, d4001, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2865, d4001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21049 p hg
    simpa only [d2865, d4001, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21051 (p : Pattern) (guard : d5850 p = 1) : d2866 p ≤ (0 : Int) + d4002 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2866, d4002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21045 p hg
    simpa only [d2866, d4002, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2866, d4002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21050 p hg
    simpa only [d2866, d4002, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21052 (p : Pattern) (guard : d5850 p = 1) : d2867 p ≤ (0 : Int) + d4003 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2867, d4003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21027 p hg
    simpa only [d2867, d4003, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2867, d4003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21051 p hg
    simpa only [d2867, d4003, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21053 (p : Pattern) (guard : d5850 p = 1) : d2746 p ≤ (0 : Int) + d4004 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d4004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20868 p hg
    simpa only [d4004, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d4004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20871 p hg
    simpa only [d4004, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21054 (p : Pattern) (guard : d5850 p = 1) : d2868 p ≤ (0 : Int) + d4005 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2868, d4005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20878 p hg
    simpa only [d2868, d4005, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2868, d4005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20643 p hg
    simpa only [d2868, d4005, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21055 (p : Pattern) (guard : d5850 p = 1) : d2869 p ≤ (0 : Int) + d4006 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2869, d4006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21053 p hg
    simpa only [d2869, d4006, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2869, d4006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21054 p hg
    simpa only [d2869, d4006, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21056 (p : Pattern) (guard : d5850 p = 1) : d2870 p ≤ (0 : Int) + d4007 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2870, d4007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21055 p hg
    simpa only [d2870, d4007, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2870, d4007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20890 p hg
    simpa only [d2870, d4007, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21057 (p : Pattern) (guard : d5850 p = 1) : d2871 p ≤ (0 : Int) + d4008 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2871, d4008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21056 p hg
    simpa only [d2871, d4008, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2871, d4008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20894 p hg
    simpa only [d2871, d4008, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21058 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d326 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare21059 (p : Pattern) (guard : d5850 p = 1) : d2703 p ≤ (0 : Int) + d4009 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d2703, d4009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20797 p hg
    simpa only [d5850, d2703, d4009, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d2703, d4009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21058 p hg
    simpa only [d5850, d2703, d4009, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21060 (p : Pattern) (guard : d5850 p = 1) : d2704 p ≤ (0 : Int) + d4010 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2704, d4010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20795 p hg
    simpa only [d2704, d4010, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2704, d4010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21059 p hg
    simpa only [d2704, d4010, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21061 (p : Pattern) (guard : d5850 p = 1) : d2705 p ≤ (0 : Int) + d4011 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2705, d4011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21060 p hg
    simpa only [d2705, d4011, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2705, d4011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d2705, d4011, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21062 (p : Pattern) (guard : d5850 p = 1) : d2753 p ≤ (0 : Int) + d4012 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2753, d4012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20849 p hg
    simpa only [d2753, d4012, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2753, d4012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21061 p hg
    simpa only [d2753, d4012, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21063 (p : Pattern) (guard : d5850 p = 1) : d2753 p ≤ (0 : Int) + d4013 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d4013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21062 p hg
    simpa only [d4013, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d4013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20878 p hg
    simpa only [d4013, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21064 (p : Pattern) (guard : d5850 p = 1) : d2872 p ≤ (0 : Int) + d4014 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2872, d4014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21063 p hg
    simpa only [d2872, d4014, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2872, d4014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21003 p hg
    simpa only [d2872, d4014, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21065 (p : Pattern) (guard : d5850 p = 1) : d2873 p ≤ (0 : Int) + d4015 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2873, d4015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21064 p hg
    simpa only [d2873, d4015, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2873, d4015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20893 p hg
    simpa only [d2873, d4015, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21066 (p : Pattern) (guard : d5850 p = 1) : d2874 p ≤ (0 : Int) + d4016 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2874, d4016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20679 p hg
    simpa only [d2874, d4016, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2874, d4016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d2874, d4016, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21067 (p : Pattern) (guard : d5850 p = 1) : d2875 p ≤ (0 : Int) + d4017 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2875, d4017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21066 p hg
    simpa only [d2875, d4017, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2875, d4017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d2875, d4017, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21068 (p : Pattern) (guard : d5850 p = 1) : d2876 p ≤ (0 : Int) + d4018 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2876, d4018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21065 p hg
    simpa only [d2876, d4018, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2876, d4018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21067 p hg
    simpa only [d2876, d4018, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21069 (p : Pattern) (guard : d5850 p = 1) : d2877 p ≤ (0 : Int) + d4019 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2877, d4019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21057 p hg
    simpa only [d2877, d4019, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2877, d4019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21068 p hg
    simpa only [d2877, d4019, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21070 (p : Pattern) (guard : d5850 p = 1) : d2878 p ≤ (0 : Int) + d4020 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2878, d4020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21052 p hg
    simpa only [d2878, d4020, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2878, d4020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21069 p hg
    simpa only [d2878, d4020, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21071 (p : Pattern) (guard : d5850 p = 1) : d2879 p ≤ (0 : Int) + d4021 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2879, d4021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20878 p hg
    simpa only [d2879, d4021, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2879, d4021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20678 p hg
    simpa only [d2879, d4021, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21072 (p : Pattern) (guard : d5850 p = 1) : d2880 p ≤ (0 : Int) + d4022 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2880, d4022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21053 p hg
    simpa only [d2880, d4022, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2880, d4022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21071 p hg
    simpa only [d2880, d4022, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21073 (p : Pattern) (guard : d5850 p = 1) : d2881 p ≤ (0 : Int) + d4023 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2881, d4023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20873 p hg
    simpa only [d2881, d4023, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2881, d4023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20678 p hg
    simpa only [d2881, d4023, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21074 (p : Pattern) (guard : d5850 p = 1) : d2882 p ≤ (0 : Int) + d4024 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2882, d4024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21073 p hg
    simpa only [d2882, d4024, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2882, d4024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d2882, d4024, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21075 (p : Pattern) (guard : d5850 p = 1) : d2883 p ≤ (0 : Int) + d4025 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2883, d4025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21072 p hg
    simpa only [d2883, d4025, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2883, d4025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21074 p hg
    simpa only [d2883, d4025, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21076 (p : Pattern) (guard : d5850 p = 1) : d2884 p ≤ (0 : Int) + d4026 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2884, d4026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20881 p hg
    simpa only [d2884, d4026, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2884, d4026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20643 p hg
    simpa only [d2884, d4026, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21077 (p : Pattern) (guard : d5850 p = 1) : d2885 p ≤ (0 : Int) + d4027 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2885, d4027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21076 p hg
    simpa only [d2885, d4027, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2885, d4027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d2885, d4027, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21078 (p : Pattern) (guard : d5850 p = 1) : d2886 p ≤ (0 : Int) + d4028 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2886, d4028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21077 p hg
    simpa only [d2886, d4028, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2886, d4028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d2886, d4028, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21079 (p : Pattern) (guard : d5850 p = 1) : d2887 p ≤ (0 : Int) + d4029 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2887, d4029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21075 p hg
    simpa only [d2887, d4029, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2887, d4029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21078 p hg
    simpa only [d2887, d4029, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21080 (p : Pattern) (guard : d5850 p = 1) : d2888 p ≤ (0 : Int) + d4030 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2888, d4030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21079 p hg
    simpa only [d2888, d4030, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2888, d4030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21068 p hg
    simpa only [d2888, d4030, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21081 (p : Pattern) (guard : d5850 p = 1) : d2889 p ≤ (0 : Int) + d4031 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2889, d4031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21080 p hg
    simpa only [d2889, d4031, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2889, d4031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d2889, d4031, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21082 (p : Pattern) (guard : d5850 p = 1) : d2890 p ≤ (0 : Int) + d4032 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2890, d4032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21070 p hg
    simpa only [d2890, d4032, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2890, d4032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21081 p hg
    simpa only [d2890, d4032, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21083 (p : Pattern) (guard : d5850 p = 1) : d2891 p ≤ (0 : Int) + d4033 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2891, d4033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21011 p hg
    simpa only [d2891, d4033, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2891, d4033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21082 p hg
    simpa only [d2891, d4033, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21084 (p : Pattern) (guard : d5850 p = 1) : d2892 p ≤ (0 : Int) + d4034 p := by
  cases selected : p 71 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2892, d4034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20724 p hg
    simpa only [d2892, d4034, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2892, d4034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21083 p hg
    simpa only [d2892, d4034, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21085 (p : Pattern) (guard : d5850 p = 1) : d2893 p ≤ (0 : Int) + d4035 p := by
  cases selected : p 49 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2893, d4035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20992 p hg
    simpa only [d2893, d4035, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2893, d4035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21084 p hg
    simpa only [d2893, d4035, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21086 (p : Pattern) (guard : d5850 p = 1) : d2894 p ≤ (0 : Int) + d4036 p := by
  cases selected : p 48 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2894, d4036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20917 p hg
    simpa only [d2894, d4036, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2894, d4036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21085 p hg
    simpa only [d2894, d4036, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21087 (p : Pattern) (guard : d0 p = 1) : d315 p ≤ (0 : Int) + d14 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare21088 (p : Pattern) (guard : d5502 p = 1) : d2503 p ≤ (0 : Int) + d14 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1207 p hg
    simpa only [d5502, d2503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21087 p hg
    simpa only [d5502, d2503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21089 (p : Pattern) (guard : d5502 p = 1) : d2504 p ≤ (0 : Int) + d14 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1207 p hg
    simpa only [d5502, d2504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5657 p hg
    simpa only [d5502, d2504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21090 (p : Pattern) (guard : d5502 p = 1) : d2505 p ≤ (0 : Int) + d14 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21088 p hg
    simpa only [d2505, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21089 p hg
    simpa only [d2505, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21091 (p : Pattern) (guard : d5502 p = 1) : d2504 p ≤ (0 : Int) + d1771 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2504, d1771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1207 p hg
    simpa only [d5502, d2504, d1771, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2504, d1771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19403 p hg
    simpa only [d5502, d2504, d1771, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21092 (p : Pattern) (guard : d5502 p = 1) : d2506 p ≤ (0 : Int) + d1770 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17202 p hg
    simpa only [d5502, d2506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19403 p hg
    simpa only [d5502, d2506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21093 (p : Pattern) (guard : d5502 p = 1) : d2507 p ≤ (0 : Int) + d1772 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2507, d1772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21091 p hg
    simpa only [d2507, d1772, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2507, d1772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21092 p hg
    simpa only [d2507, d1772, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21094 (p : Pattern) (guard : d5502 p = 1) : d2508 p ≤ (0 : Int) + d2895 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2508, d2895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21090 p hg
    simpa only [d2508, d2895, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2508, d2895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21093 p hg
    simpa only [d2508, d2895, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21095 (p : Pattern) (guard : d5502 p = 1) : d2504 p ≤ (0 : Int) + d1685 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2504, d1685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1207 p hg
    simpa only [d5502, d2504, d1685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2504, d1685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19406 p hg
    simpa only [d5502, d2504, d1685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21096 (p : Pattern) (guard : d5502 p = 1) : d2509 p ≤ (0 : Int) + d1684 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17086 p hg
    simpa only [d5502, d2509, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19406 p hg
    simpa only [d5502, d2509, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21097 (p : Pattern) (guard : d5502 p = 1) : d2510 p ≤ (0 : Int) + d1686 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2510, d1686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21095 p hg
    simpa only [d2510, d1686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2510, d1686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21096 p hg
    simpa only [d2510, d1686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21098 (p : Pattern) (guard : d5502 p = 1) : d12 p ≤ (0 : Int) + d12 p := by
  omega
theorem compare21099 (p : Pattern) (guard : d5502 p = 1) : d2511 p ≤ (0 : Int) + d1687 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2511, d1687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21097 p hg
    simpa only [d2511, d1687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2511, d1687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2511, d1687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21100 (p : Pattern) (guard : d5502 p = 1) : d2512 p ≤ (0 : Int) + d2896 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2512, d2896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21094 p hg
    simpa only [d2512, d2896, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2512, d2896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21099 p hg
    simpa only [d2512, d2896, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21101 (p : Pattern) (guard : d0 p = 1) : d327 p ≤ (0 : Int) + d14 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare21102 (p : Pattern) (guard : d5502 p = 1) : d2513 p ≤ (0 : Int) + d14 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1207 p hg
    simpa only [d5502, d2513, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21101 p hg
    simpa only [d5502, d2513, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21103 (p : Pattern) (guard : d5502 p = 1) : d2514 p ≤ (0 : Int) + d14 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21102 p hg
    simpa only [d2514, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21089 p hg
    simpa only [d2514, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21104 (p : Pattern) (guard : d5502 p = 1) : d2515 p ≤ (0 : Int) + d2895 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2515, d2895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21103 p hg
    simpa only [d2515, d2895, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2515, d2895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21093 p hg
    simpa only [d2515, d2895, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21105 (p : Pattern) (guard : d5502 p = 1) : d2516 p ≤ (0 : Int) + d2896 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2516, d2896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21104 p hg
    simpa only [d2516, d2896, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2516, d2896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21099 p hg
    simpa only [d2516, d2896, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21106 (p : Pattern) (guard : d5502 p = 1) : d2517 p ≤ (0 : Int) + d2896 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21100 p hg
    simpa only [d2517, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21105 p hg
    simpa only [d2517, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21107 (p : Pattern) (guard : d5502 p = 1) : d2518 p ≤ (0 : Int) + d2895 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2518, d2895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21089 p hg
    simpa only [d2518, d2895, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2518, d2895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21093 p hg
    simpa only [d2518, d2895, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21108 (p : Pattern) (guard : d5502 p = 1) : d2519 p ≤ (0 : Int) + d2896 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2519, d2896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21107 p hg
    simpa only [d2519, d2896, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2519, d2896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21099 p hg
    simpa only [d2519, d2896, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21109 (p : Pattern) (guard : d5502 p = 1) : d2520 p ≤ (0 : Int) + d18 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2003 p hg
    simpa only [d5502, d2520, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5661 p hg
    simpa only [d5502, d2520, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21110 (p : Pattern) (guard : d5502 p = 1) : d2520 p ≤ (0 : Int) + d2011 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2520, d2011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2003 p hg
    simpa only [d5502, d2520, d2011, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2520, d2011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19420 p hg
    simpa only [d5502, d2520, d2011, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21111 (p : Pattern) (guard : d5502 p = 1) : d2521 p ≤ (0 : Int) + d1795 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17222 p hg
    simpa only [d5502, d2521, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19420 p hg
    simpa only [d5502, d2521, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21112 (p : Pattern) (guard : d5502 p = 1) : d2522 p ≤ (0 : Int) + d2012 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2522, d2012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21110 p hg
    simpa only [d2522, d2012, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2522, d2012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21111 p hg
    simpa only [d2522, d2012, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21113 (p : Pattern) (guard : d5502 p = 1) : d2523 p ≤ (0 : Int) + d2897 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2523, d2897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21109 p hg
    simpa only [d2523, d2897, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2523, d2897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21112 p hg
    simpa only [d2523, d2897, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21114 (p : Pattern) (guard : d5502 p = 1) : d2520 p ≤ (0 : Int) + d1695 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2520, d1695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2003 p hg
    simpa only [d5502, d2520, d1695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2520, d1695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19423 p hg
    simpa only [d5502, d2520, d1695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21115 (p : Pattern) (guard : d5502 p = 1) : d2524 p ≤ (0 : Int) + d1694 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17103 p hg
    simpa only [d5502, d2524, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19423 p hg
    simpa only [d5502, d2524, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21116 (p : Pattern) (guard : d5502 p = 1) : d2525 p ≤ (0 : Int) + d1696 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2525, d1696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21114 p hg
    simpa only [d2525, d1696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2525, d1696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21115 p hg
    simpa only [d2525, d1696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21117 (p : Pattern) (guard : d5502 p = 1) : d2526 p ≤ (0 : Int) + d1697 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2526, d1697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21116 p hg
    simpa only [d2526, d1697, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2526, d1697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2526, d1697, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21118 (p : Pattern) (guard : d5502 p = 1) : d2527 p ≤ (0 : Int) + d2898 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2527, d2898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21113 p hg
    simpa only [d2527, d2898, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2527, d2898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21117 p hg
    simpa only [d2527, d2898, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21119 (p : Pattern) (guard : d5502 p = 1) : d2528 p ≤ (0 : Int) + d2899 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2528, d2899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21108 p hg
    simpa only [d2528, d2899, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2528, d2899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21118 p hg
    simpa only [d2528, d2899, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21120 (p : Pattern) (guard : d5502 p = 1) : d2529 p ≤ (0 : Int) + d2900 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2529, d2900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21106 p hg
    simpa only [d2529, d2900, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2529, d2900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21119 p hg
    simpa only [d2529, d2900, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21121 (p : Pattern) (guard : d5502 p = 1) : d2530 p ≤ (0 : Int) + d24 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2010 p hg
    simpa only [d5502, d2530, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5667 p hg
    simpa only [d5502, d2530, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21122 (p : Pattern) (guard : d5502 p = 1) : d2530 p ≤ (0 : Int) + d1802 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2530, d1802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2010 p hg
    simpa only [d5502, d2530, d1802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2530, d1802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19435 p hg
    simpa only [d5502, d2530, d1802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21123 (p : Pattern) (guard : d5502 p = 1) : d357 p ≤ (0 : Int) + d356 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17232 p hg
    simpa only [d5502, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19435 p hg
    simpa only [d5502, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21124 (p : Pattern) (guard : d5502 p = 1) : d2531 p ≤ (0 : Int) + d1803 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2531, d1803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21122 p hg
    simpa only [d2531, d1803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2531, d1803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21123 p hg
    simpa only [d2531, d1803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21125 (p : Pattern) (guard : d5502 p = 1) : d2532 p ≤ (0 : Int) + d2901 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2532, d2901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21121 p hg
    simpa only [d2532, d2901, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2532, d2901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21124 p hg
    simpa only [d2532, d2901, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21126 (p : Pattern) (guard : d5502 p = 1) : d2530 p ≤ (0 : Int) + d1703 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2530, d1703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2010 p hg
    simpa only [d5502, d2530, d1703, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2530, d1703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19438 p hg
    simpa only [d5502, d2530, d1703, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21127 (p : Pattern) (guard : d5502 p = 1) : d2533 p ≤ (0 : Int) + d1702 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17114 p hg
    simpa only [d5502, d2533, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19438 p hg
    simpa only [d5502, d2533, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21128 (p : Pattern) (guard : d5502 p = 1) : d2534 p ≤ (0 : Int) + d1704 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2534, d1704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21126 p hg
    simpa only [d2534, d1704, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2534, d1704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21127 p hg
    simpa only [d2534, d1704, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21129 (p : Pattern) (guard : d5502 p = 1) : d2535 p ≤ (0 : Int) + d1705 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2535, d1705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21128 p hg
    simpa only [d2535, d1705, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2535, d1705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2535, d1705, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21130 (p : Pattern) (guard : d5502 p = 1) : d2536 p ≤ (0 : Int) + d2902 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2536, d2902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21125 p hg
    simpa only [d2536, d2902, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2536, d2902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21129 p hg
    simpa only [d2536, d2902, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21131 (p : Pattern) (guard : d5502 p = 1) : d2537 p ≤ (0 : Int) + d2903 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2537, d2903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21130 p hg
    simpa only [d2537, d2903, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2537, d2903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2537, d2903, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21132 (p : Pattern) (guard : d5502 p = 1) : d2538 p ≤ (0 : Int) + d2904 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2538, d2904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21119 p hg
    simpa only [d2538, d2904, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2538, d2904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21131 p hg
    simpa only [d2538, d2904, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21133 (p : Pattern) (guard : d5502 p = 1) : d2539 p ≤ (0 : Int) + d2905 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2539, d2905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21120 p hg
    simpa only [d2539, d2905, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2539, d2905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21132 p hg
    simpa only [d2539, d2905, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21134 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d1776 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare21135 (p : Pattern) (guard : d5502 p = 1) : d2504 p ≤ (0 : Int) + d1777 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2504, d1777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1207 p hg
    simpa only [d5502, d2504, d1777, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2504, d1777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21134 p hg
    simpa only [d5502, d2504, d1777, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21136 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d1786 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare21137 (p : Pattern) (guard : d5502 p = 1) : d2506 p ≤ (0 : Int) + d1787 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2506, d1787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17202 p hg
    simpa only [d5502, d2506, d1787, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2506, d1787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21136 p hg
    simpa only [d5502, d2506, d1787, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21138 (p : Pattern) (guard : d5502 p = 1) : d2507 p ≤ (0 : Int) + d1788 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2507, d1788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21135 p hg
    simpa only [d2507, d1788, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2507, d1788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21137 p hg
    simpa only [d2507, d1788, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21139 (p : Pattern) (guard : d5502 p = 1) : d2518 p ≤ (0 : Int) + d2906 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2518, d2906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21089 p hg
    simpa only [d2518, d2906, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2518, d2906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21138 p hg
    simpa only [d2518, d2906, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
