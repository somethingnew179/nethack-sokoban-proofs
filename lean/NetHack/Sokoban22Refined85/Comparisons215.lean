/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons214
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare30100 (p : Pattern) (guard : d5843 p = 1) : d3832 p ≤ (0 : Int) + d3043 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3832, d3043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30049 p hg
    simpa only [d3832, d3043, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3832, d3043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30099 p hg
    simpa only [d3832, d3043, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30101 (p : Pattern) (guard : d5843 p = 1) : d3833 p ≤ (0 : Int) + d3044 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3833, d3044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30098 p hg
    simpa only [d3833, d3044, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3833, d3044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30100 p hg
    simpa only [d3833, d3044, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30102 (p : Pattern) (guard : d5843 p = 1) : d3834 p ≤ (0 : Int) + d3045 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3834, d3045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30096 p hg
    simpa only [d3834, d3045, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3834, d3045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30101 p hg
    simpa only [d3834, d3045, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30103 (p : Pattern) (guard : d5843 p = 1) : d3835 p ≤ (0 : Int) + d3046 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3835, d3046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30101 p hg
    simpa only [d3835, d3046, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3835, d3046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30021 p hg
    simpa only [d3835, d3046, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30104 (p : Pattern) (guard : d5843 p = 1) : d3836 p ≤ (0 : Int) + d3047 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3836, d3047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30102 p hg
    simpa only [d3836, d3047, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3836, d3047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30103 p hg
    simpa only [d3836, d3047, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30105 (p : Pattern) (guard : d5843 p = 1) : d3837 p ≤ (0 : Int) + d3048 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3837, d3048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30070 p hg
    simpa only [d3837, d3048, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3837, d3048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30035 p hg
    simpa only [d3837, d3048, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30106 (p : Pattern) (guard : d5843 p = 1) : d3838 p ≤ (0 : Int) + d3049 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3838, d3049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29523 p hg
    simpa only [d3838, d3049, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3838, d3049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30039 p hg
    simpa only [d3838, d3049, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30107 (p : Pattern) (guard : d5843 p = 1) : d3839 p ≤ (0 : Int) + d3050 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3839, d3050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30106 p hg
    simpa only [d3839, d3050, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3839, d3050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30040 p hg
    simpa only [d3839, d3050, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30108 (p : Pattern) (guard : d5843 p = 1) : d3840 p ≤ (0 : Int) + d3051 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3840, d3051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30105 p hg
    simpa only [d3840, d3051, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3840, d3051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30107 p hg
    simpa only [d3840, d3051, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30109 (p : Pattern) (guard : d5843 p = 1) : d3841 p ≤ (0 : Int) + d3052 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3841, d3052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30108 p hg
    simpa only [d3841, d3052, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3841, d3052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3841, d3052, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30110 (p : Pattern) (guard : d5843 p = 1) : d3842 p ≤ (0 : Int) + d3053 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3842, d3053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30109 p hg
    simpa only [d3842, d3053, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3842, d3053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3842, d3053, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30111 (p : Pattern) (guard : d5843 p = 1) : d3843 p ≤ (0 : Int) + d3054 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3843, d3054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30104 p hg
    simpa only [d3843, d3054, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3843, d3054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30110 p hg
    simpa only [d3843, d3054, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30112 (p : Pattern) (guard : d5843 p = 1) : d3844 p ≤ (0 : Int) + d3055 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3844, d3055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30095 p hg
    simpa only [d3844, d3055, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3844, d3055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30105 p hg
    simpa only [d3844, d3055, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30113 (p : Pattern) (guard : d5843 p = 1) : d3845 p ≤ (0 : Int) + d3056 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3845, d3056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30100 p hg
    simpa only [d3845, d3056, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3845, d3056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29898 p hg
    simpa only [d3845, d3056, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30114 (p : Pattern) (guard : d5843 p = 1) : d3846 p ≤ (0 : Int) + d3057 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3846, d3057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30112 p hg
    simpa only [d3846, d3057, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3846, d3057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30113 p hg
    simpa only [d3846, d3057, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30115 (p : Pattern) (guard : d5843 p = 1) : d3847 p ≤ (0 : Int) + d3058 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3847, d3058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30100 p hg
    simpa only [d3847, d3058, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3847, d3058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29901 p hg
    simpa only [d3847, d3058, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30116 (p : Pattern) (guard : d5843 p = 1) : d3848 p ≤ (0 : Int) + d3059 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3848, d3059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30115 p hg
    simpa only [d3848, d3059, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3848, d3059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3848, d3059, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30117 (p : Pattern) (guard : d5843 p = 1) : d3849 p ≤ (0 : Int) + d3060 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3849, d3060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30114 p hg
    simpa only [d3849, d3060, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3849, d3060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30116 p hg
    simpa only [d3849, d3060, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30118 (p : Pattern) (guard : d5843 p = 1) : d3850 p ≤ (0 : Int) + d3061 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3850, d3061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30107 p hg
    simpa only [d3850, d3061, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3850, d3061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3850, d3061, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30119 (p : Pattern) (guard : d5843 p = 1) : d3851 p ≤ (0 : Int) + d3062 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3851, d3062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30118 p hg
    simpa only [d3851, d3062, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3851, d3062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3851, d3062, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30120 (p : Pattern) (guard : d5843 p = 1) : d3852 p ≤ (0 : Int) + d3063 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3852, d3063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30119 p hg
    simpa only [d3852, d3063, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3852, d3063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3852, d3063, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30121 (p : Pattern) (guard : d5843 p = 1) : d3853 p ≤ (0 : Int) + d3064 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3853, d3064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30117 p hg
    simpa only [d3853, d3064, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3853, d3064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30120 p hg
    simpa only [d3853, d3064, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30122 (p : Pattern) (guard : d5843 p = 1) : d3854 p ≤ (0 : Int) + d3065 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3854, d3065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30111 p hg
    simpa only [d3854, d3065, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3854, d3065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30121 p hg
    simpa only [d3854, d3065, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30123 (p : Pattern) (guard : d5843 p = 1) : d3855 p ≤ (0 : Int) + d3066 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3855, d3066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30079 p hg
    simpa only [d3855, d3066, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3855, d3066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30122 p hg
    simpa only [d3855, d3066, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30124 (p : Pattern) (guard : d5843 p = 1) : d3856 p ≤ (0 : Int) + d3067 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3856, d3067, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30021 p hg
    simpa only [d3856, d3067, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3856, d3067, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3856, d3067, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30125 (p : Pattern) (guard : d5843 p = 1) : d3857 p ≤ (0 : Int) + d3068 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3857, d3068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30124 p hg
    simpa only [d3857, d3068, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3857, d3068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3857, d3068, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30126 (p : Pattern) (guard : d5843 p = 1) : d3858 p ≤ (0 : Int) + d3069 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3858, d3069, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30125 p hg
    simpa only [d3858, d3069, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3858, d3069, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3858, d3069, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30127 (p : Pattern) (guard : d5843 p = 1) : d3859 p ≤ (0 : Int) + d3070 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3859, d3070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30126 p hg
    simpa only [d3859, d3070, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3859, d3070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3859, d3070, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30128 (p : Pattern) (guard : d5843 p = 1) : d3860 p ≤ (0 : Int) + d3071 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3860, d3071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30122 p hg
    simpa only [d3860, d3071, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3860, d3071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30127 p hg
    simpa only [d3860, d3071, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30129 (p : Pattern) (guard : d5843 p = 1) : d3861 p ≤ (0 : Int) + d3072 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3861, d3072, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30123 p hg
    simpa only [d3861, d3072, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3861, d3072, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30128 p hg
    simpa only [d3861, d3072, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30130 (p : Pattern) (guard : d5843 p = 1) : d3862 p ≤ (0 : Int) + d2998 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3862, d2998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30010 p hg
    simpa only [d3862, d2998, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3862, d2998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30019 p hg
    simpa only [d3862, d2998, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30131 (p : Pattern) (guard : d5843 p = 1) : d3863 p ≤ (0 : Int) + d3001 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3863, d3001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30130 p hg
    simpa only [d3863, d3001, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3863, d3001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30022 p hg
    simpa only [d3863, d3001, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30132 (p : Pattern) (guard : d5843 p = 1) : d3864 p ≤ (0 : Int) + d3014 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3864, d3014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30131 p hg
    simpa only [d3864, d3014, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3864, d3014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30055 p hg
    simpa only [d3864, d3014, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30133 (p : Pattern) (guard : d5843 p = 1) : d3865 p ≤ (0 : Int) + d3032 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3865, d3032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30132 p hg
    simpa only [d3865, d3032, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3865, d3032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30078 p hg
    simpa only [d3865, d3032, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30134 (p : Pattern) (guard : d5843 p = 1) : d3866 p ≤ (0 : Int) + d3066 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3866, d3066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30133 p hg
    simpa only [d3866, d3066, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3866, d3066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30122 p hg
    simpa only [d3866, d3066, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30135 (p : Pattern) (guard : d5843 p = 1) : d3867 p ≤ (0 : Int) + d3073 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3867, d3073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30122 p hg
    simpa only [d3867, d3073, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3867, d3073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3867, d3073, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30136 (p : Pattern) (guard : d5843 p = 1) : d3868 p ≤ (0 : Int) + d3074 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3868, d3074, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30134 p hg
    simpa only [d3868, d3074, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3868, d3074, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30135 p hg
    simpa only [d3868, d3074, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30137 (p : Pattern) (guard : d5843 p = 1) : d3869 p ≤ (0 : Int) + d3075 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3869, d3075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30129 p hg
    simpa only [d3869, d3075, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3869, d3075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30136 p hg
    simpa only [d3869, d3075, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30138 (p : Pattern) (guard : d5843 p = 1) : d3870 p ≤ (0 : Int) + d3076 p := by
  cases selected : p 71 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3870, d3076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29986 p hg
    simpa only [d3870, d3076, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3870, d3076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30137 p hg
    simpa only [d3870, d3076, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30139 (p : Pattern) (guard : d5843 p = 1) : d3871 p ≤ (0 : Int) + d3077 p := by
  cases selected : p 49 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3871, d3077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29999 p hg
    simpa only [d3871, d3077, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3871, d3077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30138 p hg
    simpa only [d3871, d3077, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30140 (p : Pattern) (guard : d5843 p = 1) : d3872 p ≤ (0 : Int) + d3078 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3872, d3078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29240 p hg
    simpa only [d3872, d3078, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3872, d3078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29865 p hg
    simpa only [d3872, d3078, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30141 (p : Pattern) (guard : d5843 p = 1) : d3873 p ≤ (0 : Int) + d3079 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3873, d3079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29866 p hg
    simpa only [d3873, d3079, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3873, d3079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30140 p hg
    simpa only [d3873, d3079, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30142 (p : Pattern) (guard : d5843 p = 1) : d3874 p ≤ (0 : Int) + d3080 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3874, d3080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29235 p hg
    simpa only [d3874, d3080, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3874, d3080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30141 p hg
    simpa only [d3874, d3080, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30143 (p : Pattern) (guard : d5843 p = 1) : d3875 p ≤ (0 : Int) + d2013 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3875, d2013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29821 p hg
    simpa only [d3875, d2013, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3875, d2013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3875, d2013, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30144 (p : Pattern) (guard : d5843 p = 1) : d3876 p ≤ (0 : Int) + d3081 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3876, d3081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30142 p hg
    simpa only [d3876, d3081, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3876, d3081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30143 p hg
    simpa only [d3876, d3081, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30145 (p : Pattern) (guard : d5843 p = 1) : d3877 p ≤ (0 : Int) + d3082 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3877, d3082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29922 p hg
    simpa only [d3877, d3082, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3877, d3082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30144 p hg
    simpa only [d3877, d3082, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30146 (p : Pattern) (guard : d5843 p = 1) : d3878 p ≤ (0 : Int) + d3083 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3878, d3083, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29922 p hg
    simpa only [d3878, d3083, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3878, d3083, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30145 p hg
    simpa only [d3878, d3083, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30147 (p : Pattern) (guard : d5843 p = 1) : d3879 p ≤ (0 : Int) + d3084 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3879, d3084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30145 p hg
    simpa only [d3879, d3084, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3879, d3084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29943 p hg
    simpa only [d3879, d3084, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30148 (p : Pattern) (guard : d5843 p = 1) : d3880 p ≤ (0 : Int) + d3085 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3880, d3085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30146 p hg
    simpa only [d3880, d3085, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3880, d3085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30147 p hg
    simpa only [d3880, d3085, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30149 (p : Pattern) (guard : d5843 p = 1) : d3881 p ≤ (0 : Int) + d3086 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3881, d3086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29905 p hg
    simpa only [d3881, d3086, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3881, d3086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29857 p hg
    simpa only [d3881, d3086, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30150 (p : Pattern) (guard : d5843 p = 1) : d3882 p ≤ (0 : Int) + d3087 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3882, d3087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29946 p hg
    simpa only [d3882, d3087, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3882, d3087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30149 p hg
    simpa only [d3882, d3087, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30151 (p : Pattern) (guard : d5843 p = 1) : d3883 p ≤ (0 : Int) + d3088 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3883, d3088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29905 p hg
    simpa only [d3883, d3088, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3883, d3088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29862 p hg
    simpa only [d3883, d3088, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30152 (p : Pattern) (guard : d5843 p = 1) : d3884 p ≤ (0 : Int) + d3089 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3884, d3089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29947 p hg
    simpa only [d3884, d3089, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3884, d3089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3884, d3089, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30153 (p : Pattern) (guard : d5843 p = 1) : d3885 p ≤ (0 : Int) + d3090 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3885, d3090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30151 p hg
    simpa only [d3885, d3090, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3885, d3090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30152 p hg
    simpa only [d3885, d3090, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30154 (p : Pattern) (guard : d5843 p = 1) : d3886 p ≤ (0 : Int) + d3091 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3886, d3091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30150 p hg
    simpa only [d3886, d3091, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3886, d3091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30153 p hg
    simpa only [d3886, d3091, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30155 (p : Pattern) (guard : d5843 p = 1) : d3887 p ≤ (0 : Int) + d3092 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3887, d3092, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29906 p hg
    simpa only [d3887, d3092, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3887, d3092, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30152 p hg
    simpa only [d3887, d3092, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30156 (p : Pattern) (guard : d5843 p = 1) : d3888 p ≤ (0 : Int) + d3093 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3888, d3093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30155 p hg
    simpa only [d3888, d3093, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3888, d3093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29913 p hg
    simpa only [d3888, d3093, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30157 (p : Pattern) (guard : d5843 p = 1) : d3889 p ≤ (0 : Int) + d3094 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3889, d3094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30154 p hg
    simpa only [d3889, d3094, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3889, d3094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30156 p hg
    simpa only [d3889, d3094, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30158 (p : Pattern) (guard : d5843 p = 1) : d3890 p ≤ (0 : Int) + d3095 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3890, d3095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30148 p hg
    simpa only [d3890, d3095, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3890, d3095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30157 p hg
    simpa only [d3890, d3095, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30159 (p : Pattern) (guard : d5843 p = 1) : d3891 p ≤ (0 : Int) + d3096 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3891, d3096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29281 p hg
    simpa only [d3891, d3096, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3891, d3096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29848 p hg
    simpa only [d3891, d3096, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30160 (p : Pattern) (guard : d5843 p = 1) : d3892 p ≤ (0 : Int) + d3097 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3892, d3097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29849 p hg
    simpa only [d3892, d3097, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3892, d3097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30159 p hg
    simpa only [d3892, d3097, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30161 (p : Pattern) (guard : d5843 p = 1) : d3893 p ≤ (0 : Int) + d3098 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3893, d3098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29277 p hg
    simpa only [d3893, d3098, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3893, d3098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30160 p hg
    simpa only [d3893, d3098, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30162 (p : Pattern) (guard : d5843 p = 1) : d3894 p ≤ (0 : Int) + d2031 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3894, d2031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29885 p hg
    simpa only [d3894, d2031, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3894, d2031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3894, d2031, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30163 (p : Pattern) (guard : d5843 p = 1) : d3895 p ≤ (0 : Int) + d3099 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3895, d3099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30161 p hg
    simpa only [d3895, d3099, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3895, d3099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30162 p hg
    simpa only [d3895, d3099, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30164 (p : Pattern) (guard : d5843 p = 1) : d3896 p ≤ (0 : Int) + d3100 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3896, d3100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29922 p hg
    simpa only [d3896, d3100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3896, d3100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30163 p hg
    simpa only [d3896, d3100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30165 (p : Pattern) (guard : d5843 p = 1) : d3897 p ≤ (0 : Int) + d3101 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3897, d3101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30144 p hg
    simpa only [d3897, d3101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3897, d3101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29942 p hg
    simpa only [d3897, d3101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30166 (p : Pattern) (guard : d5843 p = 1) : d3898 p ≤ (0 : Int) + d3102 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3898, d3102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30164 p hg
    simpa only [d3898, d3102, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3898, d3102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30165 p hg
    simpa only [d3898, d3102, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30167 (p : Pattern) (guard : d5843 p = 1) : d3899 p ≤ (0 : Int) + d3103 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3899, d3103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30144 p hg
    simpa only [d3899, d3103, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3899, d3103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29898 p hg
    simpa only [d3899, d3103, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30168 (p : Pattern) (guard : d5843 p = 1) : d3900 p ≤ (0 : Int) + d3104 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3900, d3104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30167 p hg
    simpa only [d3900, d3104, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3900, d3104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29902 p hg
    simpa only [d3900, d3104, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30169 (p : Pattern) (guard : d5843 p = 1) : d3901 p ≤ (0 : Int) + d3105 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3901, d3105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30166 p hg
    simpa only [d3901, d3105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3901, d3105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30168 p hg
    simpa only [d3901, d3105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30170 (p : Pattern) (guard : d5843 p = 1) : d3902 p ≤ (0 : Int) + d3106 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3902, d3106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30149 p hg
    simpa only [d3902, d3106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3902, d3106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29870 p hg
    simpa only [d3902, d3106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30171 (p : Pattern) (guard : d5843 p = 1) : d3903 p ≤ (0 : Int) + d3107 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3903, d3107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30152 p hg
    simpa only [d3903, d3107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3903, d3107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29912 p hg
    simpa only [d3903, d3107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30172 (p : Pattern) (guard : d5843 p = 1) : d3904 p ≤ (0 : Int) + d3108 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3904, d3108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30170 p hg
    simpa only [d3904, d3108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3904, d3108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30171 p hg
    simpa only [d3904, d3108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30173 (p : Pattern) (guard : d5843 p = 1) : d3905 p ≤ (0 : Int) + d3109 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3905, d3109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30152 p hg
    simpa only [d3905, d3109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3905, d3109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3905, d3109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30174 (p : Pattern) (guard : d5843 p = 1) : d3906 p ≤ (0 : Int) + d3110 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3906, d3110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30173 p hg
    simpa only [d3906, d3110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3906, d3110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3906, d3110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30175 (p : Pattern) (guard : d5843 p = 1) : d3907 p ≤ (0 : Int) + d3111 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3907, d3111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30172 p hg
    simpa only [d3907, d3111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3907, d3111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30174 p hg
    simpa only [d3907, d3111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30176 (p : Pattern) (guard : d5843 p = 1) : d3908 p ≤ (0 : Int) + d3112 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3908, d3112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30169 p hg
    simpa only [d3908, d3112, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3908, d3112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30175 p hg
    simpa only [d3908, d3112, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30177 (p : Pattern) (guard : d5843 p = 1) : d3909 p ≤ (0 : Int) + d3113 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3909, d3113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30158 p hg
    simpa only [d3909, d3113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3909, d3113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30176 p hg
    simpa only [d3909, d3113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30178 (p : Pattern) (guard : d5843 p = 1) : d3910 p ≤ (0 : Int) + d3114 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3910, d3114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29209 p hg
    simpa only [d3910, d3114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3910, d3114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29931 p hg
    simpa only [d3910, d3114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30179 (p : Pattern) (guard : d5843 p = 1) : d3911 p ≤ (0 : Int) + d2049 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3911, d2049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29919 p hg
    simpa only [d3911, d2049, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3911, d2049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3911, d2049, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30180 (p : Pattern) (guard : d5843 p = 1) : d3912 p ≤ (0 : Int) + d3115 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3912, d3115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30178 p hg
    simpa only [d3912, d3115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3912, d3115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30179 p hg
    simpa only [d3912, d3115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30181 (p : Pattern) (guard : d5843 p = 1) : d3667 p ≤ (0 : Int) + d2055 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3667, d2055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29926 p hg
    simpa only [d3667, d2055, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3667, d2055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3667, d2055, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30182 (p : Pattern) (guard : d5843 p = 1) : d3668 p ≤ (0 : Int) + d3116 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3668, d3116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29846 p hg
    simpa only [d3668, d3116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3668, d3116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30181 p hg
    simpa only [d3668, d3116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30183 (p : Pattern) (guard : d5843 p = 1) : d3913 p ≤ (0 : Int) + d3117 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3913, d3117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30180 p hg
    simpa only [d3913, d3117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3913, d3117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30182 p hg
    simpa only [d3913, d3117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30184 (p : Pattern) (guard : d5843 p = 1) : d3914 p ≤ (0 : Int) + d3118 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3914, d3118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30183 p hg
    simpa only [d3914, d3118, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3914, d3118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29949 p hg
    simpa only [d3914, d3118, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30185 (p : Pattern) (guard : d5843 p = 1) : d3915 p ≤ (0 : Int) + d3119 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3915, d3119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30184 p hg
    simpa only [d3915, d3119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3915, d3119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29950 p hg
    simpa only [d3915, d3119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30186 (p : Pattern) (guard : d5843 p = 1) : d3916 p ≤ (0 : Int) + d2060 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3916, d2060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29683 p hg
    simpa only [d3916, d2060, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3916, d2060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20964 p hg
    simpa only [d3916, d2060, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30187 (p : Pattern) (guard : d5843 p = 1) : d3917 p ≤ (0 : Int) + d2061 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3917, d2061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30186 p hg
    simpa only [d3917, d2061, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3917, d2061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20964 p hg
    simpa only [d3917, d2061, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30188 (p : Pattern) (guard : d5843 p = 1) : d3918 p ≤ (0 : Int) + d3120 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3918, d3120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29683 p hg
    simpa only [d3918, d3120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3918, d3120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30187 p hg
    simpa only [d3918, d3120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30189 (p : Pattern) (guard : d5843 p = 1) : d3919 p ≤ (0 : Int) + d2062 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3919, d2062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30187 p hg
    simpa only [d3919, d2062, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3919, d2062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3919, d2062, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30190 (p : Pattern) (guard : d5843 p = 1) : d3920 p ≤ (0 : Int) + d3121 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3920, d3121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30188 p hg
    simpa only [d3920, d3121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3920, d3121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30189 p hg
    simpa only [d3920, d3121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30191 (p : Pattern) (guard : d5843 p = 1) : d3921 p ≤ (0 : Int) + d3122 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3921, d3122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29938 p hg
    simpa only [d3921, d3122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3921, d3122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30190 p hg
    simpa only [d3921, d3122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30192 (p : Pattern) (guard : d5843 p = 1) : d3922 p ≤ (0 : Int) + d3123 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3922, d3123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30191 p hg
    simpa only [d3922, d3123, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3922, d3123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3922, d3123, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30193 (p : Pattern) (guard : d5843 p = 1) : d3923 p ≤ (0 : Int) + d3124 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3923, d3124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30192 p hg
    simpa only [d3923, d3124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3923, d3124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3923, d3124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30194 (p : Pattern) (guard : d5843 p = 1) : d3924 p ≤ (0 : Int) + d3125 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3924, d3125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30185 p hg
    simpa only [d3924, d3125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3924, d3125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30193 p hg
    simpa only [d3924, d3125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30195 (p : Pattern) (guard : d5843 p = 1) : d30 p ≤ (0 : Int) + d2068 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d30, d2068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14558 p hg
    simpa only [d5843, d30, d2068, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d30, d2068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23493 p hg
    simpa only [d5843, d30, d2068, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30196 (p : Pattern) (guard : d5843 p = 1) : d3925 p ≤ (0 : Int) + d2069 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3925, d2069, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30195 p hg
    simpa only [d3925, d2069, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3925, d2069, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19992 p hg
    simpa only [d3925, d2069, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30197 (p : Pattern) (guard : d5843 p = 1) : d3926 p ≤ (0 : Int) + d2070 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3926, d2070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29281 p hg
    simpa only [d3926, d2070, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3926, d2070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30196 p hg
    simpa only [d3926, d2070, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30198 (p : Pattern) (guard : d5843 p = 1) : d3927 p ≤ (0 : Int) + d2071 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3927, d2071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29849 p hg
    simpa only [d3927, d2071, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3927, d2071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30197 p hg
    simpa only [d3927, d2071, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30199 (p : Pattern) (guard : d5843 p = 1) : d3928 p ≤ (0 : Int) + d2072 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3928, d2072, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30198 p hg
    simpa only [d3928, d2072, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3928, d2072, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3928, d2072, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30200 (p : Pattern) (guard : d5843 p = 1) : d3929 p ≤ (0 : Int) + d3126 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3929, d3126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29905 p hg
    simpa only [d3929, d3126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3929, d3126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30199 p hg
    simpa only [d3929, d3126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30201 (p : Pattern) (guard : d5843 p = 1) : d3930 p ≤ (0 : Int) + d3127 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3930, d3127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30200 p hg
    simpa only [d3930, d3127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3930, d3127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29946 p hg
    simpa only [d3930, d3127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30202 (p : Pattern) (guard : d5843 p = 1) : d3931 p ≤ (0 : Int) + d3128 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3931, d3128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29938 p hg
    simpa only [d3931, d3128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3931, d3128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29901 p hg
    simpa only [d3931, d3128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30203 (p : Pattern) (guard : d5843 p = 1) : d3932 p ≤ (0 : Int) + d3129 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3932, d3129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30201 p hg
    simpa only [d3932, d3129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3932, d3129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30202 p hg
    simpa only [d3932, d3129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30204 (p : Pattern) (guard : d5843 p = 1) : d3933 p ≤ (0 : Int) + d3130 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3933, d3130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30203 p hg
    simpa only [d3933, d3130, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3933, d3130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29960 p hg
    simpa only [d3933, d3130, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30205 (p : Pattern) (guard : d5843 p = 1) : d3934 p ≤ (0 : Int) + d3131 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3934, d3131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30190 p hg
    simpa only [d3934, d3131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3934, d3131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3934, d3131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30206 (p : Pattern) (guard : d5843 p = 1) : d3935 p ≤ (0 : Int) + d3132 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3935, d3132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30205 p hg
    simpa only [d3935, d3132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3935, d3132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3935, d3132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30207 (p : Pattern) (guard : d5843 p = 1) : d3936 p ≤ (0 : Int) + d3133 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3936, d3133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30206 p hg
    simpa only [d3936, d3133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3936, d3133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3936, d3133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30208 (p : Pattern) (guard : d5843 p = 1) : d3937 p ≤ (0 : Int) + d3134 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3937, d3134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30204 p hg
    simpa only [d3937, d3134, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3937, d3134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30207 p hg
    simpa only [d3937, d3134, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30209 (p : Pattern) (guard : d5843 p = 1) : d3938 p ≤ (0 : Int) + d3135 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3938, d3135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30194 p hg
    simpa only [d3938, d3135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3938, d3135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30208 p hg
    simpa only [d3938, d3135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30210 (p : Pattern) (guard : d5843 p = 1) : d3939 p ≤ (0 : Int) + d3136 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3939, d3136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30177 p hg
    simpa only [d3939, d3136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3939, d3136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30209 p hg
    simpa only [d3939, d3136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30211 (p : Pattern) (guard : d5843 p = 1) : d3940 p ≤ (0 : Int) + d3137 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3940, d3137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30209 p hg
    simpa only [d3940, d3137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3940, d3137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3940, d3137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30212 (p : Pattern) (guard : d5843 p = 1) : d3941 p ≤ (0 : Int) + d3138 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3941, d3138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30210 p hg
    simpa only [d3941, d3138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3941, d3138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30211 p hg
    simpa only [d3941, d3138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30213 (p : Pattern) (guard : d5843 p = 1) : d3942 p ≤ (0 : Int) + d3139 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3942, d3139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29997 p hg
    simpa only [d3942, d3139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3942, d3139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30212 p hg
    simpa only [d3942, d3139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30214 (p : Pattern) (guard : d5843 p = 1) : d3943 p ≤ (0 : Int) + d3140 p := by
  cases selected : p 71 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3943, d3140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29986 p hg
    simpa only [d3943, d3140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3943, d3140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30213 p hg
    simpa only [d3943, d3140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30215 (p : Pattern) (guard : d5843 p = 1) : d3944 p ≤ (0 : Int) + d3141 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3944, d3141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30018 p hg
    simpa only [d3944, d3141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3944, d3141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3944, d3141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30216 (p : Pattern) (guard : d5843 p = 1) : d3945 p ≤ (0 : Int) + d3142 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3945, d3142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30064 p hg
    simpa only [d3945, d3142, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3945, d3142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30215 p hg
    simpa only [d3945, d3142, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30217 (p : Pattern) (guard : d5843 p = 1) : d3946 p ≤ (0 : Int) + d3143 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3946, d3143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30215 p hg
    simpa only [d3946, d3143, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3946, d3143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3946, d3143, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30218 (p : Pattern) (guard : d5843 p = 1) : d3947 p ≤ (0 : Int) + d3144 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3947, d3144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30216 p hg
    simpa only [d3947, d3144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3947, d3144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30217 p hg
    simpa only [d3947, d3144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30219 (p : Pattern) (guard : d5843 p = 1) : d3948 p ≤ (0 : Int) + d3145 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3948, d3145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30050 p hg
    simpa only [d3948, d3145, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3948, d3145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3948, d3145, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30220 (p : Pattern) (guard : d5843 p = 1) : d3949 p ≤ (0 : Int) + d3146 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3949, d3146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30072 p hg
    simpa only [d3949, d3146, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3949, d3146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30219 p hg
    simpa only [d3949, d3146, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30221 (p : Pattern) (guard : d5843 p = 1) : d3950 p ≤ (0 : Int) + d3147 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3950, d3147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30219 p hg
    simpa only [d3950, d3147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3950, d3147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3950, d3147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30222 (p : Pattern) (guard : d5843 p = 1) : d3951 p ≤ (0 : Int) + d3148 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3951, d3148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30220 p hg
    simpa only [d3951, d3148, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3951, d3148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30221 p hg
    simpa only [d3951, d3148, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30223 (p : Pattern) (guard : d5843 p = 1) : d3952 p ≤ (0 : Int) + d3149 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3952, d3149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30218 p hg
    simpa only [d3952, d3149, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3952, d3149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30222 p hg
    simpa only [d3952, d3149, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30224 (p : Pattern) (guard : d5843 p = 1) : d3953 p ≤ (0 : Int) + d3150 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3953, d3150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30056 p hg
    simpa only [d3953, d3150, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3953, d3150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30223 p hg
    simpa only [d3953, d3150, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30225 (p : Pattern) (guard : d5843 p = 1) : d3954 p ≤ (0 : Int) + d3151 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3954, d3151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30100 p hg
    simpa only [d3954, d3151, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3954, d3151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3954, d3151, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30226 (p : Pattern) (guard : d5843 p = 1) : d3955 p ≤ (0 : Int) + d3152 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3955, d3152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30112 p hg
    simpa only [d3955, d3152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3955, d3152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30225 p hg
    simpa only [d3955, d3152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30227 (p : Pattern) (guard : d5843 p = 1) : d3956 p ≤ (0 : Int) + d3153 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3956, d3153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30225 p hg
    simpa only [d3956, d3153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3956, d3153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3956, d3153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30228 (p : Pattern) (guard : d5843 p = 1) : d3957 p ≤ (0 : Int) + d3154 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3957, d3154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30226 p hg
    simpa only [d3957, d3154, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3957, d3154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30227 p hg
    simpa only [d3957, d3154, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30229 (p : Pattern) (guard : d5843 p = 1) : d3958 p ≤ (0 : Int) + d3155 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3958, d3155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30228 p hg
    simpa only [d3958, d3155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3958, d3155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30120 p hg
    simpa only [d3958, d3155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30230 (p : Pattern) (guard : d5843 p = 1) : d3959 p ≤ (0 : Int) + d3156 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3959, d3156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30111 p hg
    simpa only [d3959, d3156, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3959, d3156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30229 p hg
    simpa only [d3959, d3156, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30231 (p : Pattern) (guard : d5843 p = 1) : d3960 p ≤ (0 : Int) + d3157 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3960, d3157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30224 p hg
    simpa only [d3960, d3157, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3960, d3157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30230 p hg
    simpa only [d3960, d3157, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30232 (p : Pattern) (guard : d5843 p = 1) : d3961 p ≤ (0 : Int) + d3158 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3961, d3158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30230 p hg
    simpa only [d3961, d3158, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3961, d3158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30127 p hg
    simpa only [d3961, d3158, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30233 (p : Pattern) (guard : d5843 p = 1) : d3962 p ≤ (0 : Int) + d3159 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3962, d3159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30231 p hg
    simpa only [d3962, d3159, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3962, d3159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30232 p hg
    simpa only [d3962, d3159, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30234 (p : Pattern) (guard : d5843 p = 1) : d3963 p ≤ (0 : Int) + d3160 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3963, d3160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29466 p hg
    simpa only [d3963, d3160, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3963, d3160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30093 p hg
    simpa only [d3963, d3160, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30235 (p : Pattern) (guard : d5843 p = 1) : d3964 p ≤ (0 : Int) + d2109 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3964, d2109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30081 p hg
    simpa only [d3964, d2109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3964, d2109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3964, d2109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30236 (p : Pattern) (guard : d5843 p = 1) : d3965 p ≤ (0 : Int) + d3161 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3965, d3161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30234 p hg
    simpa only [d3965, d3161, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3965, d3161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30235 p hg
    simpa only [d3965, d3161, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30237 (p : Pattern) (guard : d5843 p = 1) : d3966 p ≤ (0 : Int) + d3162 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3966, d3162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30236 p hg
    simpa only [d3966, d3162, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3966, d3162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30100 p hg
    simpa only [d3966, d3162, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30238 (p : Pattern) (guard : d5843 p = 1) : d3967 p ≤ (0 : Int) + d3163 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3967, d3163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30084 p hg
    simpa only [d3967, d3163, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3967, d3163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30237 p hg
    simpa only [d3967, d3163, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30239 (p : Pattern) (guard : d5843 p = 1) : d3968 p ≤ (0 : Int) + d3164 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3968, d3164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30095 p hg
    simpa only [d3968, d3164, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3968, d3164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30100 p hg
    simpa only [d3968, d3164, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
