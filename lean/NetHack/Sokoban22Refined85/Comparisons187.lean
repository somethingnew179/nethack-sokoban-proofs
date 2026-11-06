/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons186
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare26180 (p : Pattern) (guard : d5843 p = 1) : d3096 p ≤ (0 : Int) + d3891 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3096, d3891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20575 p hg
    simpa only [d3096, d3891, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3096, d3891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25862 p hg
    simpa only [d3096, d3891, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26181 (p : Pattern) (guard : d5843 p = 1) : d3097 p ≤ (0 : Int) + d3892 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3097, d3892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25863 p hg
    simpa only [d3097, d3892, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3097, d3892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26180 p hg
    simpa only [d3097, d3892, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26182 (p : Pattern) (guard : d5843 p = 1) : d3098 p ≤ (0 : Int) + d3893 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3098, d3893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19918 p hg
    simpa only [d3098, d3893, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3098, d3893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26181 p hg
    simpa only [d3098, d3893, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26183 (p : Pattern) (guard : d5843 p = 1) : d2031 p ≤ (0 : Int) + d3894 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2031, d3894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25902 p hg
    simpa only [d2031, d3894, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2031, d3894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d2031, d3894, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26184 (p : Pattern) (guard : d5843 p = 1) : d3099 p ≤ (0 : Int) + d3895 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3099, d3895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26182 p hg
    simpa only [d3099, d3895, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3099, d3895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26183 p hg
    simpa only [d3099, d3895, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26185 (p : Pattern) (guard : d5843 p = 1) : d3100 p ≤ (0 : Int) + d3896 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3100, d3896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25939 p hg
    simpa only [d3100, d3896, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3100, d3896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26184 p hg
    simpa only [d3100, d3896, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26186 (p : Pattern) (guard : d5843 p = 1) : d3101 p ≤ (0 : Int) + d3897 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3101, d3897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26165 p hg
    simpa only [d3101, d3897, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3101, d3897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25959 p hg
    simpa only [d3101, d3897, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26187 (p : Pattern) (guard : d5843 p = 1) : d3102 p ≤ (0 : Int) + d3898 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3102, d3898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26185 p hg
    simpa only [d3102, d3898, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3102, d3898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26186 p hg
    simpa only [d3102, d3898, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26188 (p : Pattern) (guard : d5843 p = 1) : d3103 p ≤ (0 : Int) + d3899 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3103, d3899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26165 p hg
    simpa only [d3103, d3899, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3103, d3899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25915 p hg
    simpa only [d3103, d3899, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26189 (p : Pattern) (guard : d5843 p = 1) : d3104 p ≤ (0 : Int) + d3900 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3104, d3900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26188 p hg
    simpa only [d3104, d3900, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3104, d3900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25919 p hg
    simpa only [d3104, d3900, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26190 (p : Pattern) (guard : d5843 p = 1) : d3105 p ≤ (0 : Int) + d3901 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3105, d3901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26187 p hg
    simpa only [d3105, d3901, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3105, d3901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26189 p hg
    simpa only [d3105, d3901, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26191 (p : Pattern) (guard : d5843 p = 1) : d3106 p ≤ (0 : Int) + d3902 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3106, d3902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26170 p hg
    simpa only [d3106, d3902, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3106, d3902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25887 p hg
    simpa only [d3106, d3902, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26192 (p : Pattern) (guard : d5843 p = 1) : d3107 p ≤ (0 : Int) + d3903 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3107, d3903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26173 p hg
    simpa only [d3107, d3903, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3107, d3903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25929 p hg
    simpa only [d3107, d3903, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26193 (p : Pattern) (guard : d5843 p = 1) : d3108 p ≤ (0 : Int) + d3904 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3108, d3904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26191 p hg
    simpa only [d3108, d3904, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3108, d3904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26192 p hg
    simpa only [d3108, d3904, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26194 (p : Pattern) (guard : d5843 p = 1) : d3109 p ≤ (0 : Int) + d3905 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3109, d3905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26173 p hg
    simpa only [d3109, d3905, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3109, d3905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3109, d3905, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26195 (p : Pattern) (guard : d5843 p = 1) : d3110 p ≤ (0 : Int) + d3906 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3110, d3906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26194 p hg
    simpa only [d3110, d3906, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3110, d3906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3110, d3906, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26196 (p : Pattern) (guard : d5843 p = 1) : d3111 p ≤ (0 : Int) + d3907 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3111, d3907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26193 p hg
    simpa only [d3111, d3907, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3111, d3907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26195 p hg
    simpa only [d3111, d3907, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26197 (p : Pattern) (guard : d5843 p = 1) : d3112 p ≤ (0 : Int) + d3908 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3112, d3908, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26190 p hg
    simpa only [d3112, d3908, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3112, d3908, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26196 p hg
    simpa only [d3112, d3908, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26198 (p : Pattern) (guard : d5843 p = 1) : d3113 p ≤ (0 : Int) + d3909 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3113, d3909, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26179 p hg
    simpa only [d3113, d3909, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3113, d3909, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26197 p hg
    simpa only [d3113, d3909, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26199 (p : Pattern) (guard : d5843 p = 1) : d3114 p ≤ (0 : Int) + d3910 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3114, d3910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19834 p hg
    simpa only [d3114, d3910, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3114, d3910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25948 p hg
    simpa only [d3114, d3910, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26200 (p : Pattern) (guard : d5843 p = 1) : d2049 p ≤ (0 : Int) + d3911 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2049, d3911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25936 p hg
    simpa only [d2049, d3911, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2049, d3911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d2049, d3911, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26201 (p : Pattern) (guard : d5843 p = 1) : d3115 p ≤ (0 : Int) + d3912 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3115, d3912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26199 p hg
    simpa only [d3115, d3912, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3115, d3912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26200 p hg
    simpa only [d3115, d3912, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26202 (p : Pattern) (guard : d5843 p = 1) : d2055 p ≤ (0 : Int) + d3667 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2055, d3667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25943 p hg
    simpa only [d2055, d3667, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2055, d3667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d2055, d3667, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26203 (p : Pattern) (guard : d5843 p = 1) : d3116 p ≤ (0 : Int) + d3668 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3116, d3668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25860 p hg
    simpa only [d3116, d3668, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3116, d3668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26202 p hg
    simpa only [d3116, d3668, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26204 (p : Pattern) (guard : d5843 p = 1) : d3117 p ≤ (0 : Int) + d3913 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3117, d3913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26201 p hg
    simpa only [d3117, d3913, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3117, d3913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26203 p hg
    simpa only [d3117, d3913, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26205 (p : Pattern) (guard : d5843 p = 1) : d3118 p ≤ (0 : Int) + d3914 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3118, d3914, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26204 p hg
    simpa only [d3118, d3914, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3118, d3914, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25966 p hg
    simpa only [d3118, d3914, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26206 (p : Pattern) (guard : d5843 p = 1) : d3119 p ≤ (0 : Int) + d3915 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3119, d3915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26205 p hg
    simpa only [d3119, d3915, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3119, d3915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25967 p hg
    simpa only [d3119, d3915, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26207 (p : Pattern) (guard : d5843 p = 1) : d2060 p ≤ (0 : Int) + d3916 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2060, d3916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20379 p hg
    simpa only [d2060, d3916, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2060, d3916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20964 p hg
    simpa only [d2060, d3916, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26208 (p : Pattern) (guard : d5843 p = 1) : d2061 p ≤ (0 : Int) + d3917 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2061, d3917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26207 p hg
    simpa only [d2061, d3917, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2061, d3917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20964 p hg
    simpa only [d2061, d3917, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26209 (p : Pattern) (guard : d5843 p = 1) : d3120 p ≤ (0 : Int) + d3918 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3120, d3918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20379 p hg
    simpa only [d3120, d3918, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3120, d3918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26208 p hg
    simpa only [d3120, d3918, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26210 (p : Pattern) (guard : d5843 p = 1) : d2062 p ≤ (0 : Int) + d3919 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2062, d3919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26208 p hg
    simpa only [d2062, d3919, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2062, d3919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d2062, d3919, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26211 (p : Pattern) (guard : d5843 p = 1) : d3121 p ≤ (0 : Int) + d3920 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3121, d3920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26209 p hg
    simpa only [d3121, d3920, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3121, d3920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26210 p hg
    simpa only [d3121, d3920, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26212 (p : Pattern) (guard : d5843 p = 1) : d3122 p ≤ (0 : Int) + d3921 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3122, d3921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25955 p hg
    simpa only [d3122, d3921, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3122, d3921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26211 p hg
    simpa only [d3122, d3921, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26213 (p : Pattern) (guard : d5843 p = 1) : d3123 p ≤ (0 : Int) + d3922 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3123, d3922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26212 p hg
    simpa only [d3123, d3922, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3123, d3922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3123, d3922, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26214 (p : Pattern) (guard : d5843 p = 1) : d3124 p ≤ (0 : Int) + d3923 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3124, d3923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26213 p hg
    simpa only [d3124, d3923, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3124, d3923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3124, d3923, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26215 (p : Pattern) (guard : d5843 p = 1) : d3125 p ≤ (0 : Int) + d3924 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3125, d3924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26206 p hg
    simpa only [d3125, d3924, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3125, d3924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26214 p hg
    simpa only [d3125, d3924, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26216 (p : Pattern) (guard : d5843 p = 1) : d2068 p ≤ (0 : Int) + d30 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d2068, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14558 p hg
    simpa only [d5843, d2068, d30, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d2068, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19990 p hg
    simpa only [d5843, d2068, d30, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26217 (p : Pattern) (guard : d5843 p = 1) : d2069 p ≤ (0 : Int) + d3925 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2069, d3925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26216 p hg
    simpa only [d2069, d3925, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2069, d3925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19992 p hg
    simpa only [d2069, d3925, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26218 (p : Pattern) (guard : d5843 p = 1) : d2070 p ≤ (0 : Int) + d3926 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2070, d3926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20575 p hg
    simpa only [d2070, d3926, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2070, d3926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26217 p hg
    simpa only [d2070, d3926, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26219 (p : Pattern) (guard : d5843 p = 1) : d2071 p ≤ (0 : Int) + d3927 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2071, d3927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25863 p hg
    simpa only [d2071, d3927, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2071, d3927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26218 p hg
    simpa only [d2071, d3927, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26220 (p : Pattern) (guard : d5843 p = 1) : d2072 p ≤ (0 : Int) + d3928 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2072, d3928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26219 p hg
    simpa only [d2072, d3928, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2072, d3928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d2072, d3928, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26221 (p : Pattern) (guard : d5843 p = 1) : d3126 p ≤ (0 : Int) + d3929 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3126, d3929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25922 p hg
    simpa only [d3126, d3929, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3126, d3929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26220 p hg
    simpa only [d3126, d3929, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26222 (p : Pattern) (guard : d5843 p = 1) : d3127 p ≤ (0 : Int) + d3930 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3127, d3930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26221 p hg
    simpa only [d3127, d3930, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3127, d3930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25963 p hg
    simpa only [d3127, d3930, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26223 (p : Pattern) (guard : d5843 p = 1) : d3128 p ≤ (0 : Int) + d3931 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3128, d3931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25955 p hg
    simpa only [d3128, d3931, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3128, d3931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25918 p hg
    simpa only [d3128, d3931, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26224 (p : Pattern) (guard : d5843 p = 1) : d3129 p ≤ (0 : Int) + d3932 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3129, d3932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26222 p hg
    simpa only [d3129, d3932, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3129, d3932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26223 p hg
    simpa only [d3129, d3932, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26225 (p : Pattern) (guard : d5843 p = 1) : d3130 p ≤ (0 : Int) + d3933 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3130, d3933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26224 p hg
    simpa only [d3130, d3933, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3130, d3933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25977 p hg
    simpa only [d3130, d3933, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26226 (p : Pattern) (guard : d5843 p = 1) : d3131 p ≤ (0 : Int) + d3934 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3131, d3934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26211 p hg
    simpa only [d3131, d3934, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3131, d3934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3131, d3934, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26227 (p : Pattern) (guard : d5843 p = 1) : d3132 p ≤ (0 : Int) + d3935 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3132, d3935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26226 p hg
    simpa only [d3132, d3935, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3132, d3935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3132, d3935, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26228 (p : Pattern) (guard : d5843 p = 1) : d3133 p ≤ (0 : Int) + d3936 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3133, d3936, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26227 p hg
    simpa only [d3133, d3936, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3133, d3936, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3133, d3936, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26229 (p : Pattern) (guard : d5843 p = 1) : d3134 p ≤ (0 : Int) + d3937 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3134, d3937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26225 p hg
    simpa only [d3134, d3937, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3134, d3937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26228 p hg
    simpa only [d3134, d3937, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26230 (p : Pattern) (guard : d5843 p = 1) : d3135 p ≤ (0 : Int) + d3938 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3135, d3938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26215 p hg
    simpa only [d3135, d3938, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3135, d3938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26229 p hg
    simpa only [d3135, d3938, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26231 (p : Pattern) (guard : d5843 p = 1) : d3136 p ≤ (0 : Int) + d3939 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3136, d3939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26198 p hg
    simpa only [d3136, d3939, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3136, d3939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26230 p hg
    simpa only [d3136, d3939, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26232 (p : Pattern) (guard : d5843 p = 1) : d3137 p ≤ (0 : Int) + d3940 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3137, d3940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26230 p hg
    simpa only [d3137, d3940, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3137, d3940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3137, d3940, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26233 (p : Pattern) (guard : d5843 p = 1) : d3138 p ≤ (0 : Int) + d3941 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3138, d3941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26231 p hg
    simpa only [d3138, d3941, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3138, d3941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26232 p hg
    simpa only [d3138, d3941, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26234 (p : Pattern) (guard : d5843 p = 1) : d3139 p ≤ (0 : Int) + d3942 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3139, d3942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26014 p hg
    simpa only [d3139, d3942, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3139, d3942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26233 p hg
    simpa only [d3139, d3942, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26235 (p : Pattern) (guard : d5843 p = 1) : d3140 p ≤ (0 : Int) + d3943 p := by
  cases selected : p 71 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3140, d3943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26003 p hg
    simpa only [d3140, d3943, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3140, d3943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26234 p hg
    simpa only [d3140, d3943, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26236 (p : Pattern) (guard : d5843 p = 1) : d3141 p ≤ (0 : Int) + d3944 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3141, d3944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26035 p hg
    simpa only [d3141, d3944, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3141, d3944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3141, d3944, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26237 (p : Pattern) (guard : d5843 p = 1) : d3142 p ≤ (0 : Int) + d3945 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3142, d3945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26085 p hg
    simpa only [d3142, d3945, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3142, d3945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26236 p hg
    simpa only [d3142, d3945, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26238 (p : Pattern) (guard : d5843 p = 1) : d3143 p ≤ (0 : Int) + d3946 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3143, d3946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26236 p hg
    simpa only [d3143, d3946, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3143, d3946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3143, d3946, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26239 (p : Pattern) (guard : d5843 p = 1) : d3144 p ≤ (0 : Int) + d3947 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3144, d3947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26237 p hg
    simpa only [d3144, d3947, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3144, d3947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26238 p hg
    simpa only [d3144, d3947, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26240 (p : Pattern) (guard : d5843 p = 1) : d3145 p ≤ (0 : Int) + d3948 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3145, d3948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26071 p hg
    simpa only [d3145, d3948, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3145, d3948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3145, d3948, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26241 (p : Pattern) (guard : d5843 p = 1) : d3146 p ≤ (0 : Int) + d3949 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3146, d3949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26093 p hg
    simpa only [d3146, d3949, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3146, d3949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26240 p hg
    simpa only [d3146, d3949, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26242 (p : Pattern) (guard : d5843 p = 1) : d3147 p ≤ (0 : Int) + d3950 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3147, d3950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26240 p hg
    simpa only [d3147, d3950, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3147, d3950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3147, d3950, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26243 (p : Pattern) (guard : d5843 p = 1) : d3148 p ≤ (0 : Int) + d3951 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3148, d3951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26241 p hg
    simpa only [d3148, d3951, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3148, d3951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26242 p hg
    simpa only [d3148, d3951, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26244 (p : Pattern) (guard : d5843 p = 1) : d3149 p ≤ (0 : Int) + d3952 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3149, d3952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26239 p hg
    simpa only [d3149, d3952, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3149, d3952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26243 p hg
    simpa only [d3149, d3952, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26245 (p : Pattern) (guard : d5843 p = 1) : d3150 p ≤ (0 : Int) + d3953 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3150, d3953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26077 p hg
    simpa only [d3150, d3953, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3150, d3953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26244 p hg
    simpa only [d3150, d3953, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26246 (p : Pattern) (guard : d5843 p = 1) : d3151 p ≤ (0 : Int) + d3954 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3151, d3954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26121 p hg
    simpa only [d3151, d3954, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3151, d3954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3151, d3954, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26247 (p : Pattern) (guard : d5843 p = 1) : d3152 p ≤ (0 : Int) + d3955 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3152, d3955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26133 p hg
    simpa only [d3152, d3955, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3152, d3955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26246 p hg
    simpa only [d3152, d3955, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26248 (p : Pattern) (guard : d5843 p = 1) : d3153 p ≤ (0 : Int) + d3956 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3153, d3956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26246 p hg
    simpa only [d3153, d3956, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3153, d3956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3153, d3956, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26249 (p : Pattern) (guard : d5843 p = 1) : d3154 p ≤ (0 : Int) + d3957 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3154, d3957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26247 p hg
    simpa only [d3154, d3957, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3154, d3957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26248 p hg
    simpa only [d3154, d3957, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26250 (p : Pattern) (guard : d5843 p = 1) : d3155 p ≤ (0 : Int) + d3958 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3155, d3958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26249 p hg
    simpa only [d3155, d3958, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3155, d3958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26141 p hg
    simpa only [d3155, d3958, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26251 (p : Pattern) (guard : d5843 p = 1) : d3156 p ≤ (0 : Int) + d3959 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3156, d3959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26132 p hg
    simpa only [d3156, d3959, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3156, d3959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26250 p hg
    simpa only [d3156, d3959, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26252 (p : Pattern) (guard : d5843 p = 1) : d3157 p ≤ (0 : Int) + d3960 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3157, d3960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26245 p hg
    simpa only [d3157, d3960, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3157, d3960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26251 p hg
    simpa only [d3157, d3960, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26253 (p : Pattern) (guard : d5843 p = 1) : d3158 p ≤ (0 : Int) + d3961 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3158, d3961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26251 p hg
    simpa only [d3158, d3961, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3158, d3961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26148 p hg
    simpa only [d3158, d3961, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26254 (p : Pattern) (guard : d5843 p = 1) : d3159 p ≤ (0 : Int) + d3962 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3159, d3962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26252 p hg
    simpa only [d3159, d3962, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3159, d3962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26253 p hg
    simpa only [d3159, d3962, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26255 (p : Pattern) (guard : d5843 p = 1) : d3160 p ≤ (0 : Int) + d3963 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3160, d3963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20140 p hg
    simpa only [d3160, d3963, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3160, d3963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26114 p hg
    simpa only [d3160, d3963, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26256 (p : Pattern) (guard : d5843 p = 1) : d2109 p ≤ (0 : Int) + d3964 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2109, d3964, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26102 p hg
    simpa only [d2109, d3964, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2109, d3964, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d2109, d3964, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26257 (p : Pattern) (guard : d5843 p = 1) : d3161 p ≤ (0 : Int) + d3965 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3161, d3965, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26255 p hg
    simpa only [d3161, d3965, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3161, d3965, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26256 p hg
    simpa only [d3161, d3965, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26258 (p : Pattern) (guard : d5843 p = 1) : d3162 p ≤ (0 : Int) + d3966 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3162, d3966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26257 p hg
    simpa only [d3162, d3966, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3162, d3966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26121 p hg
    simpa only [d3162, d3966, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26259 (p : Pattern) (guard : d5843 p = 1) : d3163 p ≤ (0 : Int) + d3967 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3163, d3967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26105 p hg
    simpa only [d3163, d3967, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3163, d3967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26258 p hg
    simpa only [d3163, d3967, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26260 (p : Pattern) (guard : d5843 p = 1) : d3164 p ≤ (0 : Int) + d3968 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3164, d3968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26116 p hg
    simpa only [d3164, d3968, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3164, d3968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26121 p hg
    simpa only [d3164, d3968, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26261 (p : Pattern) (guard : d5843 p = 1) : d3165 p ≤ (0 : Int) + d3969 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3165, d3969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26260 p hg
    simpa only [d3165, d3969, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3165, d3969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26038 p hg
    simpa only [d3165, d3969, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26262 (p : Pattern) (guard : d5843 p = 1) : d3166 p ≤ (0 : Int) + d3970 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3166, d3970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26259 p hg
    simpa only [d3166, d3970, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3166, d3970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26261 p hg
    simpa only [d3166, d3970, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26263 (p : Pattern) (guard : d5843 p = 1) : d3167 p ≤ (0 : Int) + d3971 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3167, d3971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26091 p hg
    simpa only [d3167, d3971, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3167, d3971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26060 p hg
    simpa only [d3167, d3971, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26264 (p : Pattern) (guard : d5843 p = 1) : d3168 p ≤ (0 : Int) + d3972 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3168, d3972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26126 p hg
    simpa only [d3168, d3972, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3168, d3972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26263 p hg
    simpa only [d3168, d3972, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26265 (p : Pattern) (guard : d5843 p = 1) : d3169 p ≤ (0 : Int) + d3973 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3169, d3973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26264 p hg
    simpa only [d3169, d3973, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3169, d3973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26240 p hg
    simpa only [d3169, d3973, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26266 (p : Pattern) (guard : d5843 p = 1) : d3170 p ≤ (0 : Int) + d3974 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3170, d3974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26127 p hg
    simpa only [d3170, d3974, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3170, d3974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3170, d3974, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26267 (p : Pattern) (guard : d5843 p = 1) : d3171 p ≤ (0 : Int) + d3975 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3171, d3975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26266 p hg
    simpa only [d3171, d3975, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3171, d3975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3171, d3975, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26268 (p : Pattern) (guard : d5843 p = 1) : d3172 p ≤ (0 : Int) + d3976 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3172, d3976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26267 p hg
    simpa only [d3172, d3976, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3172, d3976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3172, d3976, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26269 (p : Pattern) (guard : d5843 p = 1) : d3173 p ≤ (0 : Int) + d3977 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3173, d3977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26265 p hg
    simpa only [d3173, d3977, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3173, d3977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26268 p hg
    simpa only [d3173, d3977, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26270 (p : Pattern) (guard : d5843 p = 1) : d3174 p ≤ (0 : Int) + d3978 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3174, d3978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26262 p hg
    simpa only [d3174, d3978, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3174, d3978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26269 p hg
    simpa only [d3174, d3978, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26271 (p : Pattern) (guard : d5843 p = 1) : d3175 p ≤ (0 : Int) + d3979 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3175, d3979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20797 p hg
    simpa only [d3175, d3979, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3175, d3979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26049 p hg
    simpa only [d3175, d3979, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26272 (p : Pattern) (guard : d5843 p = 1) : d3176 p ≤ (0 : Int) + d3980 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3176, d3980, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26050 p hg
    simpa only [d3176, d3980, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3176, d3980, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26271 p hg
    simpa only [d3176, d3980, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26273 (p : Pattern) (guard : d5843 p = 1) : d3177 p ≤ (0 : Int) + d3981 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3177, d3981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20199 p hg
    simpa only [d3177, d3981, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3177, d3981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26272 p hg
    simpa only [d3177, d3981, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26274 (p : Pattern) (guard : d5843 p = 1) : d2126 p ≤ (0 : Int) + d3982 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2126, d3982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26079 p hg
    simpa only [d2126, d3982, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2126, d3982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d2126, d3982, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26275 (p : Pattern) (guard : d5843 p = 1) : d3178 p ≤ (0 : Int) + d3983 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3178, d3983, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26273 p hg
    simpa only [d3178, d3983, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3178, d3983, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26274 p hg
    simpa only [d3178, d3983, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26276 (p : Pattern) (guard : d5843 p = 1) : d3179 p ≤ (0 : Int) + d3984 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3179, d3984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26257 p hg
    simpa only [d3179, d3984, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3179, d3984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26275 p hg
    simpa only [d3179, d3984, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26277 (p : Pattern) (guard : d5843 p = 1) : d2135 p ≤ (0 : Int) + d3985 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2135, d3985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20772 p hg
    simpa only [d2135, d3985, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2135, d3985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26065 p hg
    simpa only [d2135, d3985, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26278 (p : Pattern) (guard : d5843 p = 1) : d2136 p ≤ (0 : Int) + d3986 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2136, d3986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26066 p hg
    simpa only [d2136, d3986, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2136, d3986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26277 p hg
    simpa only [d2136, d3986, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26279 (p : Pattern) (guard : d5843 p = 1) : d3180 p ≤ (0 : Int) + d3987 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3180, d3987, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20167 p hg
    simpa only [d3180, d3987, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3180, d3987, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26278 p hg
    simpa only [d3180, d3987, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26280 (p : Pattern) (guard : d5843 p = 1) : d2131 p ≤ (0 : Int) + d3988 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2131, d3988, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26030 p hg
    simpa only [d2131, d3988, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2131, d3988, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d2131, d3988, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26281 (p : Pattern) (guard : d5843 p = 1) : d3181 p ≤ (0 : Int) + d3989 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3181, d3989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26279 p hg
    simpa only [d3181, d3989, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3181, d3989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26280 p hg
    simpa only [d3181, d3989, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26282 (p : Pattern) (guard : d5843 p = 1) : d3182 p ≤ (0 : Int) + d3990 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3182, d3990, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26281 p hg
    simpa only [d3182, d3990, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3182, d3990, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3182, d3990, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26283 (p : Pattern) (guard : d5843 p = 1) : d3183 p ≤ (0 : Int) + d3991 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3183, d3991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26276 p hg
    simpa only [d3183, d3991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3183, d3991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26282 p hg
    simpa only [d3183, d3991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26284 (p : Pattern) (guard : d5843 p = 1) : d2137 p ≤ (0 : Int) + d3992 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2137, d3992, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26278 p hg
    simpa only [d2137, d3992, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2137, d3992, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d2137, d3992, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26285 (p : Pattern) (guard : d5843 p = 1) : d3184 p ≤ (0 : Int) + d3993 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3184, d3993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26070 p hg
    simpa only [d3184, d3993, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3184, d3993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26284 p hg
    simpa only [d3184, d3993, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26286 (p : Pattern) (guard : d5843 p = 1) : d3185 p ≤ (0 : Int) + d3994 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3185, d3994, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26285 p hg
    simpa only [d3185, d3994, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3185, d3994, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3185, d3994, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26287 (p : Pattern) (guard : d5843 p = 1) : d3186 p ≤ (0 : Int) + d3995 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3186, d3995, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26286 p hg
    simpa only [d3186, d3995, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3186, d3995, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3186, d3995, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26288 (p : Pattern) (guard : d5843 p = 1) : d3187 p ≤ (0 : Int) + d3996 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3187, d3996, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26283 p hg
    simpa only [d3187, d3996, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3187, d3996, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26287 p hg
    simpa only [d3187, d3996, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26289 (p : Pattern) (guard : d5843 p = 1) : d3188 p ≤ (0 : Int) + d3997 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3188, d3997, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26070 p hg
    simpa only [d3188, d3997, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3188, d3997, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26060 p hg
    simpa only [d3188, d3997, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26290 (p : Pattern) (guard : d5843 p = 1) : d3189 p ≤ (0 : Int) + d3998 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3189, d3998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26289 p hg
    simpa only [d3189, d3998, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3189, d3998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26071 p hg
    simpa only [d3189, d3998, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26291 (p : Pattern) (guard : d5843 p = 1) : d3190 p ≤ (0 : Int) + d3999 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3190, d3999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26290 p hg
    simpa only [d3190, d3999, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3190, d3999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26267 p hg
    simpa only [d3190, d3999, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26292 (p : Pattern) (guard : d5843 p = 1) : d3191 p ≤ (0 : Int) + d4000 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3191, d4000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25893 p hg
    simpa only [d3191, d4000, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3191, d4000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3191, d4000, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26293 (p : Pattern) (guard : d5843 p = 1) : d3192 p ≤ (0 : Int) + d4001 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3192, d4001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26291 p hg
    simpa only [d3192, d4001, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3192, d4001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26292 p hg
    simpa only [d3192, d4001, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26294 (p : Pattern) (guard : d5843 p = 1) : d3193 p ≤ (0 : Int) + d4002 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3193, d4002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26288 p hg
    simpa only [d3193, d4002, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3193, d4002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26293 p hg
    simpa only [d3193, d4002, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26295 (p : Pattern) (guard : d5843 p = 1) : d3194 p ≤ (0 : Int) + d4003 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3194, d4003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26270 p hg
    simpa only [d3194, d4003, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3194, d4003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26294 p hg
    simpa only [d3194, d4003, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26296 (p : Pattern) (guard : d5843 p = 1) : d3195 p ≤ (0 : Int) + d4004 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3195, d4004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26116 p hg
    simpa only [d3195, d4004, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3195, d4004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26119 p hg
    simpa only [d3195, d4004, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26297 (p : Pattern) (guard : d5843 p = 1) : d3196 p ≤ (0 : Int) + d4005 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3196, d4005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26126 p hg
    simpa only [d3196, d4005, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3196, d4005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25918 p hg
    simpa only [d3196, d4005, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26298 (p : Pattern) (guard : d5843 p = 1) : d3197 p ≤ (0 : Int) + d4006 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3197, d4006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26296 p hg
    simpa only [d3197, d4006, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3197, d4006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26297 p hg
    simpa only [d3197, d4006, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26299 (p : Pattern) (guard : d5843 p = 1) : d3198 p ≤ (0 : Int) + d4007 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3198, d4007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26298 p hg
    simpa only [d3198, d4007, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3198, d4007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26137 p hg
    simpa only [d3198, d4007, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26300 (p : Pattern) (guard : d5843 p = 1) : d3199 p ≤ (0 : Int) + d4008 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3199, d4008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26299 p hg
    simpa only [d3199, d4008, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3199, d4008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26141 p hg
    simpa only [d3199, d4008, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26301 (p : Pattern) (guard : d5843 p = 1) : d2154 p ≤ (0 : Int) + d115 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d2154, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14667 p hg
    simpa only [d5843, d2154, d115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d2154, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19937 p hg
    simpa only [d5843, d2154, d115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26302 (p : Pattern) (guard : d5843 p = 1) : d2155 p ≤ (0 : Int) + d326 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2155, d326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26301 p hg
    simpa only [d2155, d326, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2155, d326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19939 p hg
    simpa only [d2155, d326, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26303 (p : Pattern) (guard : d5843 p = 1) : d2156 p ≤ (0 : Int) + d4009 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2156, d4009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20797 p hg
    simpa only [d2156, d4009, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2156, d4009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26302 p hg
    simpa only [d2156, d4009, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26304 (p : Pattern) (guard : d5843 p = 1) : d2157 p ≤ (0 : Int) + d4010 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2157, d4010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26050 p hg
    simpa only [d2157, d4010, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2157, d4010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26303 p hg
    simpa only [d2157, d4010, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26305 (p : Pattern) (guard : d5843 p = 1) : d2158 p ≤ (0 : Int) + d4011 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2158, d4011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26304 p hg
    simpa only [d2158, d4011, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2158, d4011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d2158, d4011, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26306 (p : Pattern) (guard : d5843 p = 1) : d3200 p ≤ (0 : Int) + d4012 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3200, d4012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26091 p hg
    simpa only [d3200, d4012, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3200, d4012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26305 p hg
    simpa only [d3200, d4012, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26307 (p : Pattern) (guard : d5843 p = 1) : d3201 p ≤ (0 : Int) + d4013 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3201, d4013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26306 p hg
    simpa only [d3201, d4013, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3201, d4013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26126 p hg
    simpa only [d3201, d4013, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26308 (p : Pattern) (guard : d5843 p = 1) : d3202 p ≤ (0 : Int) + d4014 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3202, d4014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26307 p hg
    simpa only [d3202, d4014, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3202, d4014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26246 p hg
    simpa only [d3202, d4014, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26309 (p : Pattern) (guard : d5843 p = 1) : d3203 p ≤ (0 : Int) + d4015 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3203, d4015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26308 p hg
    simpa only [d3203, d4015, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3203, d4015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26140 p hg
    simpa only [d3203, d4015, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26310 (p : Pattern) (guard : d5843 p = 1) : d3204 p ≤ (0 : Int) + d4016 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3204, d4016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25960 p hg
    simpa only [d3204, d4016, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3204, d4016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3204, d4016, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26311 (p : Pattern) (guard : d5843 p = 1) : d3205 p ≤ (0 : Int) + d4017 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3205, d4017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26310 p hg
    simpa only [d3205, d4017, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3205, d4017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3205, d4017, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26312 (p : Pattern) (guard : d5843 p = 1) : d3206 p ≤ (0 : Int) + d4018 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3206, d4018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26309 p hg
    simpa only [d3206, d4018, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3206, d4018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26311 p hg
    simpa only [d3206, d4018, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26313 (p : Pattern) (guard : d5843 p = 1) : d3207 p ≤ (0 : Int) + d4019 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3207, d4019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26300 p hg
    simpa only [d3207, d4019, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3207, d4019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26312 p hg
    simpa only [d3207, d4019, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26314 (p : Pattern) (guard : d5843 p = 1) : d3208 p ≤ (0 : Int) + d4020 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3208, d4020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26295 p hg
    simpa only [d3208, d4020, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3208, d4020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26313 p hg
    simpa only [d3208, d4020, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26315 (p : Pattern) (guard : d5843 p = 1) : d3209 p ≤ (0 : Int) + d4021 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3209, d4021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26126 p hg
    simpa only [d3209, d4021, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3209, d4021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25959 p hg
    simpa only [d3209, d4021, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26316 (p : Pattern) (guard : d5843 p = 1) : d3210 p ≤ (0 : Int) + d4022 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3210, d4022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26296 p hg
    simpa only [d3210, d4022, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3210, d4022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26315 p hg
    simpa only [d3210, d4022, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26317 (p : Pattern) (guard : d5843 p = 1) : d3211 p ≤ (0 : Int) + d4023 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3211, d4023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26121 p hg
    simpa only [d3211, d4023, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3211, d4023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25959 p hg
    simpa only [d3211, d4023, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26318 (p : Pattern) (guard : d5843 p = 1) : d3212 p ≤ (0 : Int) + d4024 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3212, d4024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26317 p hg
    simpa only [d3212, d4024, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3212, d4024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3212, d4024, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26319 (p : Pattern) (guard : d5843 p = 1) : d3213 p ≤ (0 : Int) + d4025 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3213, d4025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26316 p hg
    simpa only [d3213, d4025, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3213, d4025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26318 p hg
    simpa only [d3213, d4025, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
