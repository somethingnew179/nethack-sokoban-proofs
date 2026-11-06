/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons239
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare33600 (p : Pattern) (guard : d5843 p = 1) : d3058 p ≤ (2 : Int) + d7900 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3058, d7900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33585 p hg
    simpa only [d3058, d7900, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3058, d7900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33379 p hg
    simpa only [d3058, d7900, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33601 (p : Pattern) (guard : d5843 p = 1) : d3059 p ≤ (2 : Int) + d7901 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3059, d7901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33600 p hg
    simpa only [d3059, d7901, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3059, d7901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33260 p hg
    simpa only [d3059, d7901, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33602 (p : Pattern) (guard : d5843 p = 1) : d3060 p ≤ (2 : Int) + d7902 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3060, d7902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33599 p hg
    simpa only [d3060, d7902, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3060, d7902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33601 p hg
    simpa only [d3060, d7902, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33603 (p : Pattern) (guard : d5843 p = 1) : d3061 p ≤ (2 : Int) + d7903 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3061, d7903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33592 p hg
    simpa only [d3061, d7903, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3061, d7903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33260 p hg
    simpa only [d3061, d7903, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33604 (p : Pattern) (guard : d5843 p = 1) : d3062 p ≤ (2 : Int) + d7904 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3062, d7904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33603 p hg
    simpa only [d3062, d7904, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3062, d7904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33260 p hg
    simpa only [d3062, d7904, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33605 (p : Pattern) (guard : d5843 p = 1) : d3063 p ≤ (2 : Int) + d7905 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3063, d7905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33604 p hg
    simpa only [d3063, d7905, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3063, d7905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33260 p hg
    simpa only [d3063, d7905, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33606 (p : Pattern) (guard : d5843 p = 1) : d3064 p ≤ (2 : Int) + d7906 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3064, d7906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33602 p hg
    simpa only [d3064, d7906, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3064, d7906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33605 p hg
    simpa only [d3064, d7906, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33607 (p : Pattern) (guard : d5843 p = 1) : d3065 p ≤ (2 : Int) + d7907 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3065, d7907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33596 p hg
    simpa only [d3065, d7907, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3065, d7907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33606 p hg
    simpa only [d3065, d7907, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33608 (p : Pattern) (guard : d5843 p = 1) : d3066 p ≤ (2 : Int) + d7908 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3066, d7908, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33564 p hg
    simpa only [d3066, d7908, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3066, d7908, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33607 p hg
    simpa only [d3066, d7908, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33609 (p : Pattern) (guard : d5843 p = 1) : d3067 p ≤ (2 : Int) + d7909 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3067, d7909, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33492 p hg
    simpa only [d3067, d7909, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3067, d7909, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33260 p hg
    simpa only [d3067, d7909, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33610 (p : Pattern) (guard : d5843 p = 1) : d3068 p ≤ (2 : Int) + d7910 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3068, d7910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33609 p hg
    simpa only [d3068, d7910, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3068, d7910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33260 p hg
    simpa only [d3068, d7910, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33611 (p : Pattern) (guard : d5843 p = 1) : d3069 p ≤ (2 : Int) + d7911 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3069, d7911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33610 p hg
    simpa only [d3069, d7911, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3069, d7911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33260 p hg
    simpa only [d3069, d7911, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33612 (p : Pattern) (guard : d5843 p = 1) : d3070 p ≤ (2 : Int) + d7912 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3070, d7912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33611 p hg
    simpa only [d3070, d7912, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3070, d7912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33260 p hg
    simpa only [d3070, d7912, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33613 (p : Pattern) (guard : d5843 p = 1) : d3071 p ≤ (2 : Int) + d7913 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3071, d7913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33607 p hg
    simpa only [d3071, d7913, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3071, d7913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33612 p hg
    simpa only [d3071, d7913, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33614 (p : Pattern) (guard : d5843 p = 1) : d3072 p ≤ (2 : Int) + d7914 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3072, d7914, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33608 p hg
    simpa only [d3072, d7914, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3072, d7914, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33613 p hg
    simpa only [d3072, d7914, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33615 (p : Pattern) (guard : d5843 p = 1) : d3073 p ≤ (2 : Int) + d7915 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3073, d7915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33607 p hg
    simpa only [d3073, d7915, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3073, d7915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33260 p hg
    simpa only [d3073, d7915, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33616 (p : Pattern) (guard : d5843 p = 1) : d3074 p ≤ (2 : Int) + d7916 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3074, d7916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33608 p hg
    simpa only [d3074, d7916, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3074, d7916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33615 p hg
    simpa only [d3074, d7916, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33617 (p : Pattern) (guard : d5843 p = 1) : d3075 p ≤ (2 : Int) + d7917 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3075, d7917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33614 p hg
    simpa only [d3075, d7917, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3075, d7917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33616 p hg
    simpa only [d3075, d7917, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33618 (p : Pattern) (guard : d5843 p = 1) : d3076 p ≤ (2 : Int) + d7918 p := by
  cases selected : p 71 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3076, d7918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33455 p hg
    simpa only [d3076, d7918, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3076, d7918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33617 p hg
    simpa only [d3076, d7918, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33619 (p : Pattern) (guard : d5843 p = 1) : d3077 p ≤ (2 : Int) + d7919 p := by
  cases selected : p 49 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3077, d7919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33455 p hg
    simpa only [d3077, d7919, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3077, d7919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33618 p hg
    simpa only [d3077, d7919, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33620 (p : Pattern) (guard : d5843 p = 1) : d3078 p ≤ (2 : Int) + d7920 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3078, d7920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33268 p hg
    simpa only [d3078, d7920, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3078, d7920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33341 p hg
    simpa only [d3078, d7920, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33621 (p : Pattern) (guard : d5843 p = 1) : d3079 p ≤ (2 : Int) + d7921 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3079, d7921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33342 p hg
    simpa only [d3079, d7921, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3079, d7921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33620 p hg
    simpa only [d3079, d7921, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33622 (p : Pattern) (guard : d5843 p = 1) : d3080 p ≤ (2 : Int) + d7922 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3080, d7922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33264 p hg
    simpa only [d3080, d7922, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3080, d7922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33621 p hg
    simpa only [d3080, d7922, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33623 (p : Pattern) (guard : d5843 p = 1) : d2013 p ≤ (2 : Int) + d7923 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2013, d7923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33270 p hg
    simpa only [d2013, d7923, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2013, d7923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33260 p hg
    simpa only [d2013, d7923, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33624 (p : Pattern) (guard : d5843 p = 1) : d3081 p ≤ (2 : Int) + d7924 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3081, d7924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33622 p hg
    simpa only [d3081, d7924, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3081, d7924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33623 p hg
    simpa only [d3081, d7924, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33625 (p : Pattern) (guard : d5843 p = 1) : d3082 p ≤ (2 : Int) + d7925 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3082, d7925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33400 p hg
    simpa only [d3082, d7925, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3082, d7925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33624 p hg
    simpa only [d3082, d7925, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33626 (p : Pattern) (guard : d5843 p = 1) : d3083 p ≤ (2 : Int) + d7926 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3083, d7926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33400 p hg
    simpa only [d3083, d7926, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3083, d7926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33625 p hg
    simpa only [d3083, d7926, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33627 (p : Pattern) (guard : d5843 p = 1) : d3084 p ≤ (2 : Int) + d7927 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3084, d7927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33625 p hg
    simpa only [d3084, d7927, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3084, d7927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33421 p hg
    simpa only [d3084, d7927, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33628 (p : Pattern) (guard : d5843 p = 1) : d3085 p ≤ (2 : Int) + d7928 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3085, d7928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33626 p hg
    simpa only [d3085, d7928, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3085, d7928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33627 p hg
    simpa only [d3085, d7928, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33629 (p : Pattern) (guard : d5843 p = 1) : d3086 p ≤ (2 : Int) + d7929 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3086, d7929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33383 p hg
    simpa only [d3086, d7929, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3086, d7929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33330 p hg
    simpa only [d3086, d7929, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33630 (p : Pattern) (guard : d5843 p = 1) : d3087 p ≤ (2 : Int) + d7930 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3087, d7930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33424 p hg
    simpa only [d3087, d7930, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3087, d7930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33629 p hg
    simpa only [d3087, d7930, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33631 (p : Pattern) (guard : d5843 p = 1) : d3088 p ≤ (2 : Int) + d7931 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3088, d7931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33383 p hg
    simpa only [d3088, d7931, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3088, d7931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33338 p hg
    simpa only [d3088, d7931, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33632 (p : Pattern) (guard : d5843 p = 1) : d3089 p ≤ (2 : Int) + d7932 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3089, d7932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33425 p hg
    simpa only [d3089, d7932, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3089, d7932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33260 p hg
    simpa only [d3089, d7932, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33633 (p : Pattern) (guard : d5843 p = 1) : d3090 p ≤ (2 : Int) + d7933 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3090, d7933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33631 p hg
    simpa only [d3090, d7933, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3090, d7933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33632 p hg
    simpa only [d3090, d7933, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33634 (p : Pattern) (guard : d5843 p = 1) : d3091 p ≤ (2 : Int) + d7934 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3091, d7934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33630 p hg
    simpa only [d3091, d7934, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3091, d7934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33633 p hg
    simpa only [d3091, d7934, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33635 (p : Pattern) (guard : d5843 p = 1) : d3092 p ≤ (2 : Int) + d7935 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3092, d7935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33384 p hg
    simpa only [d3092, d7935, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3092, d7935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33632 p hg
    simpa only [d3092, d7935, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33636 (p : Pattern) (guard : d5843 p = 1) : d3093 p ≤ (2 : Int) + d7936 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3093, d7936, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33635 p hg
    simpa only [d3093, d7936, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3093, d7936, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33391 p hg
    simpa only [d3093, d7936, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33637 (p : Pattern) (guard : d5843 p = 1) : d3094 p ≤ (2 : Int) + d7937 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3094, d7937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33634 p hg
    simpa only [d3094, d7937, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3094, d7937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33636 p hg
    simpa only [d3094, d7937, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33638 (p : Pattern) (guard : d5843 p = 1) : d3095 p ≤ (2 : Int) + d7938 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3095, d7938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33628 p hg
    simpa only [d3095, d7938, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3095, d7938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33637 p hg
    simpa only [d3095, d7938, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33639 (p : Pattern) (guard : d5843 p = 1) : d3096 p ≤ (2 : Int) + d7939 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3096, d7939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33314 p hg
    simpa only [d3096, d7939, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3096, d7939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33311 p hg
    simpa only [d3096, d7939, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33640 (p : Pattern) (guard : d5843 p = 1) : d3097 p ≤ (2 : Int) + d7940 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3097, d7940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33312 p hg
    simpa only [d3097, d7940, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3097, d7940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33639 p hg
    simpa only [d3097, d7940, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33641 (p : Pattern) (guard : d5843 p = 1) : d3098 p ≤ (2 : Int) + d7941 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3098, d7941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33309 p hg
    simpa only [d3098, d7941, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3098, d7941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33640 p hg
    simpa only [d3098, d7941, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33642 (p : Pattern) (guard : d5843 p = 1) : d2031 p ≤ (2 : Int) + d7942 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2031, d7942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33358 p hg
    simpa only [d2031, d7942, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2031, d7942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33260 p hg
    simpa only [d2031, d7942, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33643 (p : Pattern) (guard : d5843 p = 1) : d3099 p ≤ (2 : Int) + d7943 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3099, d7943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33641 p hg
    simpa only [d3099, d7943, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3099, d7943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33642 p hg
    simpa only [d3099, d7943, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33644 (p : Pattern) (guard : d5843 p = 1) : d3100 p ≤ (2 : Int) + d7944 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3100, d7944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33400 p hg
    simpa only [d3100, d7944, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3100, d7944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33643 p hg
    simpa only [d3100, d7944, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33645 (p : Pattern) (guard : d5843 p = 1) : d3101 p ≤ (2 : Int) + d7945 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3101, d7945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33624 p hg
    simpa only [d3101, d7945, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3101, d7945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33420 p hg
    simpa only [d3101, d7945, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33646 (p : Pattern) (guard : d5843 p = 1) : d3102 p ≤ (2 : Int) + d7946 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3102, d7946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33644 p hg
    simpa only [d3102, d7946, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3102, d7946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33645 p hg
    simpa only [d3102, d7946, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33647 (p : Pattern) (guard : d5843 p = 1) : d3103 p ≤ (2 : Int) + d7947 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3103, d7947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33624 p hg
    simpa only [d3103, d7947, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3103, d7947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33376 p hg
    simpa only [d3103, d7947, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33648 (p : Pattern) (guard : d5843 p = 1) : d3104 p ≤ (2 : Int) + d7948 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3104, d7948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33647 p hg
    simpa only [d3104, d7948, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3104, d7948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33380 p hg
    simpa only [d3104, d7948, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33649 (p : Pattern) (guard : d5843 p = 1) : d3105 p ≤ (2 : Int) + d7949 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3105, d7949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33646 p hg
    simpa only [d3105, d7949, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3105, d7949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33648 p hg
    simpa only [d3105, d7949, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33650 (p : Pattern) (guard : d5843 p = 1) : d3106 p ≤ (2 : Int) + d7950 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3106, d7950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33629 p hg
    simpa only [d3106, d7950, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3106, d7950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33347 p hg
    simpa only [d3106, d7950, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33651 (p : Pattern) (guard : d5843 p = 1) : d3107 p ≤ (2 : Int) + d7951 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3107, d7951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33632 p hg
    simpa only [d3107, d7951, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3107, d7951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33390 p hg
    simpa only [d3107, d7951, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33652 (p : Pattern) (guard : d5843 p = 1) : d3108 p ≤ (2 : Int) + d7952 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3108, d7952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33650 p hg
    simpa only [d3108, d7952, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3108, d7952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33651 p hg
    simpa only [d3108, d7952, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33653 (p : Pattern) (guard : d5843 p = 1) : d3109 p ≤ (2 : Int) + d7953 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3109, d7953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33632 p hg
    simpa only [d3109, d7953, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3109, d7953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33260 p hg
    simpa only [d3109, d7953, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33654 (p : Pattern) (guard : d5843 p = 1) : d3110 p ≤ (2 : Int) + d7954 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3110, d7954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33653 p hg
    simpa only [d3110, d7954, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3110, d7954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33260 p hg
    simpa only [d3110, d7954, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33655 (p : Pattern) (guard : d5843 p = 1) : d3111 p ≤ (2 : Int) + d7955 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3111, d7955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33652 p hg
    simpa only [d3111, d7955, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3111, d7955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33654 p hg
    simpa only [d3111, d7955, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33656 (p : Pattern) (guard : d5843 p = 1) : d3112 p ≤ (2 : Int) + d7956 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3112, d7956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33649 p hg
    simpa only [d3112, d7956, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3112, d7956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33655 p hg
    simpa only [d3112, d7956, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33657 (p : Pattern) (guard : d5843 p = 1) : d3113 p ≤ (2 : Int) + d7957 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3113, d7957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33638 p hg
    simpa only [d3113, d7957, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3113, d7957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33656 p hg
    simpa only [d3113, d7957, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33658 (p : Pattern) (guard : d5843 p = 1) : d3114 p ≤ (2 : Int) + d7958 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3114, d7958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33246 p hg
    simpa only [d3114, d7958, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3114, d7958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33409 p hg
    simpa only [d3114, d7958, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33659 (p : Pattern) (guard : d5843 p = 1) : d2049 p ≤ (2 : Int) + d7959 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2049, d7959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33397 p hg
    simpa only [d2049, d7959, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2049, d7959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33260 p hg
    simpa only [d2049, d7959, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33660 (p : Pattern) (guard : d5843 p = 1) : d3115 p ≤ (2 : Int) + d7960 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3115, d7960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33658 p hg
    simpa only [d3115, d7960, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3115, d7960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33659 p hg
    simpa only [d3115, d7960, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33661 (p : Pattern) (guard : d5843 p = 1) : d2055 p ≤ (2 : Int) + d7961 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2055, d7961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33404 p hg
    simpa only [d2055, d7961, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2055, d7961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33260 p hg
    simpa only [d2055, d7961, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33662 (p : Pattern) (guard : d5843 p = 1) : d3116 p ≤ (2 : Int) + d7962 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3116, d7962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33307 p hg
    simpa only [d3116, d7962, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3116, d7962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33661 p hg
    simpa only [d3116, d7962, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33663 (p : Pattern) (guard : d5843 p = 1) : d3117 p ≤ (2 : Int) + d7963 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3117, d7963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33660 p hg
    simpa only [d3117, d7963, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3117, d7963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33662 p hg
    simpa only [d3117, d7963, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33664 (p : Pattern) (guard : d5843 p = 1) : d3118 p ≤ (2 : Int) + d7964 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3118, d7964, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33663 p hg
    simpa only [d3118, d7964, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3118, d7964, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33427 p hg
    simpa only [d3118, d7964, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33665 (p : Pattern) (guard : d5843 p = 1) : d3119 p ≤ (2 : Int) + d7965 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3119, d7965, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33664 p hg
    simpa only [d3119, d7965, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3119, d7965, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33428 p hg
    simpa only [d3119, d7965, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33666 (p : Pattern) (guard : d5843 p = 1) : d8 p ≤ (2 : Int) + d8 p := by
  omega
theorem compare33667 (p : Pattern) (guard : d5843 p = 1) : d191 p ≤ (2 : Int) + d3461 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d191, d3461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33666 p hg
    simpa only [d191, d3461, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d191, d3461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33267 p hg
    simpa only [d191, d3461, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33668 (p : Pattern) (guard : d5843 p = 1) : d315 p ≤ (2 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33267 p hg
    simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33260 p hg
    simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33669 (p : Pattern) (guard : d5843 p = 1) : d2060 p ≤ (2 : Int) + d7707 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2060, d7707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33667 p hg
    simpa only [d2060, d7707, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2060, d7707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33668 p hg
    simpa only [d2060, d7707, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33670 (p : Pattern) (guard : d5843 p = 1) : d2061 p ≤ (2 : Int) + d7966 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2061, d7966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33669 p hg
    simpa only [d2061, d7966, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2061, d7966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33668 p hg
    simpa only [d2061, d7966, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33671 (p : Pattern) (guard : d5843 p = 1) : d3120 p ≤ (2 : Int) + d7967 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3120, d7967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33667 p hg
    simpa only [d3120, d7967, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3120, d7967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33670 p hg
    simpa only [d3120, d7967, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33672 (p : Pattern) (guard : d5843 p = 1) : d2062 p ≤ (2 : Int) + d7968 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2062, d7968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33670 p hg
    simpa only [d2062, d7968, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2062, d7968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33260 p hg
    simpa only [d2062, d7968, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33673 (p : Pattern) (guard : d5843 p = 1) : d3121 p ≤ (2 : Int) + d7969 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3121, d7969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33671 p hg
    simpa only [d3121, d7969, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3121, d7969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33672 p hg
    simpa only [d3121, d7969, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33674 (p : Pattern) (guard : d5843 p = 1) : d3122 p ≤ (2 : Int) + d7970 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3122, d7970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33416 p hg
    simpa only [d3122, d7970, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3122, d7970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33673 p hg
    simpa only [d3122, d7970, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33675 (p : Pattern) (guard : d5843 p = 1) : d3123 p ≤ (2 : Int) + d7971 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3123, d7971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33674 p hg
    simpa only [d3123, d7971, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3123, d7971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33260 p hg
    simpa only [d3123, d7971, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33676 (p : Pattern) (guard : d5843 p = 1) : d3124 p ≤ (2 : Int) + d7972 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3124, d7972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33675 p hg
    simpa only [d3124, d7972, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3124, d7972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33260 p hg
    simpa only [d3124, d7972, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33677 (p : Pattern) (guard : d5843 p = 1) : d3125 p ≤ (2 : Int) + d7973 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3125, d7973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33665 p hg
    simpa only [d3125, d7973, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3125, d7973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33676 p hg
    simpa only [d3125, d7973, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33678 (p : Pattern) (guard : d5843 p = 1) : d2068 p ≤ (2 : Int) + d10 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d2068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4721 p hg
    simpa only [d5843, d2068, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d2068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33324 p hg
    simpa only [d5843, d2068, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33679 (p : Pattern) (guard : d5843 p = 1) : d2069 p ≤ (2 : Int) + d3279 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2069, d3279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33678 p hg
    simpa only [d2069, d3279, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2069, d3279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33326 p hg
    simpa only [d2069, d3279, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33680 (p : Pattern) (guard : d5843 p = 1) : d2070 p ≤ (2 : Int) + d7974 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2070, d7974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33314 p hg
    simpa only [d2070, d7974, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2070, d7974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33679 p hg
    simpa only [d2070, d7974, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33681 (p : Pattern) (guard : d5843 p = 1) : d2071 p ≤ (2 : Int) + d7975 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2071, d7975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33312 p hg
    simpa only [d2071, d7975, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2071, d7975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33680 p hg
    simpa only [d2071, d7975, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33682 (p : Pattern) (guard : d5843 p = 1) : d2072 p ≤ (2 : Int) + d7976 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2072, d7976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33681 p hg
    simpa only [d2072, d7976, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2072, d7976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33260 p hg
    simpa only [d2072, d7976, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33683 (p : Pattern) (guard : d5843 p = 1) : d3126 p ≤ (2 : Int) + d7977 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3126, d7977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33383 p hg
    simpa only [d3126, d7977, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3126, d7977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33682 p hg
    simpa only [d3126, d7977, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33684 (p : Pattern) (guard : d5843 p = 1) : d3127 p ≤ (2 : Int) + d7978 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3127, d7978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33683 p hg
    simpa only [d3127, d7978, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3127, d7978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33424 p hg
    simpa only [d3127, d7978, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33685 (p : Pattern) (guard : d5843 p = 1) : d3128 p ≤ (2 : Int) + d7979 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3128, d7979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33416 p hg
    simpa only [d3128, d7979, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3128, d7979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33379 p hg
    simpa only [d3128, d7979, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33686 (p : Pattern) (guard : d5843 p = 1) : d3129 p ≤ (2 : Int) + d7980 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3129, d7980, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33684 p hg
    simpa only [d3129, d7980, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3129, d7980, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33685 p hg
    simpa only [d3129, d7980, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33687 (p : Pattern) (guard : d5843 p = 1) : d3130 p ≤ (2 : Int) + d7981 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3130, d7981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33686 p hg
    simpa only [d3130, d7981, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3130, d7981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33438 p hg
    simpa only [d3130, d7981, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33688 (p : Pattern) (guard : d5843 p = 1) : d3131 p ≤ (2 : Int) + d7982 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3131, d7982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33673 p hg
    simpa only [d3131, d7982, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3131, d7982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33260 p hg
    simpa only [d3131, d7982, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33689 (p : Pattern) (guard : d5843 p = 1) : d3132 p ≤ (2 : Int) + d7983 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3132, d7983, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33688 p hg
    simpa only [d3132, d7983, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3132, d7983, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33260 p hg
    simpa only [d3132, d7983, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33690 (p : Pattern) (guard : d5843 p = 1) : d3133 p ≤ (2 : Int) + d7984 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3133, d7984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33689 p hg
    simpa only [d3133, d7984, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3133, d7984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33260 p hg
    simpa only [d3133, d7984, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33691 (p : Pattern) (guard : d5843 p = 1) : d3134 p ≤ (2 : Int) + d7985 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3134, d7985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33687 p hg
    simpa only [d3134, d7985, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3134, d7985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33690 p hg
    simpa only [d3134, d7985, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33692 (p : Pattern) (guard : d5843 p = 1) : d3135 p ≤ (2 : Int) + d7986 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3135, d7986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33677 p hg
    simpa only [d3135, d7986, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3135, d7986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33691 p hg
    simpa only [d3135, d7986, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33693 (p : Pattern) (guard : d5843 p = 1) : d3136 p ≤ (2 : Int) + d7987 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3136, d7987, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33657 p hg
    simpa only [d3136, d7987, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3136, d7987, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33692 p hg
    simpa only [d3136, d7987, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33694 (p : Pattern) (guard : d5843 p = 1) : d3137 p ≤ (2 : Int) + d7988 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3137, d7988, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33692 p hg
    simpa only [d3137, d7988, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3137, d7988, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33260 p hg
    simpa only [d3137, d7988, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33695 (p : Pattern) (guard : d5843 p = 1) : d3138 p ≤ (2 : Int) + d7989 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3138, d7989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33693 p hg
    simpa only [d3138, d7989, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3138, d7989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33694 p hg
    simpa only [d3138, d7989, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33696 (p : Pattern) (guard : d5843 p = 1) : d3139 p ≤ (2 : Int) + d7990 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3139, d7990, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33452 p hg
    simpa only [d3139, d7990, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3139, d7990, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33695 p hg
    simpa only [d3139, d7990, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33697 (p : Pattern) (guard : d5843 p = 1) : d3140 p ≤ (2 : Int) + d7991 p := by
  cases selected : p 71 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3140, d7991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33455 p hg
    simpa only [d3140, d7991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3140, d7991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33696 p hg
    simpa only [d3140, d7991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33698 (p : Pattern) (guard : d5843 p = 1) : d3141 p ≤ (2 : Int) + d7992 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3141, d7992, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33489 p hg
    simpa only [d3141, d7992, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3141, d7992, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33260 p hg
    simpa only [d3141, d7992, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33699 (p : Pattern) (guard : d5843 p = 1) : d3142 p ≤ (2 : Int) + d7993 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3142, d7993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33549 p hg
    simpa only [d3142, d7993, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3142, d7993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33698 p hg
    simpa only [d3142, d7993, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33700 (p : Pattern) (guard : d5843 p = 1) : d3143 p ≤ (2 : Int) + d7994 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3143, d7994, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33698 p hg
    simpa only [d3143, d7994, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3143, d7994, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33260 p hg
    simpa only [d3143, d7994, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33701 (p : Pattern) (guard : d5843 p = 1) : d3144 p ≤ (2 : Int) + d7995 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3144, d7995, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33699 p hg
    simpa only [d3144, d7995, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3144, d7995, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33700 p hg
    simpa only [d3144, d7995, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33702 (p : Pattern) (guard : d5843 p = 1) : d3145 p ≤ (2 : Int) + d7996 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3145, d7996, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33533 p hg
    simpa only [d3145, d7996, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3145, d7996, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33260 p hg
    simpa only [d3145, d7996, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33703 (p : Pattern) (guard : d5843 p = 1) : d3146 p ≤ (2 : Int) + d7997 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3146, d7997, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33557 p hg
    simpa only [d3146, d7997, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3146, d7997, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33702 p hg
    simpa only [d3146, d7997, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33704 (p : Pattern) (guard : d5843 p = 1) : d3147 p ≤ (2 : Int) + d7998 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3147, d7998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33702 p hg
    simpa only [d3147, d7998, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3147, d7998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33260 p hg
    simpa only [d3147, d7998, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33705 (p : Pattern) (guard : d5843 p = 1) : d3148 p ≤ (2 : Int) + d7999 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3148, d7999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33703 p hg
    simpa only [d3148, d7999, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3148, d7999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33704 p hg
    simpa only [d3148, d7999, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33706 (p : Pattern) (guard : d5843 p = 1) : d3149 p ≤ (2 : Int) + d8000 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3149, d8000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33701 p hg
    simpa only [d3149, d8000, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3149, d8000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33705 p hg
    simpa only [d3149, d8000, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33707 (p : Pattern) (guard : d5843 p = 1) : d3150 p ≤ (2 : Int) + d8001 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3150, d8001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33539 p hg
    simpa only [d3150, d8001, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3150, d8001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33706 p hg
    simpa only [d3150, d8001, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33708 (p : Pattern) (guard : d5843 p = 1) : d3151 p ≤ (2 : Int) + d8002 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3151, d8002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33585 p hg
    simpa only [d3151, d8002, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3151, d8002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33260 p hg
    simpa only [d3151, d8002, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33709 (p : Pattern) (guard : d5843 p = 1) : d3152 p ≤ (2 : Int) + d8003 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3152, d8003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33597 p hg
    simpa only [d3152, d8003, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3152, d8003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33708 p hg
    simpa only [d3152, d8003, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33710 (p : Pattern) (guard : d5843 p = 1) : d3153 p ≤ (2 : Int) + d8004 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3153, d8004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33708 p hg
    simpa only [d3153, d8004, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3153, d8004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33260 p hg
    simpa only [d3153, d8004, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33711 (p : Pattern) (guard : d5843 p = 1) : d3154 p ≤ (2 : Int) + d8005 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3154, d8005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33709 p hg
    simpa only [d3154, d8005, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3154, d8005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33710 p hg
    simpa only [d3154, d8005, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33712 (p : Pattern) (guard : d5843 p = 1) : d3155 p ≤ (2 : Int) + d8006 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3155, d8006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33711 p hg
    simpa only [d3155, d8006, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3155, d8006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33605 p hg
    simpa only [d3155, d8006, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33713 (p : Pattern) (guard : d5843 p = 1) : d3156 p ≤ (2 : Int) + d8007 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3156, d8007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33596 p hg
    simpa only [d3156, d8007, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3156, d8007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33712 p hg
    simpa only [d3156, d8007, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33714 (p : Pattern) (guard : d5843 p = 1) : d3157 p ≤ (2 : Int) + d8008 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3157, d8008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33707 p hg
    simpa only [d3157, d8008, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3157, d8008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33713 p hg
    simpa only [d3157, d8008, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33715 (p : Pattern) (guard : d5843 p = 1) : d3158 p ≤ (2 : Int) + d8009 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3158, d8009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33713 p hg
    simpa only [d3158, d8009, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3158, d8009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33612 p hg
    simpa only [d3158, d8009, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33716 (p : Pattern) (guard : d5843 p = 1) : d3159 p ≤ (2 : Int) + d8010 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3159, d8010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33714 p hg
    simpa only [d3159, d8010, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3159, d8010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33715 p hg
    simpa only [d3159, d8010, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33717 (p : Pattern) (guard : d5843 p = 1) : d3160 p ≤ (2 : Int) + d8011 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3160, d8011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33458 p hg
    simpa only [d3160, d8011, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3160, d8011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33578 p hg
    simpa only [d3160, d8011, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33718 (p : Pattern) (guard : d5843 p = 1) : d2109 p ≤ (2 : Int) + d8012 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2109, d8012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33566 p hg
    simpa only [d2109, d8012, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2109, d8012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33260 p hg
    simpa only [d2109, d8012, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33719 (p : Pattern) (guard : d5843 p = 1) : d3161 p ≤ (2 : Int) + d8013 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3161, d8013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33717 p hg
    simpa only [d3161, d8013, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3161, d8013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33718 p hg
    simpa only [d3161, d8013, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33720 (p : Pattern) (guard : d5843 p = 1) : d3162 p ≤ (2 : Int) + d8014 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3162, d8014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33719 p hg
    simpa only [d3162, d8014, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3162, d8014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33585 p hg
    simpa only [d3162, d8014, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33721 (p : Pattern) (guard : d5843 p = 1) : d3163 p ≤ (2 : Int) + d8015 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3163, d8015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33569 p hg
    simpa only [d3163, d8015, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3163, d8015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33720 p hg
    simpa only [d3163, d8015, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33722 (p : Pattern) (guard : d5843 p = 1) : d3164 p ≤ (2 : Int) + d8016 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3164, d8016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33580 p hg
    simpa only [d3164, d8016, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3164, d8016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33585 p hg
    simpa only [d3164, d8016, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33723 (p : Pattern) (guard : d5843 p = 1) : d3165 p ≤ (2 : Int) + d8017 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3165, d8017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33722 p hg
    simpa only [d3165, d8017, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3165, d8017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33492 p hg
    simpa only [d3165, d8017, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33724 (p : Pattern) (guard : d5843 p = 1) : d3166 p ≤ (2 : Int) + d8018 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3166, d8018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33721 p hg
    simpa only [d3166, d8018, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3166, d8018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33723 p hg
    simpa only [d3166, d8018, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33725 (p : Pattern) (guard : d5843 p = 1) : d3167 p ≤ (2 : Int) + d8019 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3167, d8019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33555 p hg
    simpa only [d3167, d8019, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3167, d8019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33522 p hg
    simpa only [d3167, d8019, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33726 (p : Pattern) (guard : d5843 p = 1) : d3168 p ≤ (2 : Int) + d8020 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3168, d8020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33590 p hg
    simpa only [d3168, d8020, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3168, d8020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33725 p hg
    simpa only [d3168, d8020, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33727 (p : Pattern) (guard : d5843 p = 1) : d3169 p ≤ (2 : Int) + d8021 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3169, d8021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33726 p hg
    simpa only [d3169, d8021, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3169, d8021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33702 p hg
    simpa only [d3169, d8021, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33728 (p : Pattern) (guard : d5843 p = 1) : d3170 p ≤ (2 : Int) + d8022 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3170, d8022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33591 p hg
    simpa only [d3170, d8022, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3170, d8022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33260 p hg
    simpa only [d3170, d8022, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33729 (p : Pattern) (guard : d5843 p = 1) : d3171 p ≤ (2 : Int) + d8023 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3171, d8023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33728 p hg
    simpa only [d3171, d8023, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3171, d8023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33260 p hg
    simpa only [d3171, d8023, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33730 (p : Pattern) (guard : d5843 p = 1) : d3172 p ≤ (2 : Int) + d8024 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3172, d8024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33729 p hg
    simpa only [d3172, d8024, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3172, d8024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33260 p hg
    simpa only [d3172, d8024, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33731 (p : Pattern) (guard : d5843 p = 1) : d3173 p ≤ (2 : Int) + d8025 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3173, d8025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33727 p hg
    simpa only [d3173, d8025, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3173, d8025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33730 p hg
    simpa only [d3173, d8025, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33732 (p : Pattern) (guard : d5843 p = 1) : d3174 p ≤ (2 : Int) + d8026 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3174, d8026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33724 p hg
    simpa only [d3174, d8026, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3174, d8026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33731 p hg
    simpa only [d3174, d8026, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33733 (p : Pattern) (guard : d5843 p = 1) : d3175 p ≤ (2 : Int) + d8027 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3175, d8027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33508 p hg
    simpa only [d3175, d8027, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3175, d8027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33505 p hg
    simpa only [d3175, d8027, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33734 (p : Pattern) (guard : d5843 p = 1) : d3176 p ≤ (2 : Int) + d8028 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3176, d8028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33506 p hg
    simpa only [d3176, d8028, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3176, d8028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33733 p hg
    simpa only [d3176, d8028, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33735 (p : Pattern) (guard : d5843 p = 1) : d3177 p ≤ (2 : Int) + d8029 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3177, d8029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33503 p hg
    simpa only [d3177, d8029, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3177, d8029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33734 p hg
    simpa only [d3177, d8029, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33736 (p : Pattern) (guard : d5843 p = 1) : d2126 p ≤ (2 : Int) + d8030 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2126, d8030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33541 p hg
    simpa only [d2126, d8030, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2126, d8030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33260 p hg
    simpa only [d2126, d8030, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33737 (p : Pattern) (guard : d5843 p = 1) : d3178 p ≤ (2 : Int) + d8031 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3178, d8031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33735 p hg
    simpa only [d3178, d8031, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3178, d8031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33736 p hg
    simpa only [d3178, d8031, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33738 (p : Pattern) (guard : d5843 p = 1) : d3179 p ≤ (2 : Int) + d8032 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3179, d8032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33719 p hg
    simpa only [d3179, d8032, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3179, d8032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33737 p hg
    simpa only [d3179, d8032, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33739 (p : Pattern) (guard : d5843 p = 1) : d2135 p ≤ (2 : Int) + d7681 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2135, d7681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33478 p hg
    simpa only [d2135, d7681, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2135, d7681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33527 p hg
    simpa only [d2135, d7681, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
