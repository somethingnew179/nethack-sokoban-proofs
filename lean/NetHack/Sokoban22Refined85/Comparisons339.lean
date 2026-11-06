/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons338
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare47460 (p : Pattern) (guard : d8106 p = 1) : d2896 p ≤ (0 : Int) + d352 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2896, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47459 p hg
    simpa only [d8106, d2896, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2896, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39688 p hg
    simpa only [d8106, d2896, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47461 (p : Pattern) (guard : d8105 p = 1) : d2922 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d2922, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35657 p hg
    simpa only [d8105, d2922, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d2922, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23912 p hg
    simpa only [d8105, d2922, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47462 (p : Pattern) (guard : d8111 p = 1) : d2923 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2923, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47461 p hg
    simpa only [d8111, d2923, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2923, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15302 p hg
    simpa only [d8111, d2923, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47463 (p : Pattern) (guard : d8112 p = 1) : d2924 p ≤ (0 : Int) + d355 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2924, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47460 p hg
    simpa only [d8112, d2924, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2924, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47462 p hg
    simpa only [d8112, d2924, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47464 (p : Pattern) (guard : d8105 p = 1) : d2897 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d2897, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35664 p hg
    simpa only [d8105, d2897, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d2897, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23880 p hg
    simpa only [d8105, d2897, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47465 (p : Pattern) (guard : d8111 p = 1) : d2898 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2898, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47464 p hg
    simpa only [d8111, d2898, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2898, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15269 p hg
    simpa only [d8111, d2898, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47466 (p : Pattern) (guard : d0 p = 1) : d2902 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare47467 (p : Pattern) (guard : d8117 p = 1) : d2925 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2925, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47465 p hg
    simpa only [d8117, d2925, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2925, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47466 p hg
    simpa only [d8117, d2925, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47468 (p : Pattern) (guard : d8118 p = 1) : d2926 p ≤ (0 : Int) + d362 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2926, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47463 p hg
    simpa only [d8118, d2926, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2926, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47467 p hg
    simpa only [d8118, d2926, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47469 (p : Pattern) (guard : d8117 p = 1) : d2929 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2929, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47436 p hg
    simpa only [d8117, d2929, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2929, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46738 p hg
    simpa only [d8117, d2929, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47470 (p : Pattern) (guard : d8123 p = 1) : d2933 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d2933, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47469 p hg
    simpa only [d8123, d2933, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d2933, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46740 p hg
    simpa only [d8123, d2933, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47471 (p : Pattern) (guard : d8124 p = 1) : d2934 p ≤ (0 : Int) + d395 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d2934, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47468 p hg
    simpa only [d8124, d2934, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d2934, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47470 p hg
    simpa only [d8124, d2934, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47472 (p : Pattern) (guard : d8111 p = 1) : d2908 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2908, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47332 p hg
    simpa only [d8111, d2908, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2908, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15283 p hg
    simpa only [d8111, d2908, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47473 (p : Pattern) (guard : d0 p = 1) : d2936 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare47474 (p : Pattern) (guard : d8117 p = 1) : d2937 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2937, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47472 p hg
    simpa only [d8117, d2937, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2937, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47473 p hg
    simpa only [d8117, d2937, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47475 (p : Pattern) (guard : d0 p = 1) : d2938 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare47476 (p : Pattern) (guard : d8123 p = 1) : d2939 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d2939, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47474 p hg
    simpa only [d8123, d2939, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d2939, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47475 p hg
    simpa only [d8123, d2939, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47477 (p : Pattern) (guard : d0 p = 1) : d2944 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare47478 (p : Pattern) (guard : d8129 p = 1) : d2945 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d2945, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47476 p hg
    simpa only [d8129, d2945, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d2945, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47477 p hg
    simpa only [d8129, d2945, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47479 (p : Pattern) (guard : d8130 p = 1) : d2946 p ≤ (0 : Int) + d397 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d2946, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47471 p hg
    simpa only [d8130, d2946, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d2946, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47478 p hg
    simpa only [d8130, d2946, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47480 (p : Pattern) (guard : d8131 p = 1) : d2947 p ≤ (0 : Int) + d419 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d2947, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47458 p hg
    simpa only [d8131, d2947, d419, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d2947, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47479 p hg
    simpa only [d8131, d2947, d419, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47481 (p : Pattern) (guard : d8105 p = 1) : d2950 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d2950, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35551 p hg
    simpa only [d8105, d2950, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d2950, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23945 p hg
    simpa only [d8105, d2950, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47482 (p : Pattern) (guard : d8111 p = 1) : d2951 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2951, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47481 p hg
    simpa only [d8111, d2951, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2951, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15328 p hg
    simpa only [d8111, d2951, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47483 (p : Pattern) (guard : d8112 p = 1) : d2952 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2952, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47262 p hg
    simpa only [d8112, d2952, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2952, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47482 p hg
    simpa only [d8112, d2952, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47484 (p : Pattern) (guard : d8111 p = 1) : d2953 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47306 p hg
    simpa only [d8111, d2953, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15331 p hg
    simpa only [d8111, d2953, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47485 (p : Pattern) (guard : d0 p = 1) : d2954 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare47486 (p : Pattern) (guard : d8117 p = 1) : d2955 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47484 p hg
    simpa only [d8117, d2955, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47485 p hg
    simpa only [d8117, d2955, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47487 (p : Pattern) (guard : d8118 p = 1) : d2956 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2956, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47483 p hg
    simpa only [d8118, d2956, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2956, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47486 p hg
    simpa only [d8118, d2956, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47488 (p : Pattern) (guard : d0 p = 1) : d2958 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare47489 (p : Pattern) (guard : d8123 p = 1) : d2959 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d2959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47486 p hg
    simpa only [d8123, d2959, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d2959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47488 p hg
    simpa only [d8123, d2959, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47490 (p : Pattern) (guard : d8124 p = 1) : d2960 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d2960, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47487 p hg
    simpa only [d8124, d2960, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d2960, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47489 p hg
    simpa only [d8124, d2960, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47491 (p : Pattern) (guard : d8129 p = 1) : d2966 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d2966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47312 p hg
    simpa only [d8129, d2966, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d2966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8129, d2966, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47492 (p : Pattern) (guard : d8130 p = 1) : d2967 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d2967, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47490 p hg
    simpa only [d8130, d2967, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d2967, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47491 p hg
    simpa only [d8130, d2967, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47493 (p : Pattern) (guard : d8105 p = 1) : d2950 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d2950, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35684 p hg
    simpa only [d8105, d2950, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d2950, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23945 p hg
    simpa only [d8105, d2950, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47494 (p : Pattern) (guard : d8111 p = 1) : d2951 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2951, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47493 p hg
    simpa only [d8111, d2951, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2951, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15328 p hg
    simpa only [d8111, d2951, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47495 (p : Pattern) (guard : d8117 p = 1) : d2968 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2968, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47494 p hg
    simpa only [d8117, d2968, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2968, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47320 p hg
    simpa only [d8117, d2968, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47496 (p : Pattern) (guard : d0 p = 1) : d2969 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare47497 (p : Pattern) (guard : d8123 p = 1) : d2970 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d2970, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47495 p hg
    simpa only [d8123, d2970, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d2970, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47496 p hg
    simpa only [d8123, d2970, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47498 (p : Pattern) (guard : d0 p = 1) : d2972 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare47499 (p : Pattern) (guard : d8129 p = 1) : d2973 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d2973, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47497 p hg
    simpa only [d8129, d2973, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d2973, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47498 p hg
    simpa only [d8129, d2973, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47500 (p : Pattern) (guard : d0 p = 1) : d2976 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare47501 (p : Pattern) (guard : d8135 p = 1) : d2977 p ≤ (0 : Int) + d421 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d2977, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47499 p hg
    simpa only [d8135, d2977, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d2977, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47500 p hg
    simpa only [d8135, d2977, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47502 (p : Pattern) (guard : d8136 p = 1) : d2978 p ≤ (0 : Int) + d422 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d2978, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47492 p hg
    simpa only [d8136, d2978, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d2978, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47501 p hg
    simpa only [d8136, d2978, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47503 (p : Pattern) (guard : d8137 p = 1) : d2979 p ≤ (0 : Int) + d423 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d2979, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47480 p hg
    simpa only [d8137, d2979, d423, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d2979, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47502 p hg
    simpa only [d8137, d2979, d423, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47504 (p : Pattern) (guard : d8112 p = 1) : d2952 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2952, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47259 p hg
    simpa only [d8112, d2952, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2952, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47494 p hg
    simpa only [d8112, d2952, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47505 (p : Pattern) (guard : d8111 p = 1) : d2953 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2953, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47332 p hg
    simpa only [d8111, d2953, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2953, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15331 p hg
    simpa only [d8111, d2953, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47506 (p : Pattern) (guard : d8117 p = 1) : d2955 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2955, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47505 p hg
    simpa only [d8117, d2955, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2955, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47485 p hg
    simpa only [d8117, d2955, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47507 (p : Pattern) (guard : d8118 p = 1) : d2956 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2956, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47504 p hg
    simpa only [d8118, d2956, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2956, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47506 p hg
    simpa only [d8118, d2956, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47508 (p : Pattern) (guard : d8124 p = 1) : d2960 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d2960, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47507 p hg
    simpa only [d8124, d2960, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d2960, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47489 p hg
    simpa only [d8124, d2960, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47509 (p : Pattern) (guard : d8130 p = 1) : d2967 p ≤ (0 : Int) + d399 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d2967, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47508 p hg
    simpa only [d8130, d2967, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d2967, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47491 p hg
    simpa only [d8130, d2967, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47510 (p : Pattern) (guard : d8105 p = 1) : d2950 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d2950, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39765 p hg
    simpa only [d8105, d2950, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d2950, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23945 p hg
    simpa only [d8105, d2950, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47511 (p : Pattern) (guard : d8111 p = 1) : d2951 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2951, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47510 p hg
    simpa only [d8111, d2951, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2951, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15328 p hg
    simpa only [d8111, d2951, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47512 (p : Pattern) (guard : d8117 p = 1) : d2968 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2968, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47511 p hg
    simpa only [d8117, d2968, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2968, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47320 p hg
    simpa only [d8117, d2968, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47513 (p : Pattern) (guard : d8123 p = 1) : d2970 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d2970, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47512 p hg
    simpa only [d8123, d2970, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d2970, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47496 p hg
    simpa only [d8123, d2970, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47514 (p : Pattern) (guard : d8129 p = 1) : d2973 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d2973, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47513 p hg
    simpa only [d8129, d2973, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d2973, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47498 p hg
    simpa only [d8129, d2973, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47515 (p : Pattern) (guard : d8135 p = 1) : d2977 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d2977, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47514 p hg
    simpa only [d8135, d2977, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d2977, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47500 p hg
    simpa only [d8135, d2977, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47516 (p : Pattern) (guard : d8136 p = 1) : d2978 p ≤ (0 : Int) + d424 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d2978, d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47509 p hg
    simpa only [d8136, d2978, d424, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d2978, d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47515 p hg
    simpa only [d8136, d2978, d424, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47517 (p : Pattern) (guard : d8142 p = 1) : d2990 p ≤ (0 : Int) + d425 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8136 p = 1 := by simpa only [d8142, d2990, d425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47516 p hg
    simpa only [d8142, d2990, d425, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8141 p = 1 := by simpa only [d8142, d2990, d425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37397 p hg
    simpa only [d8142, d2990, d425, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47518 (p : Pattern) (guard : d8143 p = 1) : d2991 p ≤ (0 : Int) + d426 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8137 p = 1 := by simpa only [d8143, d2991, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47503 p hg
    simpa only [d8143, d2991, d426, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8142 p = 1 := by simpa only [d8143, d2991, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47517 p hg
    simpa only [d8143, d2991, d426, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47519 (p : Pattern) (guard : d8144 p = 1) : d2992 p ≤ (0 : Int) + d427 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8138 p = 1 := by simpa only [d8144, d2992, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47429 p hg
    simpa only [d8144, d2992, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8143 p = 1 := by simpa only [d8144, d2992, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47518 p hg
    simpa only [d8144, d2992, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47520 (p : Pattern) (guard : d8089 p = 1) : d1941 p ≤ (0 : Int) + d357 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d1941, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35236 p hg
    simpa only [d8089, d1941, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d1941, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39234 p hg
    simpa only [d8089, d1941, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47521 (p : Pattern) (guard : d8094 p = 1) : d1942 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d1942, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47520 p hg
    simpa only [d8094, d1942, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d1942, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39236 p hg
    simpa only [d8094, d1942, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47522 (p : Pattern) (guard : d8095 p = 1) : d2993 p ≤ (0 : Int) + d432 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2993, d432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35697 p hg
    simpa only [d8095, d2993, d432, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2993, d432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47521 p hg
    simpa only [d8095, d2993, d432, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47523 (p : Pattern) (guard : d8101 p = 1) : d2994 p ≤ (0 : Int) + d433 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2994, d433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47522 p hg
    simpa only [d8101, d2994, d433, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2994, d433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39780 p hg
    simpa only [d8101, d2994, d433, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47524 (p : Pattern) (guard : d8100 p = 1) : d2993 p ≤ (0 : Int) + d342 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2993, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35703 p hg
    simpa only [d8100, d2993, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2993, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39364 p hg
    simpa only [d8100, d2993, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47525 (p : Pattern) (guard : d8106 p = 1) : d2994 p ≤ (0 : Int) + d344 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2994, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47524 p hg
    simpa only [d8106, d2994, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2994, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39785 p hg
    simpa only [d8106, d2994, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47526 (p : Pattern) (guard : d8107 p = 1) : d2994 p ≤ (0 : Int) + d434 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47523 p hg
    simpa only [d8107, d434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47525 p hg
    simpa only [d8107, d434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47527 (p : Pattern) (guard : d8100 p = 1) : d2993 p ≤ (0 : Int) + d351 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2993, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35710 p hg
    simpa only [d8100, d2993, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2993, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39364 p hg
    simpa only [d8100, d2993, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47528 (p : Pattern) (guard : d8106 p = 1) : d2994 p ≤ (0 : Int) + d352 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2994, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47527 p hg
    simpa only [d8106, d2994, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2994, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39321 p hg
    simpa only [d8106, d2994, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47529 (p : Pattern) (guard : d8105 p = 1) : d2995 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d2995, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35716 p hg
    simpa only [d8105, d2995, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d2995, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24029 p hg
    simpa only [d8105, d2995, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47530 (p : Pattern) (guard : d8111 p = 1) : d2996 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2996, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47529 p hg
    simpa only [d8111, d2996, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2996, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15424 p hg
    simpa only [d8111, d2996, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47531 (p : Pattern) (guard : d8112 p = 1) : d2997 p ≤ (0 : Int) + d355 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2997, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47528 p hg
    simpa only [d8112, d2997, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2997, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47530 p hg
    simpa only [d8112, d2997, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47532 (p : Pattern) (guard : d8113 p = 1) : d2998 p ≤ (0 : Int) + d435 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2998, d435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47526 p hg
    simpa only [d8113, d2998, d435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2998, d435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47531 p hg
    simpa only [d8113, d2998, d435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47533 (p : Pattern) (guard : d8105 p = 1) : d2995 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d2995, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35724 p hg
    simpa only [d8105, d2995, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d2995, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24029 p hg
    simpa only [d8105, d2995, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47534 (p : Pattern) (guard : d8111 p = 1) : d2996 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2996, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47533 p hg
    simpa only [d8111, d2996, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2996, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15424 p hg
    simpa only [d8111, d2996, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47535 (p : Pattern) (guard : d8112 p = 1) : d2997 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2997, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47085 p hg
    simpa only [d8112, d2997, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2997, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47534 p hg
    simpa only [d8112, d2997, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47536 (p : Pattern) (guard : d8117 p = 1) : d2999 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2999, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46960 p hg
    simpa only [d8117, d2999, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2999, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8117, d2999, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47537 (p : Pattern) (guard : d8118 p = 1) : d3000 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3000, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47535 p hg
    simpa only [d8118, d3000, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3000, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47536 p hg
    simpa only [d8118, d3000, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47538 (p : Pattern) (guard : d8119 p = 1) : d3001 p ≤ (0 : Int) + d436 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d3001, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47532 p hg
    simpa only [d8119, d3001, d436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d3001, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47537 p hg
    simpa only [d8119, d3001, d436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47539 (p : Pattern) (guard : d8100 p = 1) : d3002 p ≤ (0 : Int) + d324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3002, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35300 p hg
    simpa only [d8100, d3002, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3002, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39247 p hg
    simpa only [d8100, d3002, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47540 (p : Pattern) (guard : d8106 p = 1) : d3003 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3003, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47539 p hg
    simpa only [d8106, d3003, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3003, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39261 p hg
    simpa only [d8106, d3003, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47541 (p : Pattern) (guard : d8105 p = 1) : d3002 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d3002, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35735 p hg
    simpa only [d8105, d3002, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d3002, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24037 p hg
    simpa only [d8105, d3002, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47542 (p : Pattern) (guard : d8111 p = 1) : d3004 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3004, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47541 p hg
    simpa only [d8111, d3004, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3004, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15433 p hg
    simpa only [d8111, d3004, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47543 (p : Pattern) (guard : d8112 p = 1) : d3005 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3005, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47540 p hg
    simpa only [d8112, d3005, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3005, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47542 p hg
    simpa only [d8112, d3005, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47544 (p : Pattern) (guard : d8105 p = 1) : d3002 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d3002, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35368 p hg
    simpa only [d8105, d3002, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d3002, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24037 p hg
    simpa only [d8105, d3002, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47545 (p : Pattern) (guard : d8111 p = 1) : d3006 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3006, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47544 p hg
    simpa only [d8111, d3006, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3006, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8111, d3006, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47546 (p : Pattern) (guard : d8117 p = 1) : d3009 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3009, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47545 p hg
    simpa only [d8117, d3009, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3009, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47077 p hg
    simpa only [d8117, d3009, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47547 (p : Pattern) (guard : d8118 p = 1) : d3010 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3010, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47543 p hg
    simpa only [d8118, d3010, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3010, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47546 p hg
    simpa only [d8118, d3010, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47548 (p : Pattern) (guard : d8124 p = 1) : d3013 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d3013, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47547 p hg
    simpa only [d8124, d3013, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d3013, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47081 p hg
    simpa only [d8124, d3013, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47549 (p : Pattern) (guard : d8125 p = 1) : d3014 p ≤ (0 : Int) + d437 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d3014, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47538 p hg
    simpa only [d8125, d3014, d437, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d3014, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47548 p hg
    simpa only [d8125, d3014, d437, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47550 (p : Pattern) (guard : d8100 p = 1) : d2993 p ≤ (0 : Int) + d334 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2993, d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35747 p hg
    simpa only [d8100, d2993, d334, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2993, d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39882 p hg
    simpa only [d8100, d2993, d334, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47551 (p : Pattern) (guard : d8106 p = 1) : d2994 p ≤ (0 : Int) + d337 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2994, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47550 p hg
    simpa only [d8106, d2994, d337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2994, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39812 p hg
    simpa only [d8106, d2994, d337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47552 (p : Pattern) (guard : d8105 p = 1) : d3015 p ≤ (0 : Int) + d367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d3015, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35754 p hg
    simpa only [d8105, d3015, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d3015, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24055 p hg
    simpa only [d8105, d3015, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47553 (p : Pattern) (guard : d8111 p = 1) : d3016 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3016, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47552 p hg
    simpa only [d8111, d3016, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3016, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15448 p hg
    simpa only [d8111, d3016, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47554 (p : Pattern) (guard : d8112 p = 1) : d3017 p ≤ (0 : Int) + d415 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3017, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47551 p hg
    simpa only [d8112, d3017, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3017, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47553 p hg
    simpa only [d8112, d3017, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47555 (p : Pattern) (guard : d8105 p = 1) : d2995 p ≤ (0 : Int) + d324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d2995, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35761 p hg
    simpa only [d8105, d2995, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d2995, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24029 p hg
    simpa only [d8105, d2995, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47556 (p : Pattern) (guard : d8111 p = 1) : d2996 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2996, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47555 p hg
    simpa only [d8111, d2996, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2996, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15424 p hg
    simpa only [d8111, d2996, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47557 (p : Pattern) (guard : d8117 p = 1) : d3141 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3141, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47556 p hg
    simpa only [d8117, d3141, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3141, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35764 p hg
    simpa only [d8117, d3141, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47558 (p : Pattern) (guard : d8118 p = 1) : d3142 p ≤ (0 : Int) + d416 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3142, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47554 p hg
    simpa only [d8118, d3142, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3142, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47557 p hg
    simpa only [d8118, d3142, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47559 (p : Pattern) (guard : d8117 p = 1) : d3141 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3141, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47530 p hg
    simpa only [d8117, d3141, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3141, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35767 p hg
    simpa only [d8117, d3141, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47560 (p : Pattern) (guard : d8123 p = 1) : d3143 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d3143, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47559 p hg
    simpa only [d8123, d3143, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d3143, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d3143, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47561 (p : Pattern) (guard : d8124 p = 1) : d3144 p ≤ (0 : Int) + d417 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d3144, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47558 p hg
    simpa only [d8124, d3144, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d3144, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47560 p hg
    simpa only [d8124, d3144, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47562 (p : Pattern) (guard : d8105 p = 1) : d3002 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d3002, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35774 p hg
    simpa only [d8105, d3002, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d3002, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24037 p hg
    simpa only [d8105, d3002, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47563 (p : Pattern) (guard : d8111 p = 1) : d3004 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3004, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47562 p hg
    simpa only [d8111, d3004, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3004, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15433 p hg
    simpa only [d8111, d3004, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47564 (p : Pattern) (guard : d8117 p = 1) : d3025 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3025, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47563 p hg
    simpa only [d8117, d3025, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3025, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47096 p hg
    simpa only [d8117, d3025, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47565 (p : Pattern) (guard : d0 p = 1) : d3145 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare47566 (p : Pattern) (guard : d8123 p = 1) : d3146 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d3146, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47564 p hg
    simpa only [d8123, d3146, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d3146, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47565 p hg
    simpa only [d8123, d3146, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47567 (p : Pattern) (guard : d0 p = 1) : d3147 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare47568 (p : Pattern) (guard : d8129 p = 1) : d3148 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d3148, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47566 p hg
    simpa only [d8129, d3148, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d3148, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47567 p hg
    simpa only [d8129, d3148, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47569 (p : Pattern) (guard : d8130 p = 1) : d3149 p ≤ (0 : Int) + d418 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d3149, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47561 p hg
    simpa only [d8130, d3149, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d3149, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47568 p hg
    simpa only [d8130, d3149, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47570 (p : Pattern) (guard : d8131 p = 1) : d3150 p ≤ (0 : Int) + d438 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d3150, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47549 p hg
    simpa only [d8131, d3150, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d3150, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47569 p hg
    simpa only [d8131, d3150, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47571 (p : Pattern) (guard : d8100 p = 1) : d3033 p ≤ (0 : Int) + d367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3033, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35327 p hg
    simpa only [d8100, d3033, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3033, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47105 p hg
    simpa only [d8100, d3033, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47572 (p : Pattern) (guard : d8106 p = 1) : d3034 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3034, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47571 p hg
    simpa only [d8106, d3034, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3034, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39365 p hg
    simpa only [d8106, d3034, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47573 (p : Pattern) (guard : d8105 p = 1) : d3039 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d3039, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35774 p hg
    simpa only [d8105, d3039, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d3039, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24078 p hg
    simpa only [d8105, d3039, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47574 (p : Pattern) (guard : d8111 p = 1) : d3040 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3040, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47573 p hg
    simpa only [d8111, d3040, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3040, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15467 p hg
    simpa only [d8111, d3040, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47575 (p : Pattern) (guard : d8112 p = 1) : d3041 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3041, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47572 p hg
    simpa only [d8112, d3041, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3041, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47574 p hg
    simpa only [d8112, d3041, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47576 (p : Pattern) (guard : d8111 p = 1) : d3042 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3042, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47541 p hg
    simpa only [d8111, d3042, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3042, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15470 p hg
    simpa only [d8111, d3042, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47577 (p : Pattern) (guard : d8117 p = 1) : d3044 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3044, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47576 p hg
    simpa only [d8117, d3044, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3044, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47112 p hg
    simpa only [d8117, d3044, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47578 (p : Pattern) (guard : d8118 p = 1) : d3045 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3045, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47575 p hg
    simpa only [d8118, d3045, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3045, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47577 p hg
    simpa only [d8118, d3045, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47579 (p : Pattern) (guard : d8111 p = 1) : d3042 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3042, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47544 p hg
    simpa only [d8111, d3042, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3042, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15470 p hg
    simpa only [d8111, d3042, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47580 (p : Pattern) (guard : d8117 p = 1) : d3044 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3044, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47579 p hg
    simpa only [d8117, d3044, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3044, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47112 p hg
    simpa only [d8117, d3044, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47581 (p : Pattern) (guard : d8123 p = 1) : d3046 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d3046, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47580 p hg
    simpa only [d8123, d3046, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d3046, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47115 p hg
    simpa only [d8123, d3046, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47582 (p : Pattern) (guard : d8124 p = 1) : d3047 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d3047, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47578 p hg
    simpa only [d8124, d3047, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d3047, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47581 p hg
    simpa only [d8124, d3047, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47583 (p : Pattern) (guard : d8130 p = 1) : d3054 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d3054, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47582 p hg
    simpa only [d8130, d3054, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d3054, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47122 p hg
    simpa only [d8130, d3054, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47584 (p : Pattern) (guard : d8105 p = 1) : d3039 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d3039, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35795 p hg
    simpa only [d8105, d3039, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d3039, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24078 p hg
    simpa only [d8105, d3039, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47585 (p : Pattern) (guard : d8111 p = 1) : d3040 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3040, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47584 p hg
    simpa only [d8111, d3040, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3040, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15467 p hg
    simpa only [d8111, d3040, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47586 (p : Pattern) (guard : d0 p = 1) : d3048 p ≤ (0 : Int) + d373 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare47587 (p : Pattern) (guard : d8117 p = 1) : d3055 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3055, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47585 p hg
    simpa only [d8117, d3055, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3055, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47586 p hg
    simpa only [d8117, d3055, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47588 (p : Pattern) (guard : d0 p = 1) : d3151 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare47589 (p : Pattern) (guard : d8123 p = 1) : d3152 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d3152, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47587 p hg
    simpa only [d8123, d3152, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d3152, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47588 p hg
    simpa only [d8123, d3152, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47590 (p : Pattern) (guard : d0 p = 1) : d3153 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare47591 (p : Pattern) (guard : d8129 p = 1) : d3154 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d3154, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47589 p hg
    simpa only [d8129, d3154, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d3154, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47590 p hg
    simpa only [d8129, d3154, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47592 (p : Pattern) (guard : d8135 p = 1) : d3155 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d3155, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47591 p hg
    simpa only [d8135, d3155, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d3155, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47132 p hg
    simpa only [d8135, d3155, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47593 (p : Pattern) (guard : d8136 p = 1) : d3156 p ≤ (0 : Int) + d439 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d3156, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47583 p hg
    simpa only [d8136, d3156, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d3156, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47592 p hg
    simpa only [d8136, d3156, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47594 (p : Pattern) (guard : d8137 p = 1) : d3157 p ≤ (0 : Int) + d440 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d3157, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47570 p hg
    simpa only [d8137, d3157, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d3157, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47593 p hg
    simpa only [d8137, d3157, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47595 (p : Pattern) (guard : d8100 p = 1) : d3033 p ≤ (0 : Int) + d351 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3033, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35710 p hg
    simpa only [d8100, d3033, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3033, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47105 p hg
    simpa only [d8100, d3033, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47596 (p : Pattern) (guard : d8106 p = 1) : d3034 p ≤ (0 : Int) + d352 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3034, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47595 p hg
    simpa only [d8106, d3034, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3034, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39365 p hg
    simpa only [d8106, d3034, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47597 (p : Pattern) (guard : d8112 p = 1) : d3041 p ≤ (0 : Int) + d355 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3041, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47596 p hg
    simpa only [d8112, d3041, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3041, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47585 p hg
    simpa only [d8112, d3041, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47598 (p : Pattern) (guard : d8111 p = 1) : d3042 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3042, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47562 p hg
    simpa only [d8111, d3042, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3042, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15470 p hg
    simpa only [d8111, d3042, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47599 (p : Pattern) (guard : d8117 p = 1) : d3044 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3044, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47598 p hg
    simpa only [d8117, d3044, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3044, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47112 p hg
    simpa only [d8117, d3044, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
