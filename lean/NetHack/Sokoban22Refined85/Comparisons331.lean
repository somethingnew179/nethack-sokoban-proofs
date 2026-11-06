/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons330
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare46340 (p : Pattern) (guard : d8102 p = 1) : d2964 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d2964, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46337 p hg
    simpa only [d8102, d2964, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d2964, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46339 p hg
    simpa only [d8102, d2964, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46341 (p : Pattern) (guard : d8095 p = 1) : d2930 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34437 p hg
    simpa only [d8095, d2930, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38456 p hg
    simpa only [d8095, d2930, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46342 (p : Pattern) (guard : d8101 p = 1) : d2931 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46341 p hg
    simpa only [d8101, d2931, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38457 p hg
    simpa only [d8101, d2931, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46343 (p : Pattern) (guard : d8107 p = 1) : d2932 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46342 p hg
    simpa only [d8107, d2932, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34455 p hg
    simpa only [d8107, d2932, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46344 (p : Pattern) (guard : d8108 p = 1) : d2965 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d2965, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46340 p hg
    simpa only [d8108, d2965, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d2965, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46343 p hg
    simpa only [d8108, d2965, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46345 (p : Pattern) (guard : d8114 p = 1) : d2966 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d2966, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46344 p hg
    simpa only [d8114, d2966, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d2966, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34577 p hg
    simpa only [d8114, d2966, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46346 (p : Pattern) (guard : d8115 p = 1) : d2967 p ≤ (0 : Int) + d397 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8109 p = 1 := by simpa only [d8115, d2967, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46335 p hg
    simpa only [d8115, d2967, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8114 p = 1 := by simpa only [d8115, d2967, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46345 p hg
    simpa only [d8115, d2967, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46347 (p : Pattern) (guard : d8091 p = 1) : d2950 p ≤ (0 : Int) + d324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d2950, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34580 p hg
    simpa only [d8091, d2950, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d2950, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46322 p hg
    simpa only [d8091, d2950, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46348 (p : Pattern) (guard : d8096 p = 1) : d2951 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d2951, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46347 p hg
    simpa only [d8096, d2951, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d2951, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38492 p hg
    simpa only [d8096, d2951, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46349 (p : Pattern) (guard : d8095 p = 1) : d2935 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2935, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34587 p hg
    simpa only [d8095, d2935, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2935, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38550 p hg
    simpa only [d8095, d2935, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46350 (p : Pattern) (guard : d8101 p = 1) : d2961 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2961, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46349 p hg
    simpa only [d8101, d2961, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2961, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38551 p hg
    simpa only [d8101, d2961, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46351 (p : Pattern) (guard : d8102 p = 1) : d2968 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d2968, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46348 p hg
    simpa only [d8102, d2968, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d2968, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46350 p hg
    simpa only [d8102, d2968, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46352 (p : Pattern) (guard : d8095 p = 1) : d2911 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2911, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34595 p hg
    simpa only [d8095, d2911, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2911, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38507 p hg
    simpa only [d8095, d2911, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46353 (p : Pattern) (guard : d8101 p = 1) : d2954 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2954, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46352 p hg
    simpa only [d8101, d2954, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2954, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38508 p hg
    simpa only [d8101, d2954, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46354 (p : Pattern) (guard : d8106 p = 1) : d2957 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46301 p hg
    simpa only [d8106, d2957, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38558 p hg
    simpa only [d8106, d2957, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46355 (p : Pattern) (guard : d8107 p = 1) : d2969 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2969, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46353 p hg
    simpa only [d8107, d2969, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2969, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46354 p hg
    simpa only [d8107, d2969, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46356 (p : Pattern) (guard : d8108 p = 1) : d2970 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d2970, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46351 p hg
    simpa only [d8108, d2970, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d2970, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46355 p hg
    simpa only [d8108, d2970, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46357 (p : Pattern) (guard : d8106 p = 1) : d2928 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46305 p hg
    simpa only [d8106, d2928, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38564 p hg
    simpa only [d8106, d2928, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46358 (p : Pattern) (guard : d8107 p = 1) : d2971 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46327 p hg
    simpa only [d8107, d2971, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46357 p hg
    simpa only [d8107, d2971, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46359 (p : Pattern) (guard : d8106 p = 1) : d2931 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46308 p hg
    simpa only [d8106, d2931, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38569 p hg
    simpa only [d8106, d2931, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46360 (p : Pattern) (guard : d8112 p = 1) : d2932 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46359 p hg
    simpa only [d8112, d2932, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34543 p hg
    simpa only [d8112, d2932, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46361 (p : Pattern) (guard : d8113 p = 1) : d2972 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46358 p hg
    simpa only [d8113, d2972, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46360 p hg
    simpa only [d8113, d2972, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46362 (p : Pattern) (guard : d8114 p = 1) : d2973 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d2973, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46356 p hg
    simpa only [d8114, d2973, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d2973, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46361 p hg
    simpa only [d8114, d2973, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46363 (p : Pattern) (guard : d8107 p = 1) : d2974 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46339 p hg
    simpa only [d8107, d2974, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34455 p hg
    simpa only [d8107, d2974, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46364 (p : Pattern) (guard : d8113 p = 1) : d2975 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46363 p hg
    simpa only [d8113, d2975, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34611 p hg
    simpa only [d8113, d2975, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46365 (p : Pattern) (guard : d8119 p = 1) : d2976 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d2976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46364 p hg
    simpa only [d8119, d2976, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d2976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34613 p hg
    simpa only [d8119, d2976, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46366 (p : Pattern) (guard : d8120 p = 1) : d2977 p ≤ (0 : Int) + d399 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d2977, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46362 p hg
    simpa only [d8120, d2977, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d2977, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46365 p hg
    simpa only [d8120, d2977, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46367 (p : Pattern) (guard : d8121 p = 1) : d2978 p ≤ (0 : Int) + d400 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8115 p = 1 := by simpa only [d8121, d2978, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46346 p hg
    simpa only [d8121, d2978, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8120 p = 1 := by simpa only [d8121, d2978, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46366 p hg
    simpa only [d8121, d2978, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46368 (p : Pattern) (guard : d8122 p = 1) : d2979 p ≤ (0 : Int) + d401 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8116 p = 1 := by simpa only [d8122, d2979, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46314 p hg
    simpa only [d8122, d2979, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8121 p = 1 := by simpa only [d8122, d2979, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46367 p hg
    simpa only [d8122, d2979, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46369 (p : Pattern) (guard : d8087 p = 1) : d2948 p ≤ (0 : Int) + d342 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8087, d2948, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34350 p hg
    simpa only [d8087, d2948, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8086 p = 1 := by simpa only [d8087, d2948, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46316 p hg
    simpa only [d8087, d2948, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46370 (p : Pattern) (guard : d8092 p = 1) : d2949 p ≤ (0 : Int) + d344 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8087 p = 1 := by simpa only [d8092, d2949, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46369 p hg
    simpa only [d8092, d2949, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8091 p = 1 := by simpa only [d8092, d2949, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38582 p hg
    simpa only [d8092, d2949, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46371 (p : Pattern) (guard : d8097 p = 1) : d2952 p ≤ (0 : Int) + d346 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8092 p = 1 := by simpa only [d8097, d2952, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46370 p hg
    simpa only [d8097, d2952, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8096 p = 1 := by simpa only [d8097, d2952, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46348 p hg
    simpa only [d8097, d2952, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46372 (p : Pattern) (guard : d8096 p = 1) : d2953 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d2953, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46296 p hg
    simpa only [d8096, d2953, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d2953, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38499 p hg
    simpa only [d8096, d2953, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46373 (p : Pattern) (guard : d8102 p = 1) : d2955 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d2955, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46372 p hg
    simpa only [d8102, d2955, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d2955, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46353 p hg
    simpa only [d8102, d2955, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46374 (p : Pattern) (guard : d8103 p = 1) : d2956 p ≤ (0 : Int) + d402 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8097 p = 1 := by simpa only [d8103, d2956, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46371 p hg
    simpa only [d8103, d2956, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8102 p = 1 := by simpa only [d8103, d2956, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46373 p hg
    simpa only [d8103, d2956, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46375 (p : Pattern) (guard : d8108 p = 1) : d2959 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d2959, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46328 p hg
    simpa only [d8108, d2959, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d2959, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46333 p hg
    simpa only [d8108, d2959, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46376 (p : Pattern) (guard : d8109 p = 1) : d2960 p ≤ (0 : Int) + d404 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8103 p = 1 := by simpa only [d8109, d2960, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46374 p hg
    simpa only [d8109, d2960, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8108 p = 1 := by simpa only [d8109, d2960, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46375 p hg
    simpa only [d8109, d2960, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46377 (p : Pattern) (guard : d8091 p = 1) : d2935 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d2935, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38108 p hg
    simpa only [d8091, d2935, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d2935, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38526 p hg
    simpa only [d8091, d2935, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46378 (p : Pattern) (guard : d8096 p = 1) : d2961 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d2961, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46377 p hg
    simpa only [d8096, d2961, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d2961, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38527 p hg
    simpa only [d8096, d2961, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46379 (p : Pattern) (guard : d8102 p = 1) : d2964 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d2964, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46378 p hg
    simpa only [d8102, d2964, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d2964, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46339 p hg
    simpa only [d8102, d2964, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46380 (p : Pattern) (guard : d8108 p = 1) : d2965 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d2965, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46379 p hg
    simpa only [d8108, d2965, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d2965, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46343 p hg
    simpa only [d8108, d2965, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46381 (p : Pattern) (guard : d8114 p = 1) : d2966 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d2966, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46380 p hg
    simpa only [d8114, d2966, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d2966, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34577 p hg
    simpa only [d8114, d2966, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46382 (p : Pattern) (guard : d8115 p = 1) : d2967 p ≤ (0 : Int) + d406 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8109 p = 1 := by simpa only [d8115, d2967, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46376 p hg
    simpa only [d8115, d2967, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8114 p = 1 := by simpa only [d8115, d2967, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46381 p hg
    simpa only [d8115, d2967, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46383 (p : Pattern) (guard : d8091 p = 1) : d2950 p ≤ (0 : Int) + d367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d2950, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34620 p hg
    simpa only [d8091, d2950, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d2950, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46322 p hg
    simpa only [d8091, d2950, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46384 (p : Pattern) (guard : d8096 p = 1) : d2951 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d2951, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46383 p hg
    simpa only [d8096, d2951, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d2951, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38492 p hg
    simpa only [d8096, d2951, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46385 (p : Pattern) (guard : d8095 p = 1) : d2935 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2935, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38600 p hg
    simpa only [d8095, d2935, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2935, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38550 p hg
    simpa only [d8095, d2935, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46386 (p : Pattern) (guard : d8101 p = 1) : d2961 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2961, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46385 p hg
    simpa only [d8101, d2961, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2961, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38551 p hg
    simpa only [d8101, d2961, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46387 (p : Pattern) (guard : d8102 p = 1) : d2968 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d2968, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46384 p hg
    simpa only [d8102, d2968, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d2968, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46386 p hg
    simpa only [d8102, d2968, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46388 (p : Pattern) (guard : d8095 p = 1) : d2911 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2911, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34627 p hg
    simpa only [d8095, d2911, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2911, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38507 p hg
    simpa only [d8095, d2911, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46389 (p : Pattern) (guard : d8101 p = 1) : d2954 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2954, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46388 p hg
    simpa only [d8101, d2954, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2954, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38508 p hg
    simpa only [d8101, d2954, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46390 (p : Pattern) (guard : d8107 p = 1) : d2969 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2969, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46389 p hg
    simpa only [d8107, d2969, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2969, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46354 p hg
    simpa only [d8107, d2969, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46391 (p : Pattern) (guard : d8108 p = 1) : d2970 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d2970, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46387 p hg
    simpa only [d8108, d2970, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d2970, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46390 p hg
    simpa only [d8108, d2970, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46392 (p : Pattern) (guard : d8107 p = 1) : d2971 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2971, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46353 p hg
    simpa only [d8107, d2971, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2971, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46357 p hg
    simpa only [d8107, d2971, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46393 (p : Pattern) (guard : d8113 p = 1) : d2972 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2972, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46392 p hg
    simpa only [d8113, d2972, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2972, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46360 p hg
    simpa only [d8113, d2972, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46394 (p : Pattern) (guard : d8114 p = 1) : d2973 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d2973, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46391 p hg
    simpa only [d8114, d2973, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d2973, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46393 p hg
    simpa only [d8114, d2973, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46395 (p : Pattern) (guard : d8120 p = 1) : d2977 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d2977, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46394 p hg
    simpa only [d8120, d2977, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d2977, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46365 p hg
    simpa only [d8120, d2977, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46396 (p : Pattern) (guard : d8121 p = 1) : d2978 p ≤ (0 : Int) + d408 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8115 p = 1 := by simpa only [d8121, d2978, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46382 p hg
    simpa only [d8121, d2978, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8120 p = 1 := by simpa only [d8121, d2978, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46395 p hg
    simpa only [d8121, d2978, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46397 (p : Pattern) (guard : d8096 p = 1) : d2957 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d2957, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46241 p hg
    simpa only [d8096, d2957, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d2957, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38615 p hg
    simpa only [d8096, d2957, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46398 (p : Pattern) (guard : d8102 p = 1) : d2980 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d2980, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46397 p hg
    simpa only [d8102, d2980, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d2980, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46342 p hg
    simpa only [d8102, d2980, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46399 (p : Pattern) (guard : d8108 p = 1) : d2981 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d2981, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46398 p hg
    simpa only [d8108, d2981, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d2981, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46343 p hg
    simpa only [d8108, d2981, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46400 (p : Pattern) (guard : d8113 p = 1) : d2982 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46343 p hg
    simpa only [d8113, d2982, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34611 p hg
    simpa only [d8113, d2982, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46401 (p : Pattern) (guard : d8114 p = 1) : d2983 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d2983, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46399 p hg
    simpa only [d8114, d2983, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d2983, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46400 p hg
    simpa only [d8114, d2983, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46402 (p : Pattern) (guard : d8119 p = 1) : d2984 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d2984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46400 p hg
    simpa only [d8119, d2984, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d2984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34613 p hg
    simpa only [d8119, d2984, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46403 (p : Pattern) (guard : d8120 p = 1) : d2985 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d2985, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46401 p hg
    simpa only [d8120, d2985, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d2985, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46402 p hg
    simpa only [d8120, d2985, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46404 (p : Pattern) (guard : d8113 p = 1) : d2982 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2982, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46293 p hg
    simpa only [d8113, d2982, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2982, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34611 p hg
    simpa only [d8113, d2982, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46405 (p : Pattern) (guard : d8119 p = 1) : d2984 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d2984, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46404 p hg
    simpa only [d8119, d2984, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d2984, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34613 p hg
    simpa only [d8119, d2984, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46406 (p : Pattern) (guard : d8125 p = 1) : d2986 p ≤ (0 : Int) + d411 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d2986, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46405 p hg
    simpa only [d8125, d2986, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d2986, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36298 p hg
    simpa only [d8125, d2986, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46407 (p : Pattern) (guard : d8126 p = 1) : d2987 p ≤ (0 : Int) + d412 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d2987, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46403 p hg
    simpa only [d8126, d2987, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d2987, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46406 p hg
    simpa only [d8126, d2987, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46408 (p : Pattern) (guard : d8127 p = 1) : d2988 p ≤ (0 : Int) + d413 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8121 p = 1 := by simpa only [d8127, d2988, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46396 p hg
    simpa only [d8127, d2988, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8126 p = 1 := by simpa only [d8127, d2988, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46407 p hg
    simpa only [d8127, d2988, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46409 (p : Pattern) (guard : d8128 p = 1) : d2989 p ≤ (0 : Int) + d414 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8122 p = 1 := by simpa only [d8128, d2989, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46368 p hg
    simpa only [d8128, d2989, d414, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8127 p = 1 := by simpa only [d8128, d2989, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46408 p hg
    simpa only [d8128, d2989, d414, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46410 (p : Pattern) (guard : d8091 p = 1) : d2895 p ≤ (0 : Int) + d367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d2895, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34620 p hg
    simpa only [d8091, d2895, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d2895, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38703 p hg
    simpa only [d8091, d2895, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46411 (p : Pattern) (guard : d8096 p = 1) : d2896 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d2896, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46410 p hg
    simpa only [d8096, d2896, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d2896, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38634 p hg
    simpa only [d8096, d2896, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46412 (p : Pattern) (guard : d8097 p = 1) : d2896 p ≤ (0 : Int) + d415 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8092 p = 1 := by simpa only [d8097, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46225 p hg
    simpa only [d8097, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8096 p = 1 := by simpa only [d8097, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46411 p hg
    simpa only [d8097, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46413 (p : Pattern) (guard : d8091 p = 1) : d2895 p ≤ (0 : Int) + d324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d2895, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34580 p hg
    simpa only [d8091, d2895, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d2895, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38703 p hg
    simpa only [d8091, d2895, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46414 (p : Pattern) (guard : d8096 p = 1) : d2896 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d2896, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46413 p hg
    simpa only [d8096, d2896, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d2896, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38634 p hg
    simpa only [d8096, d2896, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46415 (p : Pattern) (guard : d8089 p = 1) : d2011 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d2011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34359 p hg
    simpa only [d8089, d2011, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d2011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38505 p hg
    simpa only [d8089, d2011, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46416 (p : Pattern) (guard : d5854 p = 1) : d1795 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38505 p hg
    simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17458 p hg
    simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46417 (p : Pattern) (guard : d8094 p = 1) : d2012 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d2012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46415 p hg
    simpa only [d8094, d2012, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d2012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46416 p hg
    simpa only [d8094, d2012, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46418 (p : Pattern) (guard : d8095 p = 1) : d2897 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2897, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34627 p hg
    simpa only [d8095, d2897, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2897, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46417 p hg
    simpa only [d8095, d2897, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46419 (p : Pattern) (guard : d8101 p = 1) : d2898 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2898, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46418 p hg
    simpa only [d8101, d2898, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2898, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38641 p hg
    simpa only [d8101, d2898, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46420 (p : Pattern) (guard : d8102 p = 1) : d2899 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d2899, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46414 p hg
    simpa only [d8102, d2899, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d2899, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46419 p hg
    simpa only [d8102, d2899, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46421 (p : Pattern) (guard : d8103 p = 1) : d2900 p ≤ (0 : Int) + d416 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8097 p = 1 := by simpa only [d8103, d2900, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46412 p hg
    simpa only [d8103, d2900, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8102 p = 1 := by simpa only [d8103, d2900, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46420 p hg
    simpa only [d8103, d2900, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46422 (p : Pattern) (guard : d8091 p = 1) : d2895 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d2895, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34518 p hg
    simpa only [d8091, d2895, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d2895, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38703 p hg
    simpa only [d8091, d2895, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46423 (p : Pattern) (guard : d8096 p = 1) : d2896 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d2896, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46422 p hg
    simpa only [d8096, d2896, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d2896, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38634 p hg
    simpa only [d8096, d2896, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46424 (p : Pattern) (guard : d8095 p = 1) : d2897 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2897, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34595 p hg
    simpa only [d8095, d2897, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2897, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46417 p hg
    simpa only [d8095, d2897, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46425 (p : Pattern) (guard : d8101 p = 1) : d2898 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2898, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46424 p hg
    simpa only [d8101, d2898, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2898, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38641 p hg
    simpa only [d8101, d2898, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46426 (p : Pattern) (guard : d8102 p = 1) : d2899 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d2899, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46423 p hg
    simpa only [d8102, d2899, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d2899, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46425 p hg
    simpa only [d8102, d2899, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46427 (p : Pattern) (guard : d8101 p = 1) : d2902 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46266 p hg
    simpa only [d8101, d2902, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38444 p hg
    simpa only [d8101, d2902, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46428 (p : Pattern) (guard : d8107 p = 1) : d2903 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46427 p hg
    simpa only [d8107, d2903, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34455 p hg
    simpa only [d8107, d2903, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46429 (p : Pattern) (guard : d8108 p = 1) : d2904 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d2904, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46426 p hg
    simpa only [d8108, d2904, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d2904, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46428 p hg
    simpa only [d8108, d2904, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46430 (p : Pattern) (guard : d8109 p = 1) : d2905 p ≤ (0 : Int) + d417 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8103 p = 1 := by simpa only [d8109, d2905, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46421 p hg
    simpa only [d8109, d2905, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8108 p = 1 := by simpa only [d8109, d2905, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46429 p hg
    simpa only [d8109, d2905, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46431 (p : Pattern) (guard : d8096 p = 1) : d2907 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d2907, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46254 p hg
    simpa only [d8096, d2907, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d2907, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38527 p hg
    simpa only [d8096, d2907, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46432 (p : Pattern) (guard : d8095 p = 1) : d2906 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34418 p hg
    simpa only [d8095, d2906, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38715 p hg
    simpa only [d8095, d2906, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46433 (p : Pattern) (guard : d8101 p = 1) : d2908 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2908, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46432 p hg
    simpa only [d8101, d2908, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2908, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38534 p hg
    simpa only [d8101, d2908, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46434 (p : Pattern) (guard : d8102 p = 1) : d2909 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d2909, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46431 p hg
    simpa only [d8102, d2909, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d2909, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46433 p hg
    simpa only [d8102, d2909, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46435 (p : Pattern) (guard : d8101 p = 1) : d2910 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46432 p hg
    simpa only [d8101, d2910, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38457 p hg
    simpa only [d8101, d2910, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46436 (p : Pattern) (guard : d8100 p = 1) : d2911 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34441 p hg
    simpa only [d8100, d2911, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38720 p hg
    simpa only [d8100, d2911, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46437 (p : Pattern) (guard : d8106 p = 1) : d2912 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46436 p hg
    simpa only [d8106, d2912, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34532 p hg
    simpa only [d8106, d2912, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46438 (p : Pattern) (guard : d8107 p = 1) : d2913 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46435 p hg
    simpa only [d8107, d2913, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46437 p hg
    simpa only [d8107, d2913, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46439 (p : Pattern) (guard : d8108 p = 1) : d2914 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d2914, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46434 p hg
    simpa only [d8108, d2914, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d2914, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46438 p hg
    simpa only [d8108, d2914, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46440 (p : Pattern) (guard : d8101 p = 1) : d2915 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46432 p hg
    simpa only [d8101, d2915, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34443 p hg
    simpa only [d8101, d2915, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46441 (p : Pattern) (guard : d8107 p = 1) : d2916 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46440 p hg
    simpa only [d8107, d2916, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46437 p hg
    simpa only [d8107, d2916, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46442 (p : Pattern) (guard : d8112 p = 1) : d2918 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46302 p hg
    simpa only [d8112, d2918, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34543 p hg
    simpa only [d8112, d2918, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46443 (p : Pattern) (guard : d8113 p = 1) : d2919 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46441 p hg
    simpa only [d8113, d2919, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46442 p hg
    simpa only [d8113, d2919, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46444 (p : Pattern) (guard : d8114 p = 1) : d2920 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d2920, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46439 p hg
    simpa only [d8114, d2920, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d2920, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46443 p hg
    simpa only [d8114, d2920, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46445 (p : Pattern) (guard : d8115 p = 1) : d2921 p ≤ (0 : Int) + d418 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8109 p = 1 := by simpa only [d8115, d2921, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46430 p hg
    simpa only [d8115, d2921, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8114 p = 1 := by simpa only [d8115, d2921, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46444 p hg
    simpa only [d8115, d2921, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46446 (p : Pattern) (guard : d8091 p = 1) : d2895 p ≤ (0 : Int) + d351 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d2895, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34653 p hg
    simpa only [d8091, d2895, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d2895, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38703 p hg
    simpa only [d8091, d2895, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46447 (p : Pattern) (guard : d8096 p = 1) : d2896 p ≤ (0 : Int) + d352 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d2896, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46446 p hg
    simpa only [d8096, d2896, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d2896, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38634 p hg
    simpa only [d8096, d2896, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46448 (p : Pattern) (guard : d8089 p = 1) : d2029 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d2029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34408 p hg
    simpa only [d8089, d2029, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d2029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38548 p hg
    simpa only [d8089, d2029, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46449 (p : Pattern) (guard : d5854 p = 1) : d1714 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38548 p hg
    simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17478 p hg
    simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46450 (p : Pattern) (guard : d8094 p = 1) : d2030 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d2030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46448 p hg
    simpa only [d8094, d2030, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d2030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46449 p hg
    simpa only [d8094, d2030, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46451 (p : Pattern) (guard : d8095 p = 1) : d2922 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2922, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34659 p hg
    simpa only [d8095, d2922, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2922, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46450 p hg
    simpa only [d8095, d2922, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46452 (p : Pattern) (guard : d8101 p = 1) : d2923 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2923, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46451 p hg
    simpa only [d8101, d2923, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2923, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38671 p hg
    simpa only [d8101, d2923, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46453 (p : Pattern) (guard : d8102 p = 1) : d2924 p ≤ (0 : Int) + d355 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d2924, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46447 p hg
    simpa only [d8102, d2924, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d2924, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46452 p hg
    simpa only [d8102, d2924, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46454 (p : Pattern) (guard : d8095 p = 1) : d2897 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2897, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34666 p hg
    simpa only [d8095, d2897, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2897, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46417 p hg
    simpa only [d8095, d2897, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46455 (p : Pattern) (guard : d8101 p = 1) : d2898 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2898, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46454 p hg
    simpa only [d8101, d2898, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2898, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38641 p hg
    simpa only [d8101, d2898, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46456 (p : Pattern) (guard : d8106 p = 1) : d2902 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46301 p hg
    simpa only [d8106, d2902, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38678 p hg
    simpa only [d8106, d2902, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46457 (p : Pattern) (guard : d8107 p = 1) : d2925 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2925, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46455 p hg
    simpa only [d8107, d2925, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2925, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46456 p hg
    simpa only [d8107, d2925, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46458 (p : Pattern) (guard : d8108 p = 1) : d2926 p ≤ (0 : Int) + d362 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d2926, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46453 p hg
    simpa only [d8108, d2926, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d2926, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46457 p hg
    simpa only [d8108, d2926, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46459 (p : Pattern) (guard : d8107 p = 1) : d2929 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2929, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46419 p hg
    simpa only [d8107, d2929, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2929, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46357 p hg
    simpa only [d8107, d2929, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46460 (p : Pattern) (guard : d8113 p = 1) : d2933 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2933, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46459 p hg
    simpa only [d8113, d2933, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2933, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46360 p hg
    simpa only [d8113, d2933, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46461 (p : Pattern) (guard : d8114 p = 1) : d2934 p ≤ (0 : Int) + d395 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d2934, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46458 p hg
    simpa only [d8114, d2934, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d2934, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46460 p hg
    simpa only [d8114, d2934, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46462 (p : Pattern) (guard : d8095 p = 1) : d2906 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2906, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34675 p hg
    simpa only [d8095, d2906, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2906, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38715 p hg
    simpa only [d8095, d2906, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46463 (p : Pattern) (guard : d8101 p = 1) : d2908 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2908, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46462 p hg
    simpa only [d8101, d2908, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2908, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38534 p hg
    simpa only [d8101, d2908, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46464 (p : Pattern) (guard : d8100 p = 1) : d2935 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34526 p hg
    simpa only [d8100, d2935, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38741 p hg
    simpa only [d8100, d2935, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46465 (p : Pattern) (guard : d8106 p = 1) : d2936 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2936, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46464 p hg
    simpa only [d8106, d2936, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2936, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34532 p hg
    simpa only [d8106, d2936, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46466 (p : Pattern) (guard : d8107 p = 1) : d2937 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2937, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46463 p hg
    simpa only [d8107, d2937, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2937, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46465 p hg
    simpa only [d8107, d2937, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46467 (p : Pattern) (guard : d8105 p = 1) : d2901 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d2901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34530 p hg
    simpa only [d8105, d2901, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d2901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23885 p hg
    simpa only [d8105, d2901, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46468 (p : Pattern) (guard : d8111 p = 1) : d2917 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46467 p hg
    simpa only [d8111, d2917, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8111, d2917, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46469 (p : Pattern) (guard : d8112 p = 1) : d2938 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46437 p hg
    simpa only [d8112, d2938, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46468 p hg
    simpa only [d8112, d2938, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46470 (p : Pattern) (guard : d8113 p = 1) : d2939 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2939, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46466 p hg
    simpa only [d8113, d2939, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2939, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46469 p hg
    simpa only [d8113, d2939, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46471 (p : Pattern) (guard : d8105 p = 1) : d2927 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d2927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34536 p hg
    simpa only [d8105, d2927, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d2927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23918 p hg
    simpa only [d8105, d2927, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46472 (p : Pattern) (guard : d8111 p = 1) : d2940 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46471 p hg
    simpa only [d8111, d2940, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8111, d2940, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46473 (p : Pattern) (guard : d8112 p = 1) : d2941 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46437 p hg
    simpa only [d8112, d2941, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46472 p hg
    simpa only [d8112, d2941, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46474 (p : Pattern) (guard : d8105 p = 1) : d2930 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d2930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34540 p hg
    simpa only [d8105, d2930, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d2930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23922 p hg
    simpa only [d8105, d2930, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46475 (p : Pattern) (guard : d8111 p = 1) : d2942 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46474 p hg
    simpa only [d8111, d2942, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8111, d2942, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46476 (p : Pattern) (guard : d8117 p = 1) : d2943 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46475 p hg
    simpa only [d8117, d2943, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8117, d2943, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46477 (p : Pattern) (guard : d8118 p = 1) : d2944 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46473 p hg
    simpa only [d8118, d2944, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46476 p hg
    simpa only [d8118, d2944, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46478 (p : Pattern) (guard : d8119 p = 1) : d2945 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d2945, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46470 p hg
    simpa only [d8119, d2945, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d2945, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46477 p hg
    simpa only [d8119, d2945, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46479 (p : Pattern) (guard : d8120 p = 1) : d2946 p ≤ (0 : Int) + d397 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d2946, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46461 p hg
    simpa only [d8120, d2946, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d2946, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46478 p hg
    simpa only [d8120, d2946, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
