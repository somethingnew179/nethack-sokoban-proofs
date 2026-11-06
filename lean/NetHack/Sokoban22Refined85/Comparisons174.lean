/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons173
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare24360 (p : Pattern) (guard : d4985 p = 1) : d2920 p ≤ (2 : Int) + d5864 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d2920, d5864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24350 p hg
    simpa only [d2920, d5864, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d2920, d5864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24359 p hg
    simpa only [d2920, d5864, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24361 (p : Pattern) (guard : d4985 p = 1) : d2921 p ≤ (2 : Int) + d5865 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d2921, d5865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24305 p hg
    simpa only [d2921, d5865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d2921, d5865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24360 p hg
    simpa only [d2921, d5865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24362 (p : Pattern) (guard : d0 p = 1) : d31 p ≤ (2 : Int) + d1745 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24363 (p : Pattern) (guard : d1 p = 1) : d1713 p ≤ (2 : Int) + d1742 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1713, d1742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15711 p hg
    simpa only [d1713, d1742, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1713, d1742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4697 p hg
    simpa only [d1713, d1742, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24364 (p : Pattern) (guard : d1 p = 1) : d1714 p ≤ (2 : Int) + d1743 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1714, d1743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24363 p hg
    simpa only [d1714, d1743, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1714, d1743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4698 p hg
    simpa only [d1714, d1743, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24365 (p : Pattern) (guard : d1 p = 1) : d2029 p ≤ (2 : Int) + d1744 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2029, d1744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7126 p hg
    simpa only [d2029, d1744, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2029, d1744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24364 p hg
    simpa only [d2029, d1744, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24366 (p : Pattern) (guard : d1 p = 1) : d2030 p ≤ (2 : Int) + d1745 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2030, d1745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24365 p hg
    simpa only [d2030, d1745, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2030, d1745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24364 p hg
    simpa only [d2030, d1745, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24367 (p : Pattern) (guard : d4473 p = 1) : d2922 p ≤ (2 : Int) + d1745 p := by
  cases selected : p 204 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4473, d2922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24362 p hg
    simpa only [d4473, d2922, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4473, d2922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24366 p hg
    simpa only [d4473, d2922, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24368 (p : Pattern) (guard : d0 p = 1) : d1746 p ≤ (2 : Int) + d1745 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24369 (p : Pattern) (guard : d4985 p = 1) : d2923 p ≤ (2 : Int) + d1745 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4473 p = 1 := by simpa only [d4985, d2923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24367 p hg
    simpa only [d4985, d2923, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4985, d2923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24368 p hg
    simpa only [d4985, d2923, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24370 (p : Pattern) (guard : d4985 p = 1) : d2924 p ≤ (2 : Int) + d5866 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d2924, d5866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24283 p hg
    simpa only [d2924, d5866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d2924, d5866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24369 p hg
    simpa only [d2924, d5866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24371 (p : Pattern) (guard : d4985 p = 1) : d2925 p ≤ (2 : Int) + d5867 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d2925, d5867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24291 p hg
    simpa only [d2925, d5867, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d2925, d5867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24301 p hg
    simpa only [d2925, d5867, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24372 (p : Pattern) (guard : d4985 p = 1) : d2926 p ≤ (2 : Int) + d5868 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d2926, d5868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24370 p hg
    simpa only [d2926, d5868, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d2926, d5868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24371 p hg
    simpa only [d2926, d5868, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24373 (p : Pattern) (guard : d0 p = 1) : d58 p ≤ (2 : Int) + d1752 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24374 (p : Pattern) (guard : d1 p = 1) : d1752 p ≤ (2 : Int) + d1752 p := by
  omega
theorem compare24375 (p : Pattern) (guard : d4473 p = 1) : d2927 p ≤ (2 : Int) + d1752 p := by
  cases selected : p 204 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4473, d2927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24373 p hg
    simpa only [d4473, d2927, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4473, d2927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24374 p hg
    simpa only [d4473, d2927, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24376 (p : Pattern) (guard : d0 p = 1) : d1753 p ≤ (2 : Int) + d1752 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24377 (p : Pattern) (guard : d4985 p = 1) : d2928 p ≤ (2 : Int) + d1752 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4473 p = 1 := by simpa only [d4985, d2928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24375 p hg
    simpa only [d4985, d2928, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4985, d2928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24376 p hg
    simpa only [d4985, d2928, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24378 (p : Pattern) (guard : d4985 p = 1) : d2929 p ≤ (2 : Int) + d5869 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d2929, d5869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24291 p hg
    simpa only [d2929, d5869, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d2929, d5869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24377 p hg
    simpa only [d2929, d5869, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24379 (p : Pattern) (guard : d0 p = 1) : d40 p ≤ (2 : Int) + d1729 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24380 (p : Pattern) (guard : d1 p = 1) : d1729 p ≤ (2 : Int) + d1729 p := by
  omega
theorem compare24381 (p : Pattern) (guard : d4473 p = 1) : d2930 p ≤ (2 : Int) + d1729 p := by
  cases selected : p 204 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4473, d2930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24379 p hg
    simpa only [d4473, d2930, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4473, d2930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24380 p hg
    simpa only [d4473, d2930, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24382 (p : Pattern) (guard : d4985 p = 1) : d2931 p ≤ (2 : Int) + d1729 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4473 p = 1 := by simpa only [d4985, d2931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24381 p hg
    simpa only [d4985, d2931, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4985, d2931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24344 p hg
    simpa only [d4985, d2931, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24383 (p : Pattern) (guard : d4985 p = 1) : d2932 p ≤ (2 : Int) + d5862 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d2932, d5862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24382 p hg
    simpa only [d2932, d5862, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d2932, d5862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24302 p hg
    simpa only [d2932, d5862, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24384 (p : Pattern) (guard : d4985 p = 1) : d2933 p ≤ (2 : Int) + d5870 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d2933, d5870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24378 p hg
    simpa only [d2933, d5870, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d2933, d5870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24383 p hg
    simpa only [d2933, d5870, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24385 (p : Pattern) (guard : d4985 p = 1) : d2934 p ≤ (2 : Int) + d5871 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d2934, d5871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24372 p hg
    simpa only [d2934, d5871, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d2934, d5871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24384 p hg
    simpa only [d2934, d5871, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24386 (p : Pattern) (guard : d0 p = 1) : d31 p ≤ (2 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24387 (p : Pattern) (guard : d4473 p = 1) : d2935 p ≤ (2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4473, d2935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24386 p hg
    simpa only [d4473, d2935, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4473, d2935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15840 p hg
    simpa only [d4473, d2935, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24388 (p : Pattern) (guard : d4985 p = 1) : d2936 p ≤ (2 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4473 p = 1 := by simpa only [d4985, d2936, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24387 p hg
    simpa only [d4985, d2936, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4985, d2936, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6043 p hg
    simpa only [d4985, d2936, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24389 (p : Pattern) (guard : d4985 p = 1) : d2937 p ≤ (2 : Int) + d5872 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d2937, d5872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24331 p hg
    simpa only [d2937, d5872, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d2937, d5872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24388 p hg
    simpa only [d2937, d5872, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24390 (p : Pattern) (guard : d4985 p = 1) : d2938 p ≤ (2 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d2938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24348 p hg
    simpa only [d2938, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d2938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24357 p hg
    simpa only [d2938, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24391 (p : Pattern) (guard : d4985 p = 1) : d2939 p ≤ (2 : Int) + d5873 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d2939, d5873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24389 p hg
    simpa only [d2939, d5873, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d2939, d5873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24390 p hg
    simpa only [d2939, d5873, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24392 (p : Pattern) (guard : d0 p = 1) : d58 p ≤ (2 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24393 (p : Pattern) (guard : d4473 p = 1) : d2927 p ≤ (2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4473, d2927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24392 p hg
    simpa only [d4473, d2927, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4473, d2927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15849 p hg
    simpa only [d4473, d2927, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24394 (p : Pattern) (guard : d4985 p = 1) : d2940 p ≤ (2 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4473 p = 1 := by simpa only [d4985, d2940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24393 p hg
    simpa only [d4985, d2940, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4985, d2940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6043 p hg
    simpa only [d4985, d2940, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24395 (p : Pattern) (guard : d4985 p = 1) : d2941 p ≤ (2 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d2941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24348 p hg
    simpa only [d2941, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d2941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24394 p hg
    simpa only [d2941, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24396 (p : Pattern) (guard : d0 p = 1) : d40 p ≤ (2 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24397 (p : Pattern) (guard : d4473 p = 1) : d2930 p ≤ (2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4473, d2930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24396 p hg
    simpa only [d4473, d2930, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4473, d2930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15856 p hg
    simpa only [d4473, d2930, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24398 (p : Pattern) (guard : d4985 p = 1) : d2942 p ≤ (2 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4473 p = 1 := by simpa only [d4985, d2942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24397 p hg
    simpa only [d4985, d2942, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4985, d2942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6043 p hg
    simpa only [d4985, d2942, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24399 (p : Pattern) (guard : d4985 p = 1) : d2943 p ≤ (2 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d2943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24398 p hg
    simpa only [d2943, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d2943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24302 p hg
    simpa only [d2943, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24400 (p : Pattern) (guard : d4985 p = 1) : d2944 p ≤ (2 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d2944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24395 p hg
    simpa only [d2944, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d2944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24399 p hg
    simpa only [d2944, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24401 (p : Pattern) (guard : d4985 p = 1) : d2945 p ≤ (2 : Int) + d5874 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d2945, d5874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24391 p hg
    simpa only [d2945, d5874, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d2945, d5874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24400 p hg
    simpa only [d2945, d5874, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24402 (p : Pattern) (guard : d4985 p = 1) : d2946 p ≤ (2 : Int) + d5875 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d2946, d5875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24385 p hg
    simpa only [d2946, d5875, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d2946, d5875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24401 p hg
    simpa only [d2946, d5875, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24403 (p : Pattern) (guard : d4985 p = 1) : d2947 p ≤ (2 : Int) + d5876 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d2947, d5876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24361 p hg
    simpa only [d2947, d5876, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d2947, d5876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24402 p hg
    simpa only [d2947, d5876, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24404 (p : Pattern) (guard : d0 p = 1) : d14 p ≤ (2 : Int) + d1772 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24405 (p : Pattern) (guard : d1 p = 1) : d1775 p ≤ (2 : Int) + d1769 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1775, d1769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15669 p hg
    simpa only [d1775, d1769, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1775, d1769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4697 p hg
    simpa only [d1775, d1769, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24406 (p : Pattern) (guard : d1 p = 1) : d1776 p ≤ (2 : Int) + d1770 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1776, d1770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24405 p hg
    simpa only [d1776, d1770, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1776, d1770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4698 p hg
    simpa only [d1776, d1770, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24407 (p : Pattern) (guard : d1 p = 1) : d1777 p ≤ (2 : Int) + d1771 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1777, d1771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4688 p hg
    simpa only [d1777, d1771, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1777, d1771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24406 p hg
    simpa only [d1777, d1771, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24408 (p : Pattern) (guard : d1 p = 1) : d1770 p ≤ (2 : Int) + d1770 p := by
  omega
theorem compare24409 (p : Pattern) (guard : d1 p = 1) : d2047 p ≤ (2 : Int) + d1770 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24408 p hg
    simpa only [d2047, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24406 p hg
    simpa only [d2047, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24410 (p : Pattern) (guard : d1 p = 1) : d2048 p ≤ (2 : Int) + d1772 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2048, d1772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24407 p hg
    simpa only [d2048, d1772, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2048, d1772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24409 p hg
    simpa only [d2048, d1772, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24411 (p : Pattern) (guard : d4473 p = 1) : d2948 p ≤ (2 : Int) + d1772 p := by
  cases selected : p 204 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4473, d2948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24404 p hg
    simpa only [d4473, d2948, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4473, d2948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24410 p hg
    simpa only [d4473, d2948, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24412 (p : Pattern) (guard : d0 p = 1) : d1773 p ≤ (2 : Int) + d1772 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24413 (p : Pattern) (guard : d4985 p = 1) : d2949 p ≤ (2 : Int) + d1772 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4473 p = 1 := by simpa only [d4985, d2949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24411 p hg
    simpa only [d4985, d2949, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4985, d2949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24412 p hg
    simpa only [d4985, d2949, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24414 (p : Pattern) (guard : d0 p = 1) : d14 p ≤ (2 : Int) + d1781 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24415 (p : Pattern) (guard : d1 p = 1) : d1777 p ≤ (2 : Int) + d1777 p := by
  omega
theorem compare24416 (p : Pattern) (guard : d1 p = 1) : d2051 p ≤ (2 : Int) + d1778 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2051, d1778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15669 p hg
    simpa only [d2051, d1778, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2051, d1778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16124 p hg
    simpa only [d2051, d1778, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24417 (p : Pattern) (guard : d1 p = 1) : d2052 p ≤ (2 : Int) + d1779 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2052, d1779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24416 p hg
    simpa only [d2052, d1779, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2052, d1779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16127 p hg
    simpa only [d2052, d1779, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24418 (p : Pattern) (guard : d1 p = 1) : d2053 p ≤ (2 : Int) + d1780 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2053, d1780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24408 p hg
    simpa only [d2053, d1780, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2053, d1780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24417 p hg
    simpa only [d2053, d1780, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24419 (p : Pattern) (guard : d1 p = 1) : d2054 p ≤ (2 : Int) + d1781 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2054, d1781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24415 p hg
    simpa only [d2054, d1781, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2054, d1781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24418 p hg
    simpa only [d2054, d1781, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24420 (p : Pattern) (guard : d4473 p = 1) : d2950 p ≤ (2 : Int) + d1781 p := by
  cases selected : p 204 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4473, d2950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24414 p hg
    simpa only [d4473, d2950, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4473, d2950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24419 p hg
    simpa only [d4473, d2950, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24421 (p : Pattern) (guard : d0 p = 1) : d1782 p ≤ (2 : Int) + d1781 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24422 (p : Pattern) (guard : d4985 p = 1) : d2951 p ≤ (2 : Int) + d1781 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4473 p = 1 := by simpa only [d4985, d2951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24420 p hg
    simpa only [d4985, d2951, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4985, d2951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24421 p hg
    simpa only [d4985, d2951, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24423 (p : Pattern) (guard : d4985 p = 1) : d2952 p ≤ (2 : Int) + d5877 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d2952, d5877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24413 p hg
    simpa only [d2952, d5877, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d2952, d5877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24422 p hg
    simpa only [d2952, d5877, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24424 (p : Pattern) (guard : d0 p = 1) : d14 p ≤ (2 : Int) + d1788 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24425 (p : Pattern) (guard : d1 p = 1) : d1788 p ≤ (2 : Int) + d1788 p := by
  omega
theorem compare24426 (p : Pattern) (guard : d4473 p = 1) : d2906 p ≤ (2 : Int) + d1788 p := by
  cases selected : p 204 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4473, d2906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24424 p hg
    simpa only [d4473, d2906, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4473, d2906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24425 p hg
    simpa only [d4473, d2906, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24427 (p : Pattern) (guard : d0 p = 1) : d1789 p ≤ (2 : Int) + d1788 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24428 (p : Pattern) (guard : d4985 p = 1) : d2953 p ≤ (2 : Int) + d1788 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4473 p = 1 := by simpa only [d4985, d2953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24426 p hg
    simpa only [d4985, d2953, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4985, d2953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24427 p hg
    simpa only [d4985, d2953, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24429 (p : Pattern) (guard : d0 p = 1) : d18 p ≤ (2 : Int) + d1797 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24430 (p : Pattern) (guard : d1 p = 1) : d1797 p ≤ (2 : Int) + d1797 p := by
  omega
theorem compare24431 (p : Pattern) (guard : d4473 p = 1) : d2911 p ≤ (2 : Int) + d1797 p := by
  cases selected : p 204 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4473, d2911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24429 p hg
    simpa only [d4473, d2911, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4473, d2911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24430 p hg
    simpa only [d4473, d2911, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24432 (p : Pattern) (guard : d0 p = 1) : d1798 p ≤ (2 : Int) + d1797 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24433 (p : Pattern) (guard : d4985 p = 1) : d2954 p ≤ (2 : Int) + d1797 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4473 p = 1 := by simpa only [d4985, d2954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24431 p hg
    simpa only [d4985, d2954, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4985, d2954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24432 p hg
    simpa only [d4985, d2954, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24434 (p : Pattern) (guard : d4985 p = 1) : d2955 p ≤ (2 : Int) + d5878 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d2955, d5878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24428 p hg
    simpa only [d2955, d5878, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d2955, d5878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24433 p hg
    simpa only [d2955, d5878, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24435 (p : Pattern) (guard : d4985 p = 1) : d2956 p ≤ (2 : Int) + d5879 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d2956, d5879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24423 p hg
    simpa only [d2956, d5879, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d2956, d5879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24434 p hg
    simpa only [d2956, d5879, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24436 (p : Pattern) (guard : d0 p = 1) : d24 p ≤ (2 : Int) + d1803 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24437 (p : Pattern) (guard : d1 p = 1) : d1803 p ≤ (2 : Int) + d1803 p := by
  omega
theorem compare24438 (p : Pattern) (guard : d4473 p = 1) : d2901 p ≤ (2 : Int) + d1803 p := by
  cases selected : p 204 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4473, d2901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24436 p hg
    simpa only [d4473, d2901, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4473, d2901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24437 p hg
    simpa only [d4473, d2901, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24439 (p : Pattern) (guard : d0 p = 1) : d1804 p ≤ (2 : Int) + d1803 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24440 (p : Pattern) (guard : d4985 p = 1) : d2957 p ≤ (2 : Int) + d1803 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4473 p = 1 := by simpa only [d4985, d2957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24438 p hg
    simpa only [d4985, d2957, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4985, d2957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24439 p hg
    simpa only [d4985, d2957, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24441 (p : Pattern) (guard : d4985 p = 1) : d2958 p ≤ (2 : Int) + d5880 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d2958, d5880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24440 p hg
    simpa only [d2958, d5880, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d2958, d5880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24302 p hg
    simpa only [d2958, d5880, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24442 (p : Pattern) (guard : d4985 p = 1) : d2959 p ≤ (2 : Int) + d5881 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d2959, d5881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24434 p hg
    simpa only [d2959, d5881, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d2959, d5881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24441 p hg
    simpa only [d2959, d5881, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24443 (p : Pattern) (guard : d4985 p = 1) : d2960 p ≤ (2 : Int) + d5882 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d2960, d5882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24435 p hg
    simpa only [d2960, d5882, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d2960, d5882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24442 p hg
    simpa only [d2960, d5882, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24444 (p : Pattern) (guard : d0 p = 1) : d31 p ≤ (2 : Int) + d1717 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24445 (p : Pattern) (guard : d1 p = 1) : d1717 p ≤ (2 : Int) + d1717 p := by
  omega
theorem compare24446 (p : Pattern) (guard : d4473 p = 1) : d2935 p ≤ (2 : Int) + d1717 p := by
  cases selected : p 204 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4473, d2935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24444 p hg
    simpa only [d4473, d2935, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4473, d2935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24445 p hg
    simpa only [d4473, d2935, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24447 (p : Pattern) (guard : d4985 p = 1) : d2961 p ≤ (2 : Int) + d1717 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4473 p = 1 := by simpa only [d4985, d2961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24446 p hg
    simpa only [d4985, d2961, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4985, d2961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24317 p hg
    simpa only [d4985, d2961, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24448 (p : Pattern) (guard : d0 p = 1) : d35 p ≤ (2 : Int) + d1724 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24449 (p : Pattern) (guard : d1 p = 1) : d1724 p ≤ (2 : Int) + d1724 p := by
  omega
theorem compare24450 (p : Pattern) (guard : d4473 p = 1) : d2962 p ≤ (2 : Int) + d1724 p := by
  cases selected : p 204 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4473, d2962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24448 p hg
    simpa only [d4473, d2962, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4473, d2962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24449 p hg
    simpa only [d4473, d2962, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24451 (p : Pattern) (guard : d4985 p = 1) : d2963 p ≤ (2 : Int) + d1724 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4473 p = 1 := by simpa only [d4985, d2963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24450 p hg
    simpa only [d4985, d2963, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4985, d2963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24330 p hg
    simpa only [d4985, d2963, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24452 (p : Pattern) (guard : d4985 p = 1) : d2964 p ≤ (2 : Int) + d5861 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d2964, d5861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24447 p hg
    simpa only [d2964, d5861, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d2964, d5861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24451 p hg
    simpa only [d2964, d5861, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24453 (p : Pattern) (guard : d4985 p = 1) : d2965 p ≤ (2 : Int) + d5863 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d2965, d5863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24452 p hg
    simpa only [d2965, d5863, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d2965, d5863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24383 p hg
    simpa only [d2965, d5863, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24454 (p : Pattern) (guard : d4985 p = 1) : d2966 p ≤ (2 : Int) + d5864 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d2966, d5864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24453 p hg
    simpa only [d2966, d5864, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d2966, d5864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24302 p hg
    simpa only [d2966, d5864, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24455 (p : Pattern) (guard : d4985 p = 1) : d2967 p ≤ (2 : Int) + d5883 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d2967, d5883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24443 p hg
    simpa only [d2967, d5883, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d2967, d5883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24454 p hg
    simpa only [d2967, d5883, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24456 (p : Pattern) (guard : d4985 p = 1) : d2968 p ≤ (2 : Int) + d5884 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d2968, d5884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24422 p hg
    simpa only [d2968, d5884, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d2968, d5884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24447 p hg
    simpa only [d2968, d5884, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24457 (p : Pattern) (guard : d4985 p = 1) : d2969 p ≤ (2 : Int) + d5885 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d2969, d5885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24433 p hg
    simpa only [d2969, d5885, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d2969, d5885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24440 p hg
    simpa only [d2969, d5885, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24458 (p : Pattern) (guard : d4985 p = 1) : d2970 p ≤ (2 : Int) + d5886 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d2970, d5886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24456 p hg
    simpa only [d2970, d5886, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d2970, d5886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24457 p hg
    simpa only [d2970, d5886, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24459 (p : Pattern) (guard : d4985 p = 1) : d2971 p ≤ (2 : Int) + d5887 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d2971, d5887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24433 p hg
    simpa only [d2971, d5887, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d2971, d5887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24377 p hg
    simpa only [d2971, d5887, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24460 (p : Pattern) (guard : d4985 p = 1) : d2972 p ≤ (2 : Int) + d5888 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d2972, d5888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24459 p hg
    simpa only [d2972, d5888, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d2972, d5888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24383 p hg
    simpa only [d2972, d5888, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24461 (p : Pattern) (guard : d4985 p = 1) : d2973 p ≤ (2 : Int) + d5889 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d2973, d5889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24458 p hg
    simpa only [d2973, d5889, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d2973, d5889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24460 p hg
    simpa only [d2973, d5889, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24462 (p : Pattern) (guard : d4985 p = 1) : d2974 p ≤ (2 : Int) + d5872 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d2974, d5872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24451 p hg
    simpa only [d2974, d5872, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d2974, d5872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24302 p hg
    simpa only [d2974, d5872, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24463 (p : Pattern) (guard : d4985 p = 1) : d2975 p ≤ (2 : Int) + d5873 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d2975, d5873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24462 p hg
    simpa only [d2975, d5873, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d2975, d5873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24302 p hg
    simpa only [d2975, d5873, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24464 (p : Pattern) (guard : d4985 p = 1) : d2976 p ≤ (2 : Int) + d5874 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d2976, d5874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24463 p hg
    simpa only [d2976, d5874, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d2976, d5874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24302 p hg
    simpa only [d2976, d5874, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24465 (p : Pattern) (guard : d4985 p = 1) : d2977 p ≤ (2 : Int) + d5890 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d2977, d5890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24461 p hg
    simpa only [d2977, d5890, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d2977, d5890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24464 p hg
    simpa only [d2977, d5890, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24466 (p : Pattern) (guard : d4985 p = 1) : d2978 p ≤ (2 : Int) + d5891 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d2978, d5891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24455 p hg
    simpa only [d2978, d5891, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d2978, d5891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24465 p hg
    simpa only [d2978, d5891, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24467 (p : Pattern) (guard : d4985 p = 1) : d2979 p ≤ (2 : Int) + d5892 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d2979, d5892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24403 p hg
    simpa only [d2979, d5892, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d2979, d5892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24466 p hg
    simpa only [d2979, d5892, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24468 (p : Pattern) (guard : d4985 p = 1) : d2980 p ≤ (2 : Int) + d5893 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d2980, d5893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24440 p hg
    simpa only [d2980, d5893, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d2980, d5893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24382 p hg
    simpa only [d2980, d5893, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24469 (p : Pattern) (guard : d4985 p = 1) : d2981 p ≤ (2 : Int) + d5894 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d2981, d5894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24468 p hg
    simpa only [d2981, d5894, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d2981, d5894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24383 p hg
    simpa only [d2981, d5894, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24470 (p : Pattern) (guard : d4985 p = 1) : d2982 p ≤ (2 : Int) + d5895 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d2982, d5895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24383 p hg
    simpa only [d2982, d5895, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d2982, d5895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24302 p hg
    simpa only [d2982, d5895, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24471 (p : Pattern) (guard : d4985 p = 1) : d2983 p ≤ (2 : Int) + d5896 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d2983, d5896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24469 p hg
    simpa only [d2983, d5896, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d2983, d5896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24470 p hg
    simpa only [d2983, d5896, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24472 (p : Pattern) (guard : d4985 p = 1) : d2984 p ≤ (2 : Int) + d5897 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d2984, d5897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24470 p hg
    simpa only [d2984, d5897, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d2984, d5897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24302 p hg
    simpa only [d2984, d5897, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24473 (p : Pattern) (guard : d4985 p = 1) : d2985 p ≤ (2 : Int) + d5898 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d2985, d5898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24471 p hg
    simpa only [d2985, d5898, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d2985, d5898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24472 p hg
    simpa only [d2985, d5898, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24474 (p : Pattern) (guard : d4985 p = 1) : d2986 p ≤ (2 : Int) + d5899 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d2986, d5899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24472 p hg
    simpa only [d2986, d5899, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d2986, d5899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24302 p hg
    simpa only [d2986, d5899, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24475 (p : Pattern) (guard : d4985 p = 1) : d2987 p ≤ (2 : Int) + d5900 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d2987, d5900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24473 p hg
    simpa only [d2987, d5900, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d2987, d5900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24474 p hg
    simpa only [d2987, d5900, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24476 (p : Pattern) (guard : d4985 p = 1) : d2988 p ≤ (2 : Int) + d5901 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d2988, d5901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24466 p hg
    simpa only [d2988, d5901, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d2988, d5901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24475 p hg
    simpa only [d2988, d5901, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24477 (p : Pattern) (guard : d4985 p = 1) : d2989 p ≤ (2 : Int) + d5902 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d2989, d5902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24467 p hg
    simpa only [d2989, d5902, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d2989, d5902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24476 p hg
    simpa only [d2989, d5902, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24478 (p : Pattern) (guard : d4985 p = 1) : d2990 p ≤ (2 : Int) + d5903 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d2990, d5903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24466 p hg
    simpa only [d2990, d5903, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d2990, d5903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24302 p hg
    simpa only [d2990, d5903, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24479 (p : Pattern) (guard : d4985 p = 1) : d2991 p ≤ (2 : Int) + d5904 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d2991, d5904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24467 p hg
    simpa only [d2991, d5904, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d2991, d5904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24478 p hg
    simpa only [d2991, d5904, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24480 (p : Pattern) (guard : d4985 p = 1) : d2992 p ≤ (2 : Int) + d5905 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d2992, d5905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24477 p hg
    simpa only [d2992, d5905, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d2992, d5905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24479 p hg
    simpa only [d2992, d5905, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24481 (p : Pattern) (guard : d0 p = 1) : d103 p ≤ (2 : Int) + d1875 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24482 (p : Pattern) (guard : d1 p = 1) : d1939 p ≤ (2 : Int) + d1872 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1939, d1872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15921 p hg
    simpa only [d1939, d1872, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1939, d1872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2187 p hg
    simpa only [d1939, d1872, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24483 (p : Pattern) (guard : d1 p = 1) : d1940 p ≤ (2 : Int) + d1873 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1940, d1873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24482 p hg
    simpa only [d1940, d1873, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1940, d1873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2188 p hg
    simpa only [d1940, d1873, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24484 (p : Pattern) (guard : d1 p = 1) : d1941 p ≤ (2 : Int) + d1874 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1941, d1874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2156 p hg
    simpa only [d1941, d1874, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1941, d1874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24483 p hg
    simpa only [d1941, d1874, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24485 (p : Pattern) (guard : d1 p = 1) : d1942 p ≤ (2 : Int) + d1875 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1942, d1875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24484 p hg
    simpa only [d1942, d1875, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1942, d1875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24483 p hg
    simpa only [d1942, d1875, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24486 (p : Pattern) (guard : d4473 p = 1) : d2993 p ≤ (2 : Int) + d1875 p := by
  cases selected : p 204 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4473, d2993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24481 p hg
    simpa only [d4473, d2993, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4473, d2993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24485 p hg
    simpa only [d4473, d2993, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24487 (p : Pattern) (guard : d0 p = 1) : d1876 p ≤ (2 : Int) + d1875 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24488 (p : Pattern) (guard : d4985 p = 1) : d2994 p ≤ (2 : Int) + d1875 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4473 p = 1 := by simpa only [d4985, d2994, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24486 p hg
    simpa only [d4985, d2994, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4985, d2994, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24487 p hg
    simpa only [d4985, d2994, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24489 (p : Pattern) (guard : d0 p = 1) : d107 p ≤ (2 : Int) + d1883 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24490 (p : Pattern) (guard : d1 p = 1) : d1963 p ≤ (2 : Int) + d1880 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1963, d1880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15933 p hg
    simpa only [d1963, d1880, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1963, d1880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4942 p hg
    simpa only [d1963, d1880, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24491 (p : Pattern) (guard : d1 p = 1) : d1964 p ≤ (2 : Int) + d1881 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1964, d1881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24490 p hg
    simpa only [d1964, d1881, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1964, d1881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4943 p hg
    simpa only [d1964, d1881, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24492 (p : Pattern) (guard : d1 p = 1) : d2129 p ≤ (2 : Int) + d1882 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2129, d1882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2167 p hg
    simpa only [d2129, d1882, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2129, d1882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24491 p hg
    simpa only [d2129, d1882, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24493 (p : Pattern) (guard : d1 p = 1) : d2130 p ≤ (2 : Int) + d1883 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2130, d1883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24492 p hg
    simpa only [d2130, d1883, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2130, d1883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24491 p hg
    simpa only [d2130, d1883, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24494 (p : Pattern) (guard : d4473 p = 1) : d2995 p ≤ (2 : Int) + d1883 p := by
  cases selected : p 204 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4473, d2995, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24489 p hg
    simpa only [d4473, d2995, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4473, d2995, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24493 p hg
    simpa only [d4473, d2995, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24495 (p : Pattern) (guard : d0 p = 1) : d1884 p ≤ (2 : Int) + d1883 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24496 (p : Pattern) (guard : d4985 p = 1) : d2996 p ≤ (2 : Int) + d1883 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4473 p = 1 := by simpa only [d4985, d2996, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24494 p hg
    simpa only [d4985, d2996, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4985, d2996, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24495 p hg
    simpa only [d4985, d2996, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24497 (p : Pattern) (guard : d4985 p = 1) : d2997 p ≤ (2 : Int) + d5906 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d2997, d5906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24488 p hg
    simpa only [d2997, d5906, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d2997, d5906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24496 p hg
    simpa only [d2997, d5906, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24498 (p : Pattern) (guard : d4985 p = 1) : d2998 p ≤ (2 : Int) + d5907 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d2998, d5907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24488 p hg
    simpa only [d2998, d5907, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d2998, d5907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24497 p hg
    simpa only [d2998, d5907, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24499 (p : Pattern) (guard : d4985 p = 1) : d2999 p ≤ (2 : Int) + d5908 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d2999, d5908, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24377 p hg
    simpa only [d2999, d5908, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d2999, d5908, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24302 p hg
    simpa only [d2999, d5908, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
