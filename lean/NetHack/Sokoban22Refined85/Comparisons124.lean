/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons123
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare17360 (p : Pattern) (guard : d5537 p = 1) : d1916 p ≤ (0 : Int) + d2723 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5537, d1916, d2723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17358 p hg
    simpa only [d5537, d1916, d2723, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5537, d1916, d2723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17359 p hg
    simpa only [d5537, d1916, d2723, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17361 (p : Pattern) (guard : d5537 p = 1) : d1917 p ≤ (0 : Int) + d2724 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1917, d2724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17360 p hg
    simpa only [d1917, d2724, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1917, d2724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17314 p hg
    simpa only [d1917, d2724, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17362 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d2704 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare17363 (p : Pattern) (guard : d5537 p = 1) : d117 p ≤ (0 : Int) + d2725 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5537, d117, d2725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15057 p hg
    simpa only [d5537, d117, d2725, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5537, d117, d2725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17362 p hg
    simpa only [d5537, d117, d2725, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17364 (p : Pattern) (guard : d0 p = 1) : d1919 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare17365 (p : Pattern) (guard : d5502 p = 1) : d1920 p ≤ (0 : Int) + d2702 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d1920, d2702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d5502, d1920, d2702, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d1920, d2702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17364 p hg
    simpa only [d5502, d1920, d2702, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17366 (p : Pattern) (guard : d1 p = 1) : d1919 p ≤ (0 : Int) + d1919 p := by
  omega
theorem compare17367 (p : Pattern) (guard : d5502 p = 1) : d1919 p ≤ (0 : Int) + d2726 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17366 p hg
    simpa only [d5502, d2726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17364 p hg
    simpa only [d5502, d2726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17368 (p : Pattern) (guard : d5502 p = 1) : d1921 p ≤ (0 : Int) + d2727 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d1921, d2727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17365 p hg
    simpa only [d1921, d2727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d1921, d2727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17367 p hg
    simpa only [d1921, d2727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17369 (p : Pattern) (guard : d5537 p = 1) : d1922 p ≤ (0 : Int) + d2728 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5537, d1922, d2728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17368 p hg
    simpa only [d5537, d1922, d2728, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5537, d1922, d2728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5537, d1922, d2728, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17370 (p : Pattern) (guard : d5537 p = 1) : d1923 p ≤ (0 : Int) + d2729 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1923, d2729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17363 p hg
    simpa only [d1923, d2729, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1923, d2729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17369 p hg
    simpa only [d1923, d2729, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17371 (p : Pattern) (guard : d5537 p = 1) : d1924 p ≤ (0 : Int) + d2730 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1924, d2730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17361 p hg
    simpa only [d1924, d2730, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1924, d2730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17370 p hg
    simpa only [d1924, d2730, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17372 (p : Pattern) (guard : d5537 p = 1) : d1925 p ≤ (0 : Int) + d2731 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1925, d2731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17328 p hg
    simpa only [d1925, d2731, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1925, d2731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17180 p hg
    simpa only [d1925, d2731, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17373 (p : Pattern) (guard : d5537 p = 1) : d1926 p ≤ (0 : Int) + d2732 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1926, d2732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17371 p hg
    simpa only [d1926, d2732, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1926, d2732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17372 p hg
    simpa only [d1926, d2732, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17374 (p : Pattern) (guard : d5537 p = 1) : d1927 p ≤ (0 : Int) + d2733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1927, d2733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17328 p hg
    simpa only [d1927, d2733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1927, d2733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17184 p hg
    simpa only [d1927, d2733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17375 (p : Pattern) (guard : d5537 p = 1) : d1928 p ≤ (0 : Int) + d2734 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1928, d2734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17374 p hg
    simpa only [d1928, d2734, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1928, d2734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d1928, d2734, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17376 (p : Pattern) (guard : d5537 p = 1) : d1929 p ≤ (0 : Int) + d2735 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1929, d2735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17373 p hg
    simpa only [d1929, d2735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1929, d2735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17375 p hg
    simpa only [d1929, d2735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17377 (p : Pattern) (guard : d5537 p = 1) : d1930 p ≤ (0 : Int) + d2736 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1930, d2736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17363 p hg
    simpa only [d1930, d2736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1930, d2736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d1930, d2736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17378 (p : Pattern) (guard : d5537 p = 1) : d1931 p ≤ (0 : Int) + d2737 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1931, d2737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17348 p hg
    simpa only [d1931, d2737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1931, d2737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17377 p hg
    simpa only [d1931, d2737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17379 (p : Pattern) (guard : d5537 p = 1) : d1932 p ≤ (0 : Int) + d2738 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1932, d2738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17351 p hg
    simpa only [d1932, d2738, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1932, d2738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17192 p hg
    simpa only [d1932, d2738, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17380 (p : Pattern) (guard : d5537 p = 1) : d1933 p ≤ (0 : Int) + d2739 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1933, d2739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17378 p hg
    simpa only [d1933, d2739, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1933, d2739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17379 p hg
    simpa only [d1933, d2739, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17381 (p : Pattern) (guard : d5537 p = 1) : d1934 p ≤ (0 : Int) + d2740 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1934, d2740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17351 p hg
    simpa only [d1934, d2740, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1934, d2740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17194 p hg
    simpa only [d1934, d2740, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17382 (p : Pattern) (guard : d5537 p = 1) : d1935 p ≤ (0 : Int) + d2741 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1935, d2741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17381 p hg
    simpa only [d1935, d2741, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1935, d2741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d1935, d2741, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17383 (p : Pattern) (guard : d5537 p = 1) : d1936 p ≤ (0 : Int) + d2742 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1936, d2742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17380 p hg
    simpa only [d1936, d2742, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1936, d2742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17382 p hg
    simpa only [d1936, d2742, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17384 (p : Pattern) (guard : d5537 p = 1) : d1937 p ≤ (0 : Int) + d2743 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1937, d2743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17376 p hg
    simpa only [d1937, d2743, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1937, d2743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17383 p hg
    simpa only [d1937, d2743, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17385 (p : Pattern) (guard : d5537 p = 1) : d1938 p ≤ (0 : Int) + d2744 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1938, d2744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17357 p hg
    simpa only [d1938, d2744, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1938, d2744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17384 p hg
    simpa only [d1938, d2744, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17386 (p : Pattern) (guard : d0 p = 1) : d1940 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare17387 (p : Pattern) (guard : d5502 p = 1) : d1941 p ≤ (0 : Int) + d2677 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d1941, d2677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1274 p hg
    simpa only [d5502, d1941, d2677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d1941, d2677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17386 p hg
    simpa only [d5502, d1941, d2677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17388 (p : Pattern) (guard : d1 p = 1) : d1940 p ≤ (0 : Int) + d1940 p := by
  omega
theorem compare17389 (p : Pattern) (guard : d5502 p = 1) : d1940 p ≤ (0 : Int) + d2679 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17388 p hg
    simpa only [d5502, d2679, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17386 p hg
    simpa only [d5502, d2679, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17390 (p : Pattern) (guard : d5502 p = 1) : d1942 p ≤ (0 : Int) + d2680 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d1942, d2680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17387 p hg
    simpa only [d1942, d2680, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d1942, d2680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17389 p hg
    simpa only [d1942, d2680, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17391 (p : Pattern) (guard : d5537 p = 1) : d1943 p ≤ (0 : Int) + d2745 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5537, d1943, d2745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17390 p hg
    simpa only [d5537, d1943, d2745, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5537, d1943, d2745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5537, d1943, d2745, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17392 (p : Pattern) (guard : d5537 p = 1) : d1944 p ≤ (0 : Int) + d2746 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1944, d2746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17317 p hg
    simpa only [d1944, d2746, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1944, d2746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17391 p hg
    simpa only [d1944, d2746, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17393 (p : Pattern) (guard : d0 p = 1) : d1946 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare17394 (p : Pattern) (guard : d5502 p = 1) : d1947 p ≤ (0 : Int) + d2677 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d1947, d2677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1274 p hg
    simpa only [d5502, d1947, d2677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d1947, d2677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17393 p hg
    simpa only [d5502, d1947, d2677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17395 (p : Pattern) (guard : d0 p = 1) : d1949 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare17396 (p : Pattern) (guard : d5502 p = 1) : d1950 p ≤ (0 : Int) + d2679 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d1950, d2679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17388 p hg
    simpa only [d5502, d1950, d2679, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d1950, d2679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17395 p hg
    simpa only [d5502, d1950, d2679, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17397 (p : Pattern) (guard : d5502 p = 1) : d1951 p ≤ (0 : Int) + d2680 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d1951, d2680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17394 p hg
    simpa only [d1951, d2680, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d1951, d2680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17396 p hg
    simpa only [d1951, d2680, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17398 (p : Pattern) (guard : d5537 p = 1) : d1952 p ≤ (0 : Int) + d2745 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5537, d1952, d2745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17397 p hg
    simpa only [d5537, d1952, d2745, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5537, d1952, d2745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5537, d1952, d2745, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17399 (p : Pattern) (guard : d5537 p = 1) : d1953 p ≤ (0 : Int) + d2746 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1953, d2746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17317 p hg
    simpa only [d1953, d2746, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1953, d2746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17398 p hg
    simpa only [d1953, d2746, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17400 (p : Pattern) (guard : d5537 p = 1) : d1954 p ≤ (0 : Int) + d2746 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17392 p hg
    simpa only [d1954, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17399 p hg
    simpa only [d1954, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17401 (p : Pattern) (guard : d0 p = 1) : d1955 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare17402 (p : Pattern) (guard : d5502 p = 1) : d1956 p ≤ (0 : Int) + d2679 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d1956, d2679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17388 p hg
    simpa only [d5502, d1956, d2679, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d1956, d2679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17401 p hg
    simpa only [d5502, d1956, d2679, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17403 (p : Pattern) (guard : d5502 p = 1) : d1957 p ≤ (0 : Int) + d2680 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d1957, d2680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17394 p hg
    simpa only [d1957, d2680, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d1957, d2680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17402 p hg
    simpa only [d1957, d2680, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17404 (p : Pattern) (guard : d5537 p = 1) : d1958 p ≤ (0 : Int) + d2745 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5537, d1958, d2745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17403 p hg
    simpa only [d5537, d1958, d2745, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5537, d1958, d2745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5537, d1958, d2745, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17405 (p : Pattern) (guard : d5537 p = 1) : d1959 p ≤ (0 : Int) + d2746 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1959, d2746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17317 p hg
    simpa only [d1959, d2746, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1959, d2746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17404 p hg
    simpa only [d1959, d2746, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17406 (p : Pattern) (guard : d0 p = 1) : d1961 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare17407 (p : Pattern) (guard : d5502 p = 1) : d1962 p ≤ (0 : Int) + d2689 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d1962, d2689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2051 p hg
    simpa only [d5502, d1962, d2689, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d1962, d2689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17406 p hg
    simpa only [d5502, d1962, d2689, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17408 (p : Pattern) (guard : d1 p = 1) : d1964 p ≤ (0 : Int) + d1964 p := by
  omega
theorem compare17409 (p : Pattern) (guard : d0 p = 1) : d348 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare17410 (p : Pattern) (guard : d5502 p = 1) : d1965 p ≤ (0 : Int) + d2690 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d1965, d2690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17408 p hg
    simpa only [d5502, d1965, d2690, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d1965, d2690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17409 p hg
    simpa only [d5502, d1965, d2690, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17411 (p : Pattern) (guard : d5502 p = 1) : d1966 p ≤ (0 : Int) + d2691 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d1966, d2691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17407 p hg
    simpa only [d1966, d2691, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d1966, d2691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17410 p hg
    simpa only [d1966, d2691, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17412 (p : Pattern) (guard : d5537 p = 1) : d1967 p ≤ (0 : Int) + d2747 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5537, d1967, d2747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17411 p hg
    simpa only [d5537, d1967, d2747, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5537, d1967, d2747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5537, d1967, d2747, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17413 (p : Pattern) (guard : d5537 p = 1) : d1968 p ≤ (0 : Int) + d2748 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1968, d2748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17321 p hg
    simpa only [d1968, d2748, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1968, d2748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17412 p hg
    simpa only [d1968, d2748, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17414 (p : Pattern) (guard : d5537 p = 1) : d1969 p ≤ (0 : Int) + d2749 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1969, d2749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17405 p hg
    simpa only [d1969, d2749, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1969, d2749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17413 p hg
    simpa only [d1969, d2749, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17415 (p : Pattern) (guard : d5537 p = 1) : d1970 p ≤ (0 : Int) + d2750 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1970, d2750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17400 p hg
    simpa only [d1970, d2750, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1970, d2750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17414 p hg
    simpa only [d1970, d2750, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17416 (p : Pattern) (guard : d5537 p = 1) : d1971 p ≤ (0 : Int) + d2751 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1971, d2751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17414 p hg
    simpa only [d1971, d2751, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1971, d2751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17331 p hg
    simpa only [d1971, d2751, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17417 (p : Pattern) (guard : d5537 p = 1) : d1972 p ≤ (0 : Int) + d2752 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1972, d2752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17415 p hg
    simpa only [d1972, d2752, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1972, d2752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17416 p hg
    simpa only [d1972, d2752, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17418 (p : Pattern) (guard : d5537 p = 1) : d1973 p ≤ (0 : Int) + d2753 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1973, d2753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17363 p hg
    simpa only [d1973, d2753, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1973, d2753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17340 p hg
    simpa only [d1973, d2753, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17419 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d2709 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare17420 (p : Pattern) (guard : d5537 p = 1) : d121 p ≤ (0 : Int) + d2754 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5537, d121, d2754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15062 p hg
    simpa only [d5537, d121, d2754, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5537, d121, d2754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17419 p hg
    simpa only [d5537, d121, d2754, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17421 (p : Pattern) (guard : d5537 p = 1) : d1974 p ≤ (0 : Int) + d2755 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1974, d2755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17420 p hg
    simpa only [d1974, d2755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1974, d2755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17347 p hg
    simpa only [d1974, d2755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17422 (p : Pattern) (guard : d5537 p = 1) : d1975 p ≤ (0 : Int) + d2756 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1975, d2756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17418 p hg
    simpa only [d1975, d2756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1975, d2756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17421 p hg
    simpa only [d1975, d2756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17423 (p : Pattern) (guard : d5537 p = 1) : d1976 p ≤ (0 : Int) + d2757 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1976, d2757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17422 p hg
    simpa only [d1976, d2757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1976, d2757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d1976, d2757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17424 (p : Pattern) (guard : d5537 p = 1) : d1977 p ≤ (0 : Int) + d2758 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1977, d2758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17423 p hg
    simpa only [d1977, d2758, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1977, d2758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d1977, d2758, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17425 (p : Pattern) (guard : d5537 p = 1) : d1978 p ≤ (0 : Int) + d2759 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1978, d2759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17417 p hg
    simpa only [d1978, d2759, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1978, d2759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17424 p hg
    simpa only [d1978, d2759, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17426 (p : Pattern) (guard : d5537 p = 1) : d1979 p ≤ (0 : Int) + d2760 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1979, d2760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17399 p hg
    simpa only [d1979, d2760, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1979, d2760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17418 p hg
    simpa only [d1979, d2760, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17427 (p : Pattern) (guard : d5537 p = 1) : d1980 p ≤ (0 : Int) + d2761 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1980, d2761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17413 p hg
    simpa only [d1980, d2761, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1980, d2761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17180 p hg
    simpa only [d1980, d2761, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17428 (p : Pattern) (guard : d5537 p = 1) : d1981 p ≤ (0 : Int) + d2762 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1981, d2762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17426 p hg
    simpa only [d1981, d2762, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1981, d2762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17427 p hg
    simpa only [d1981, d2762, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17429 (p : Pattern) (guard : d5537 p = 1) : d1982 p ≤ (0 : Int) + d2763 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1982, d2763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17413 p hg
    simpa only [d1982, d2763, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1982, d2763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17184 p hg
    simpa only [d1982, d2763, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17430 (p : Pattern) (guard : d5537 p = 1) : d1983 p ≤ (0 : Int) + d2764 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1983, d2764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17429 p hg
    simpa only [d1983, d2764, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1983, d2764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d1983, d2764, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17431 (p : Pattern) (guard : d5537 p = 1) : d1984 p ≤ (0 : Int) + d2765 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1984, d2765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17428 p hg
    simpa only [d1984, d2765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1984, d2765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17430 p hg
    simpa only [d1984, d2765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17432 (p : Pattern) (guard : d5537 p = 1) : d1985 p ≤ (0 : Int) + d2766 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1985, d2766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17421 p hg
    simpa only [d1985, d2766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1985, d2766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d1985, d2766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17433 (p : Pattern) (guard : d5537 p = 1) : d1986 p ≤ (0 : Int) + d2767 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1986, d2767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17432 p hg
    simpa only [d1986, d2767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1986, d2767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d1986, d2767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17434 (p : Pattern) (guard : d5537 p = 1) : d1987 p ≤ (0 : Int) + d2768 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1987, d2768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17433 p hg
    simpa only [d1987, d2768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1987, d2768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d1987, d2768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17435 (p : Pattern) (guard : d5537 p = 1) : d1988 p ≤ (0 : Int) + d2769 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1988, d2769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17431 p hg
    simpa only [d1988, d2769, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1988, d2769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17434 p hg
    simpa only [d1988, d2769, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17436 (p : Pattern) (guard : d5537 p = 1) : d1989 p ≤ (0 : Int) + d2770 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1989, d2770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17425 p hg
    simpa only [d1989, d2770, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1989, d2770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17435 p hg
    simpa only [d1989, d2770, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17437 (p : Pattern) (guard : d5537 p = 1) : d1990 p ≤ (0 : Int) + d2771 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1990, d2771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17385 p hg
    simpa only [d1990, d2771, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1990, d2771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17436 p hg
    simpa only [d1990, d2771, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17438 (p : Pattern) (guard : d5537 p = 1) : d1991 p ≤ (0 : Int) + d2772 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1991, d2772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17331 p hg
    simpa only [d1991, d2772, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1991, d2772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d1991, d2772, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17439 (p : Pattern) (guard : d5537 p = 1) : d1992 p ≤ (0 : Int) + d2773 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1992, d2773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17438 p hg
    simpa only [d1992, d2773, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1992, d2773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d1992, d2773, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17440 (p : Pattern) (guard : d5537 p = 1) : d1993 p ≤ (0 : Int) + d2774 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1993, d2774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17439 p hg
    simpa only [d1993, d2774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1993, d2774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d1993, d2774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17441 (p : Pattern) (guard : d5537 p = 1) : d1994 p ≤ (0 : Int) + d2775 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1994, d2775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17440 p hg
    simpa only [d1994, d2775, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1994, d2775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d1994, d2775, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17442 (p : Pattern) (guard : d5537 p = 1) : d1995 p ≤ (0 : Int) + d2776 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1995, d2776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17436 p hg
    simpa only [d1995, d2776, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1995, d2776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17441 p hg
    simpa only [d1995, d2776, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17443 (p : Pattern) (guard : d5537 p = 1) : d1996 p ≤ (0 : Int) + d2777 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1996, d2777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17437 p hg
    simpa only [d1996, d2777, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1996, d2777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17442 p hg
    simpa only [d1996, d2777, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17444 (p : Pattern) (guard : d5537 p = 1) : d1997 p ≤ (0 : Int) + d2778 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1997, d2778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17318 p hg
    simpa only [d1997, d2778, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1997, d2778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17329 p hg
    simpa only [d1997, d2778, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17445 (p : Pattern) (guard : d5537 p = 1) : d1998 p ≤ (0 : Int) + d2779 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1998, d2779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17444 p hg
    simpa only [d1998, d2779, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1998, d2779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17332 p hg
    simpa only [d1998, d2779, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17446 (p : Pattern) (guard : d5537 p = 1) : d1999 p ≤ (0 : Int) + d2780 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1999, d2780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17445 p hg
    simpa only [d1999, d2780, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1999, d2780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17356 p hg
    simpa only [d1999, d2780, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17447 (p : Pattern) (guard : d5537 p = 1) : d2000 p ≤ (0 : Int) + d2781 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2000, d2781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17318 p hg
    simpa only [d2000, d2781, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2000, d2781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17370 p hg
    simpa only [d2000, d2781, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17448 (p : Pattern) (guard : d5537 p = 1) : d2001 p ≤ (0 : Int) + d2782 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2001, d2782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17447 p hg
    simpa only [d2001, d2782, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2001, d2782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17372 p hg
    simpa only [d2001, d2782, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17449 (p : Pattern) (guard : d5537 p = 1) : d2002 p ≤ (0 : Int) + d2783 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2002, d2783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17448 p hg
    simpa only [d2002, d2783, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2002, d2783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17375 p hg
    simpa only [d2002, d2783, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17450 (p : Pattern) (guard : d5537 p = 1) : d2003 p ≤ (0 : Int) + d2784 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2003, d2784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17449 p hg
    simpa only [d2003, d2784, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2003, d2784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17383 p hg
    simpa only [d2003, d2784, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17451 (p : Pattern) (guard : d5537 p = 1) : d2004 p ≤ (0 : Int) + d2785 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2004, d2785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17446 p hg
    simpa only [d2004, d2785, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2004, d2785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17450 p hg
    simpa only [d2004, d2785, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17452 (p : Pattern) (guard : d5537 p = 1) : d2005 p ≤ (0 : Int) + d2786 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2005, d2786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17451 p hg
    simpa only [d2005, d2786, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2005, d2786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17436 p hg
    simpa only [d2005, d2786, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17453 (p : Pattern) (guard : d5537 p = 1) : d2006 p ≤ (0 : Int) + d2787 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2006, d2787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17436 p hg
    simpa only [d2006, d2787, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2006, d2787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d2006, d2787, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17454 (p : Pattern) (guard : d5537 p = 1) : d2007 p ≤ (0 : Int) + d2788 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2007, d2788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17452 p hg
    simpa only [d2007, d2788, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2007, d2788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17453 p hg
    simpa only [d2007, d2788, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17455 (p : Pattern) (guard : d5537 p = 1) : d2008 p ≤ (0 : Int) + d2789 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2008, d2789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17443 p hg
    simpa only [d2008, d2789, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2008, d2789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17454 p hg
    simpa only [d2008, d2789, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17456 (p : Pattern) (guard : d5537 p = 1) : d2009 p ≤ (0 : Int) + d2790 p := by
  cases selected : p 71 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2009, d2790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17282 p hg
    simpa only [d2009, d2790, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2009, d2790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17455 p hg
    simpa only [d2009, d2790, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17457 (p : Pattern) (guard : d5537 p = 1) : d2010 p ≤ (0 : Int) + d2791 p := by
  cases selected : p 49 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2010, d2791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17305 p hg
    simpa only [d2010, d2791, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2010, d2791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17456 p hg
    simpa only [d2010, d2791, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17458 (p : Pattern) (guard : d0 p = 1) : d1795 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare17459 (p : Pattern) (guard : d5502 p = 1) : d2011 p ≤ (0 : Int) + d2520 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2011, d2520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2003 p hg
    simpa only [d5502, d2011, d2520, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2011, d2520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17458 p hg
    simpa only [d5502, d2011, d2520, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17460 (p : Pattern) (guard : d5502 p = 1) : d1795 p ≤ (0 : Int) + d2521 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17222 p hg
    simpa only [d5502, d2521, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17458 p hg
    simpa only [d5502, d2521, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17461 (p : Pattern) (guard : d5502 p = 1) : d2012 p ≤ (0 : Int) + d2522 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2012, d2522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17459 p hg
    simpa only [d2012, d2522, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2012, d2522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17460 p hg
    simpa only [d2012, d2522, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17462 (p : Pattern) (guard : d5537 p = 1) : d2013 p ≤ (0 : Int) + d2602 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5537, d2013, d2602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17461 p hg
    simpa only [d5537, d2013, d2602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5537, d2013, d2602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5537, d2013, d2602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17463 (p : Pattern) (guard : d5537 p = 1) : d2014 p ≤ (0 : Int) + d2603 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2014, d2603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17100 p hg
    simpa only [d2014, d2603, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2014, d2603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17462 p hg
    simpa only [d2014, d2603, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17464 (p : Pattern) (guard : d5537 p = 1) : d2015 p ≤ (0 : Int) + d2604 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2015, d2604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17206 p hg
    simpa only [d2015, d2604, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2015, d2604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17463 p hg
    simpa only [d2015, d2604, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17465 (p : Pattern) (guard : d5537 p = 1) : d2016 p ≤ (0 : Int) + d2605 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2016, d2605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17206 p hg
    simpa only [d2016, d2605, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2016, d2605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17464 p hg
    simpa only [d2016, d2605, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17466 (p : Pattern) (guard : d5537 p = 1) : d2017 p ≤ (0 : Int) + d2609 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2017, d2609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17464 p hg
    simpa only [d2017, d2609, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2017, d2609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17237 p hg
    simpa only [d2017, d2609, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17467 (p : Pattern) (guard : d5537 p = 1) : d2018 p ≤ (0 : Int) + d2610 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2018, d2610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17465 p hg
    simpa only [d2018, d2610, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2018, d2610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17466 p hg
    simpa only [d2018, d2610, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17468 (p : Pattern) (guard : d5537 p = 1) : d2019 p ≤ (0 : Int) + d2792 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2019, d2792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17161 p hg
    simpa only [d2019, d2792, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2019, d2792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17136 p hg
    simpa only [d2019, d2792, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17469 (p : Pattern) (guard : d5537 p = 1) : d2020 p ≤ (0 : Int) + d2793 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2020, d2793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17240 p hg
    simpa only [d2020, d2793, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2020, d2793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17468 p hg
    simpa only [d2020, d2793, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17470 (p : Pattern) (guard : d5537 p = 1) : d2021 p ≤ (0 : Int) + d2794 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2021, d2794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17161 p hg
    simpa only [d2021, d2794, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2021, d2794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17144 p hg
    simpa only [d2021, d2794, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17471 (p : Pattern) (guard : d5537 p = 1) : d2022 p ≤ (0 : Int) + d2795 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2022, d2795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17242 p hg
    simpa only [d2022, d2795, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2022, d2795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d2022, d2795, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17472 (p : Pattern) (guard : d5537 p = 1) : d2023 p ≤ (0 : Int) + d2796 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2023, d2796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17470 p hg
    simpa only [d2023, d2796, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2023, d2796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17471 p hg
    simpa only [d2023, d2796, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17473 (p : Pattern) (guard : d5537 p = 1) : d2024 p ≤ (0 : Int) + d2797 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2024, d2797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17469 p hg
    simpa only [d2024, d2797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2024, d2797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17472 p hg
    simpa only [d2024, d2797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17474 (p : Pattern) (guard : d5537 p = 1) : d2025 p ≤ (0 : Int) + d2798 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2025, d2798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17188 p hg
    simpa only [d2025, d2798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2025, d2798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17471 p hg
    simpa only [d2025, d2798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17475 (p : Pattern) (guard : d5537 p = 1) : d2026 p ≤ (0 : Int) + d2799 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2026, d2799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17474 p hg
    simpa only [d2026, d2799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2026, d2799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17195 p hg
    simpa only [d2026, d2799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17476 (p : Pattern) (guard : d5537 p = 1) : d2027 p ≤ (0 : Int) + d2800 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2027, d2800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17473 p hg
    simpa only [d2027, d2800, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2027, d2800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17475 p hg
    simpa only [d2027, d2800, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17477 (p : Pattern) (guard : d5537 p = 1) : d2028 p ≤ (0 : Int) + d2801 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2028, d2801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17467 p hg
    simpa only [d2028, d2801, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2028, d2801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17476 p hg
    simpa only [d2028, d2801, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17478 (p : Pattern) (guard : d0 p = 1) : d1714 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare17479 (p : Pattern) (guard : d5502 p = 1) : d2029 p ≤ (0 : Int) + d2540 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2029, d2540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2017 p hg
    simpa only [d5502, d2029, d2540, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2029, d2540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17478 p hg
    simpa only [d5502, d2029, d2540, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17480 (p : Pattern) (guard : d5502 p = 1) : d1714 p ≤ (0 : Int) + d2541 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17125 p hg
    simpa only [d5502, d2541, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17478 p hg
    simpa only [d5502, d2541, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17481 (p : Pattern) (guard : d5502 p = 1) : d2030 p ≤ (0 : Int) + d2542 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2030, d2542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17479 p hg
    simpa only [d2030, d2542, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2030, d2542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17480 p hg
    simpa only [d2030, d2542, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17482 (p : Pattern) (guard : d5537 p = 1) : d2031 p ≤ (0 : Int) + d2543 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5537, d2031, d2543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17481 p hg
    simpa only [d5537, d2031, d2543, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5537, d2031, d2543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5537, d2031, d2543, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17483 (p : Pattern) (guard : d5537 p = 1) : d2032 p ≤ (0 : Int) + d2611 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2032, d2611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17161 p hg
    simpa only [d2032, d2611, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2032, d2611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17482 p hg
    simpa only [d2032, d2611, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17484 (p : Pattern) (guard : d5537 p = 1) : d2033 p ≤ (0 : Int) + d2618 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2033, d2618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17206 p hg
    simpa only [d2033, d2618, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2033, d2618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17483 p hg
    simpa only [d2033, d2618, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17485 (p : Pattern) (guard : d5537 p = 1) : d2034 p ≤ (0 : Int) + d2619 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2034, d2619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17463 p hg
    simpa only [d2034, d2619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2034, d2619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17236 p hg
    simpa only [d2034, d2619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17486 (p : Pattern) (guard : d5537 p = 1) : d2035 p ≤ (0 : Int) + d2620 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2035, d2620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17484 p hg
    simpa only [d2035, d2620, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2035, d2620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17485 p hg
    simpa only [d2035, d2620, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17487 (p : Pattern) (guard : d5537 p = 1) : d2036 p ≤ (0 : Int) + d2621 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2036, d2621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17463 p hg
    simpa only [d2036, d2621, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2036, d2621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17180 p hg
    simpa only [d2036, d2621, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17488 (p : Pattern) (guard : d5537 p = 1) : d2037 p ≤ (0 : Int) + d2622 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2037, d2622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17487 p hg
    simpa only [d2037, d2622, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2037, d2622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17185 p hg
    simpa only [d2037, d2622, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17489 (p : Pattern) (guard : d5537 p = 1) : d2038 p ≤ (0 : Int) + d2623 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2038, d2623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17486 p hg
    simpa only [d2038, d2623, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2038, d2623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17488 p hg
    simpa only [d2038, d2623, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17490 (p : Pattern) (guard : d5537 p = 1) : d2039 p ≤ (0 : Int) + d2802 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2039, d2802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17468 p hg
    simpa only [d2039, d2802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2039, d2802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17146 p hg
    simpa only [d2039, d2802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17491 (p : Pattern) (guard : d5537 p = 1) : d2040 p ≤ (0 : Int) + d2803 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2040, d2803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17471 p hg
    simpa only [d2040, d2803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2040, d2803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17194 p hg
    simpa only [d2040, d2803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17492 (p : Pattern) (guard : d5537 p = 1) : d2041 p ≤ (0 : Int) + d2804 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2041, d2804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17490 p hg
    simpa only [d2041, d2804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2041, d2804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17491 p hg
    simpa only [d2041, d2804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17493 (p : Pattern) (guard : d5537 p = 1) : d2042 p ≤ (0 : Int) + d2805 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2042, d2805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17471 p hg
    simpa only [d2042, d2805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2042, d2805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d2042, d2805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17494 (p : Pattern) (guard : d5537 p = 1) : d2043 p ≤ (0 : Int) + d2806 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2043, d2806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17493 p hg
    simpa only [d2043, d2806, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2043, d2806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d2043, d2806, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17495 (p : Pattern) (guard : d5537 p = 1) : d2044 p ≤ (0 : Int) + d2807 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2044, d2807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17492 p hg
    simpa only [d2044, d2807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2044, d2807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17494 p hg
    simpa only [d2044, d2807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17496 (p : Pattern) (guard : d5537 p = 1) : d2045 p ≤ (0 : Int) + d2808 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2045, d2808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17489 p hg
    simpa only [d2045, d2808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2045, d2808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17495 p hg
    simpa only [d2045, d2808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17497 (p : Pattern) (guard : d5537 p = 1) : d2046 p ≤ (0 : Int) + d2809 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2046, d2809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17477 p hg
    simpa only [d2046, d2809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2046, d2809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17496 p hg
    simpa only [d2046, d2809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17498 (p : Pattern) (guard : d5502 p = 1) : d2047 p ≤ (0 : Int) + d2506 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2047, d2506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17202 p hg
    simpa only [d5502, d2047, d2506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2047, d2506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17207 p hg
    simpa only [d5502, d2047, d2506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17499 (p : Pattern) (guard : d5502 p = 1) : d2048 p ≤ (0 : Int) + d2507 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2048, d2507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17208 p hg
    simpa only [d2048, d2507, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2048, d2507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17498 p hg
    simpa only [d2048, d2507, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
