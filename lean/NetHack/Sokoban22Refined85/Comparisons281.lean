/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons280
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare39340 (p : Pattern) (guard : d8123 p = 1) : d1913 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39338 p hg
    simpa only [d8123, d1913, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4396 p hg
    simpa only [d8123, d1913, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39341 (p : Pattern) (guard : d8124 p = 1) : d1914 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1914, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39339 p hg
    simpa only [d8124, d1914, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1914, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39340 p hg
    simpa only [d8124, d1914, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39342 (p : Pattern) (guard : d8125 p = 1) : d1999 p ≤ (0 : Int) + d406 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d1999, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39332 p hg
    simpa only [d8125, d1999, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d1999, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39341 p hg
    simpa only [d8125, d1999, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39343 (p : Pattern) (guard : d8100 p = 1) : d104 p ≤ (0 : Int) + d367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d104, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35327 p hg
    simpa only [d8100, d104, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d104, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d104, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39344 (p : Pattern) (guard : d8106 p = 1) : d1878 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d1878, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39343 p hg
    simpa only [d8106, d1878, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d1878, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39321 p hg
    simpa only [d8106, d1878, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39345 (p : Pattern) (guard : d8105 p = 1) : d117 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d117, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35333 p hg
    simpa only [d8105, d117, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d117, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d117, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39346 (p : Pattern) (guard : d8111 p = 1) : d1923 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d1923, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39345 p hg
    simpa only [d8111, d1923, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d1923, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15448 p hg
    simpa only [d8111, d1923, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39347 (p : Pattern) (guard : d8112 p = 1) : d2000 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2000, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39344 p hg
    simpa only [d8112, d2000, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2000, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39346 p hg
    simpa only [d8112, d2000, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39348 (p : Pattern) (guard : d8105 p = 1) : d108 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d108, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35340 p hg
    simpa only [d8105, d108, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d108, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d108, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39349 (p : Pattern) (guard : d8111 p = 1) : d1885 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d1885, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39348 p hg
    simpa only [d8111, d1885, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d1885, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15424 p hg
    simpa only [d8111, d1885, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39350 (p : Pattern) (guard : d8117 p = 1) : d1925 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d1925, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39349 p hg
    simpa only [d8117, d1925, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d1925, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38975 p hg
    simpa only [d8117, d1925, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39351 (p : Pattern) (guard : d8118 p = 1) : d2001 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2001, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39347 p hg
    simpa only [d8118, d2001, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2001, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39350 p hg
    simpa only [d8118, d2001, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39352 (p : Pattern) (guard : d8117 p = 1) : d1927 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d1927, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39325 p hg
    simpa only [d8117, d1927, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d1927, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39274 p hg
    simpa only [d8117, d1927, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39353 (p : Pattern) (guard : d8123 p = 1) : d1928 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1928, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39352 p hg
    simpa only [d8123, d1928, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1928, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d1928, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39354 (p : Pattern) (guard : d8124 p = 1) : d2002 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d2002, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39351 p hg
    simpa only [d8124, d2002, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d2002, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39353 p hg
    simpa only [d8124, d2002, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39355 (p : Pattern) (guard : d0 p = 1) : d1930 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare39356 (p : Pattern) (guard : d8117 p = 1) : d1931 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d1931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39334 p hg
    simpa only [d8117, d1931, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d1931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39355 p hg
    simpa only [d8117, d1931, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39357 (p : Pattern) (guard : d0 p = 1) : d1932 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare39358 (p : Pattern) (guard : d8123 p = 1) : d1933 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39356 p hg
    simpa only [d8123, d1933, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39357 p hg
    simpa only [d8123, d1933, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39359 (p : Pattern) (guard : d0 p = 1) : d1935 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare39360 (p : Pattern) (guard : d8129 p = 1) : d1936 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d1936, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39358 p hg
    simpa only [d8129, d1936, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d1936, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39359 p hg
    simpa only [d8129, d1936, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39361 (p : Pattern) (guard : d8130 p = 1) : d2003 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d2003, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39354 p hg
    simpa only [d8130, d2003, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d2003, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39360 p hg
    simpa only [d8130, d2003, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39362 (p : Pattern) (guard : d8131 p = 1) : d2004 p ≤ (0 : Int) + d408 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d2004, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39342 p hg
    simpa only [d8131, d2004, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d2004, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39361 p hg
    simpa only [d8131, d2004, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39363 (p : Pattern) (guard : d5854 p = 1) : d1941 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d1941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35099 p hg
    simpa only [d5854, d1941, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d1941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17386 p hg
    simpa only [d5854, d1941, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39364 (p : Pattern) (guard : d8099 p = 1) : d1942 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d1942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39363 p hg
    simpa only [d8099, d1942, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d1942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17386 p hg
    simpa only [d8099, d1942, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39365 (p : Pattern) (guard : d8105 p = 1) : d1943 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d1943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39364 p hg
    simpa only [d8105, d1943, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d1943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d1943, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39366 (p : Pattern) (guard : d8106 p = 1) : d1944 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d1944, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39221 p hg
    simpa only [d8106, d1944, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d1944, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39365 p hg
    simpa only [d8106, d1944, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39367 (p : Pattern) (guard : d8111 p = 1) : d1953 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d1953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35252 p hg
    simpa only [d8111, d1953, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d1953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15467 p hg
    simpa only [d8111, d1953, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39368 (p : Pattern) (guard : d8112 p = 1) : d1954 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1954, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39366 p hg
    simpa only [d8112, d1954, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1954, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39367 p hg
    simpa only [d8112, d1954, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39369 (p : Pattern) (guard : d8111 p = 1) : d1959 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d1959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35252 p hg
    simpa only [d8111, d1959, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d1959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15470 p hg
    simpa only [d8111, d1959, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39370 (p : Pattern) (guard : d0 p = 1) : d1968 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare39371 (p : Pattern) (guard : d8117 p = 1) : d1969 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d1969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39369 p hg
    simpa only [d8117, d1969, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d1969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39370 p hg
    simpa only [d8117, d1969, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39372 (p : Pattern) (guard : d8118 p = 1) : d1970 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1970, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39368 p hg
    simpa only [d8118, d1970, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1970, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39371 p hg
    simpa only [d8118, d1970, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39373 (p : Pattern) (guard : d0 p = 1) : d1888 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare39374 (p : Pattern) (guard : d8123 p = 1) : d1971 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39371 p hg
    simpa only [d8123, d1971, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39373 p hg
    simpa only [d8123, d1971, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39375 (p : Pattern) (guard : d8124 p = 1) : d1972 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1972, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39372 p hg
    simpa only [d8124, d1972, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1972, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39374 p hg
    simpa only [d8124, d1972, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39376 (p : Pattern) (guard : d8111 p = 1) : d1973 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d1973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35214 p hg
    simpa only [d8111, d1973, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d1973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15431 p hg
    simpa only [d8111, d1973, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39377 (p : Pattern) (guard : d0 p = 1) : d1974 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare39378 (p : Pattern) (guard : d8117 p = 1) : d1975 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d1975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39376 p hg
    simpa only [d8117, d1975, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d1975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39377 p hg
    simpa only [d8117, d1975, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39379 (p : Pattern) (guard : d8123 p = 1) : d1976 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39378 p hg
    simpa only [d8123, d1976, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d1976, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39380 (p : Pattern) (guard : d8129 p = 1) : d1977 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d1977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39379 p hg
    simpa only [d8129, d1977, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d1977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8129, d1977, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39381 (p : Pattern) (guard : d8130 p = 1) : d1978 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d1978, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39375 p hg
    simpa only [d8130, d1978, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d1978, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39380 p hg
    simpa only [d8130, d1978, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39382 (p : Pattern) (guard : d8111 p = 1) : d1953 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d1953, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35705 p hg
    simpa only [d8111, d1953, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d1953, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15467 p hg
    simpa only [d8111, d1953, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39383 (p : Pattern) (guard : d0 p = 1) : d1973 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare39384 (p : Pattern) (guard : d8117 p = 1) : d1979 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d1979, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39382 p hg
    simpa only [d8117, d1979, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d1979, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39383 p hg
    simpa only [d8117, d1979, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39385 (p : Pattern) (guard : d0 p = 1) : d1980 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare39386 (p : Pattern) (guard : d8123 p = 1) : d1981 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1981, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39384 p hg
    simpa only [d8123, d1981, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1981, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39385 p hg
    simpa only [d8123, d1981, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39387 (p : Pattern) (guard : d0 p = 1) : d1983 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare39388 (p : Pattern) (guard : d8129 p = 1) : d1984 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d1984, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39386 p hg
    simpa only [d8129, d1984, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d1984, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39387 p hg
    simpa only [d8129, d1984, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39389 (p : Pattern) (guard : d0 p = 1) : d1987 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare39390 (p : Pattern) (guard : d8135 p = 1) : d1988 p ≤ (0 : Int) + d411 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d1988, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39388 p hg
    simpa only [d8135, d1988, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d1988, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39389 p hg
    simpa only [d8135, d1988, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39391 (p : Pattern) (guard : d8136 p = 1) : d1989 p ≤ (0 : Int) + d412 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d1989, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39381 p hg
    simpa only [d8136, d1989, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d1989, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39390 p hg
    simpa only [d8136, d1989, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39392 (p : Pattern) (guard : d8137 p = 1) : d2005 p ≤ (0 : Int) + d413 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d2005, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39362 p hg
    simpa only [d8137, d2005, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d2005, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39391 p hg
    simpa only [d8137, d2005, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39393 (p : Pattern) (guard : d8106 p = 1) : d1944 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d1944, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35699 p hg
    simpa only [d8106, d1944, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d1944, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39365 p hg
    simpa only [d8106, d1944, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39394 (p : Pattern) (guard : d8112 p = 1) : d1954 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1954, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39393 p hg
    simpa only [d8112, d1954, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1954, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39382 p hg
    simpa only [d8112, d1954, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39395 (p : Pattern) (guard : d8118 p = 1) : d1970 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1970, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39394 p hg
    simpa only [d8118, d1970, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1970, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39371 p hg
    simpa only [d8118, d1970, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39396 (p : Pattern) (guard : d8124 p = 1) : d1972 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1972, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39395 p hg
    simpa only [d8124, d1972, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1972, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39374 p hg
    simpa only [d8124, d1972, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39397 (p : Pattern) (guard : d8130 p = 1) : d1978 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d1978, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39396 p hg
    simpa only [d8130, d1978, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d1978, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39380 p hg
    simpa only [d8130, d1978, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39398 (p : Pattern) (guard : d8111 p = 1) : d1953 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d1953, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35749 p hg
    simpa only [d8111, d1953, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d1953, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15467 p hg
    simpa only [d8111, d1953, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39399 (p : Pattern) (guard : d8117 p = 1) : d1979 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d1979, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39398 p hg
    simpa only [d8117, d1979, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d1979, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39383 p hg
    simpa only [d8117, d1979, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39400 (p : Pattern) (guard : d8123 p = 1) : d1981 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1981, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39399 p hg
    simpa only [d8123, d1981, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1981, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39385 p hg
    simpa only [d8123, d1981, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39401 (p : Pattern) (guard : d8129 p = 1) : d1984 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d1984, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39400 p hg
    simpa only [d8129, d1984, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d1984, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39387 p hg
    simpa only [d8129, d1984, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39402 (p : Pattern) (guard : d8135 p = 1) : d1988 p ≤ (0 : Int) + d421 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d1988, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39401 p hg
    simpa only [d8135, d1988, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d1988, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39389 p hg
    simpa only [d8135, d1988, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39403 (p : Pattern) (guard : d8136 p = 1) : d1989 p ≤ (0 : Int) + d422 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d1989, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39397 p hg
    simpa only [d8136, d1989, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d1989, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39402 p hg
    simpa only [d8136, d1989, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39404 (p : Pattern) (guard : d8142 p = 1) : d2006 p ≤ (0 : Int) + d444 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8136 p = 1 := by simpa only [d8142, d2006, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39403 p hg
    simpa only [d8142, d2006, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8141 p = 1 := by simpa only [d8142, d2006, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37397 p hg
    simpa only [d8142, d2006, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39405 (p : Pattern) (guard : d8143 p = 1) : d2007 p ≤ (0 : Int) + d445 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8137 p = 1 := by simpa only [d8143, d2007, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39392 p hg
    simpa only [d8143, d2007, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8142 p = 1 := by simpa only [d8143, d2007, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39404 p hg
    simpa only [d8143, d2007, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39406 (p : Pattern) (guard : d8144 p = 1) : d2008 p ≤ (0 : Int) + d446 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8138 p = 1 := by simpa only [d8144, d2008, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39318 p hg
    simpa only [d8144, d2008, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8143 p = 1 := by simpa only [d8144, d2008, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39405 p hg
    simpa only [d8144, d2008, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39407 (p : Pattern) (guard : d8145 p = 1) : d2009 p ≤ (0 : Int) + d447 p := by
  cases selected : p 71 with
  | false =>
    have hg : d8139 p = 1 := by simpa only [d8145, d2009, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39133 p hg
    simpa only [d8145, d2009, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8144 p = 1 := by simpa only [d8145, d2009, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39406 p hg
    simpa only [d8145, d2009, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39408 (p : Pattern) (guard : d8146 p = 1) : d2010 p ≤ (0 : Int) + d447 p := by
  cases selected : p 49 with
  | false =>
    have hg : d8140 p = 1 := by simpa only [d8146, d2010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39000 p hg
    simpa only [d8146, d2010, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8145 p = 1 := by simpa only [d8146, d2010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39407 p hg
    simpa only [d8146, d2010, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39409 (p : Pattern) (guard : d8091 p = 1) : d1850 p ≤ (0 : Int) + d432 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d1850, d432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35382 p hg
    simpa only [d8091, d1850, d432, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d1850, d432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39134 p hg
    simpa only [d8091, d1850, d432, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39410 (p : Pattern) (guard : d8085 p = 1) : d1685 p ≤ (0 : Int) + d320 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d1685, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34319 p hg
    simpa only [d8085, d1685, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d1685, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38345 p hg
    simpa only [d8085, d1685, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39411 (p : Pattern) (guard : d8090 p = 1) : d1686 p ≤ (0 : Int) + d321 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d1686, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39410 p hg
    simpa only [d8090, d1686, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d1686, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38632 p hg
    simpa only [d8090, d1686, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39412 (p : Pattern) (guard : d8095 p = 1) : d1687 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d1687, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39411 p hg
    simpa only [d8095, d1687, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d1687, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34367 p hg
    simpa only [d8095, d1687, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39413 (p : Pattern) (guard : d8096 p = 1) : d1851 p ≤ (0 : Int) + d433 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d1851, d433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39409 p hg
    simpa only [d8096, d1851, d433, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d1851, d433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39412 p hg
    simpa only [d8096, d1851, d433, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39414 (p : Pattern) (guard : d8095 p = 1) : d15 p ≤ (0 : Int) + d342 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d15, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35387 p hg
    simpa only [d8095, d15, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d15, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34367 p hg
    simpa only [d8095, d15, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39415 (p : Pattern) (guard : d8089 p = 1) : d1685 p ≤ (0 : Int) + d332 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d1685, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34923 p hg
    simpa only [d8089, d1685, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d1685, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38631 p hg
    simpa only [d8089, d1685, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39416 (p : Pattern) (guard : d8094 p = 1) : d1686 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d1686, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39415 p hg
    simpa only [d8094, d1686, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d1686, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38884 p hg
    simpa only [d8094, d1686, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39417 (p : Pattern) (guard : d8100 p = 1) : d1687 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d1687, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39416 p hg
    simpa only [d8100, d1687, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d1687, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d1687, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39418 (p : Pattern) (guard : d8101 p = 1) : d1692 p ≤ (0 : Int) + d344 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d1692, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39414 p hg
    simpa only [d8101, d1692, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d1692, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39417 p hg
    simpa only [d8101, d1692, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39419 (p : Pattern) (guard : d8102 p = 1) : d1852 p ≤ (0 : Int) + d434 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d1852, d434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39413 p hg
    simpa only [d8102, d1852, d434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d1852, d434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39418 p hg
    simpa only [d8102, d1852, d434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39420 (p : Pattern) (guard : d8100 p = 1) : d19 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d19, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35394 p hg
    simpa only [d8100, d19, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d19, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d19, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39421 (p : Pattern) (guard : d8106 p = 1) : d1698 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d1698, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39420 p hg
    simpa only [d8106, d1698, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d1698, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38892 p hg
    simpa only [d8106, d1698, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39422 (p : Pattern) (guard : d8107 p = 1) : d1699 p ≤ (0 : Int) + d355 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d1699, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39100 p hg
    simpa only [d8107, d1699, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d1699, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39421 p hg
    simpa only [d8107, d1699, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39423 (p : Pattern) (guard : d8108 p = 1) : d1853 p ≤ (0 : Int) + d435 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d1853, d435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39419 p hg
    simpa only [d8108, d1853, d435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d1853, d435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39422 p hg
    simpa only [d8108, d1853, d435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39424 (p : Pattern) (guard : d8107 p = 1) : d1699 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d1699, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38916 p hg
    simpa only [d8107, d1699, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d1699, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39105 p hg
    simpa only [d8107, d1699, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39425 (p : Pattern) (guard : d8112 p = 1) : d1707 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1707, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38818 p hg
    simpa only [d8112, d1707, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1707, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34543 p hg
    simpa only [d8112, d1707, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39426 (p : Pattern) (guard : d8113 p = 1) : d1708 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1708, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39424 p hg
    simpa only [d8113, d1708, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1708, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39425 p hg
    simpa only [d8113, d1708, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39427 (p : Pattern) (guard : d8114 p = 1) : d1854 p ≤ (0 : Int) + d436 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d1854, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39423 p hg
    simpa only [d8114, d1854, d436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d1854, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39426 p hg
    simpa only [d8114, d1854, d436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39428 (p : Pattern) (guard : d8101 p = 1) : d1719 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d1719, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35565 p hg
    simpa only [d8101, d1719, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d1719, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38551 p hg
    simpa only [d8101, d1719, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39429 (p : Pattern) (guard : d8106 p = 1) : d1726 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d1726, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35414 p hg
    simpa only [d8106, d1726, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d1726, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38732 p hg
    simpa only [d8106, d1726, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39430 (p : Pattern) (guard : d8107 p = 1) : d1727 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d1727, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39428 p hg
    simpa only [d8107, d1727, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d1727, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39429 p hg
    simpa only [d8107, d1727, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39431 (p : Pattern) (guard : d8106 p = 1) : d1731 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d1731, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35389 p hg
    simpa only [d8106, d1731, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d1731, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38569 p hg
    simpa only [d8106, d1731, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39432 (p : Pattern) (guard : d8112 p = 1) : d1733 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1733, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39431 p hg
    simpa only [d8112, d1733, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1733, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38906 p hg
    simpa only [d8112, d1733, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39433 (p : Pattern) (guard : d8113 p = 1) : d1734 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1734, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39430 p hg
    simpa only [d8113, d1734, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1734, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39432 p hg
    simpa only [d8113, d1734, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39434 (p : Pattern) (guard : d8119 p = 1) : d1738 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1738, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39433 p hg
    simpa only [d8119, d1738, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1738, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38912 p hg
    simpa only [d8119, d1738, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39435 (p : Pattern) (guard : d8120 p = 1) : d1855 p ≤ (0 : Int) + d437 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d1855, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39427 p hg
    simpa only [d8120, d1855, d437, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d1855, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39434 p hg
    simpa only [d8120, d1855, d437, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39436 (p : Pattern) (guard : d8095 p = 1) : d1689 p ≤ (0 : Int) + d334 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d1689, d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35412 p hg
    simpa only [d8095, d1689, d334, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d1689, d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39198 p hg
    simpa only [d8095, d1689, d334, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39437 (p : Pattern) (guard : d8089 p = 1) : d1685 p ≤ (0 : Int) + d330 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d1685, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35069 p hg
    simpa only [d8089, d1685, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d1685, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38631 p hg
    simpa only [d8089, d1685, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39438 (p : Pattern) (guard : d8094 p = 1) : d1686 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d1686, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39437 p hg
    simpa only [d8094, d1686, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d1686, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38884 p hg
    simpa only [d8094, d1686, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39439 (p : Pattern) (guard : d8100 p = 1) : d1687 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d1687, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39438 p hg
    simpa only [d8100, d1687, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d1687, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d1687, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39440 (p : Pattern) (guard : d8101 p = 1) : d1690 p ≤ (0 : Int) + d337 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d1690, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39436 p hg
    simpa only [d8101, d1690, d337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d1690, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39439 p hg
    simpa only [d8101, d1690, d337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39441 (p : Pattern) (guard : d8100 p = 1) : d32 p ≤ (0 : Int) + d367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d32, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35418 p hg
    simpa only [d8100, d32, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d32, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d32, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39442 (p : Pattern) (guard : d8106 p = 1) : d1747 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d1747, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39441 p hg
    simpa only [d8106, d1747, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d1747, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38920 p hg
    simpa only [d8106, d1747, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39443 (p : Pattern) (guard : d8107 p = 1) : d1856 p ≤ (0 : Int) + d415 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d1856, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39440 p hg
    simpa only [d8107, d1856, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d1856, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39442 p hg
    simpa only [d8107, d1856, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39444 (p : Pattern) (guard : d8100 p = 1) : d19 p ≤ (0 : Int) + d324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d19, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35424 p hg
    simpa only [d8100, d19, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d19, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d19, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39445 (p : Pattern) (guard : d8106 p = 1) : d1698 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d1698, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39444 p hg
    simpa only [d8106, d1698, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d1698, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38892 p hg
    simpa only [d8106, d1698, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39446 (p : Pattern) (guard : d8105 p = 1) : d25 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d25, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35430 p hg
    simpa only [d8105, d25, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d25, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d25, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39447 (p : Pattern) (guard : d8111 p = 1) : d1706 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d1706, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39446 p hg
    simpa only [d8111, d1706, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d1706, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15276 p hg
    simpa only [d8111, d1706, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39448 (p : Pattern) (guard : d8112 p = 1) : d1749 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1749, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39445 p hg
    simpa only [d8112, d1749, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1749, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39447 p hg
    simpa only [d8112, d1749, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39449 (p : Pattern) (guard : d8113 p = 1) : d1857 p ≤ (0 : Int) + d416 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1857, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39443 p hg
    simpa only [d8113, d1857, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1857, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39448 p hg
    simpa only [d8113, d1857, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39450 (p : Pattern) (guard : d8105 p = 1) : d59 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d59, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35438 p hg
    simpa only [d8105, d59, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d59, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d59, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39451 (p : Pattern) (guard : d8111 p = 1) : d1754 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d1754, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39450 p hg
    simpa only [d8111, d1754, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d1754, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15307 p hg
    simpa only [d8111, d1754, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39452 (p : Pattern) (guard : d8112 p = 1) : d1755 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1755, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39421 p hg
    simpa only [d8112, d1755, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1755, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39451 p hg
    simpa only [d8112, d1755, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39453 (p : Pattern) (guard : d8118 p = 1) : d1758 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1758, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39452 p hg
    simpa only [d8118, d1758, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1758, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38751 p hg
    simpa only [d8118, d1758, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39454 (p : Pattern) (guard : d8119 p = 1) : d1858 p ≤ (0 : Int) + d417 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1858, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39449 p hg
    simpa only [d8119, d1858, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1858, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39453 p hg
    simpa only [d8119, d1858, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39455 (p : Pattern) (guard : d8106 p = 1) : d1726 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d1726, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35586 p hg
    simpa only [d8106, d1726, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d1726, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38732 p hg
    simpa only [d8106, d1726, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39456 (p : Pattern) (guard : d8112 p = 1) : d1761 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1761, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39455 p hg
    simpa only [d8112, d1761, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1761, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38931 p hg
    simpa only [d8112, d1761, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39457 (p : Pattern) (guard : d8118 p = 1) : d1763 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1763, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39456 p hg
    simpa only [d8118, d1763, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1763, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38934 p hg
    simpa only [d8118, d1763, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39458 (p : Pattern) (guard : d8124 p = 1) : d1766 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1766, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39457 p hg
    simpa only [d8124, d1766, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1766, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38939 p hg
    simpa only [d8124, d1766, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39459 (p : Pattern) (guard : d8125 p = 1) : d1859 p ≤ (0 : Int) + d418 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d1859, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39454 p hg
    simpa only [d8125, d1859, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d1859, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39458 p hg
    simpa only [d8125, d1859, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39460 (p : Pattern) (guard : d8126 p = 1) : d1860 p ≤ (0 : Int) + d438 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d1860, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39435 p hg
    simpa only [d8126, d1860, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d1860, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39459 p hg
    simpa only [d8126, d1860, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39461 (p : Pattern) (guard : d8101 p = 1) : d1774 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d1774, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38915 p hg
    simpa only [d8101, d1774, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d1774, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38946 p hg
    simpa only [d8101, d1774, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39462 (p : Pattern) (guard : d8107 p = 1) : d1784 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d1784, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39461 p hg
    simpa only [d8107, d1784, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d1784, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39125 p hg
    simpa only [d8107, d1784, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39463 (p : Pattern) (guard : d8106 p = 1) : d1790 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d1790, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35414 p hg
    simpa only [d8106, d1790, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d1790, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38956 p hg
    simpa only [d8106, d1790, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39464 (p : Pattern) (guard : d8112 p = 1) : d1800 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1800, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39463 p hg
    simpa only [d8112, d1800, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1800, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38958 p hg
    simpa only [d8112, d1800, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39465 (p : Pattern) (guard : d8113 p = 1) : d1801 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1801, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39462 p hg
    simpa only [d8113, d1801, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1801, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39464 p hg
    simpa only [d8113, d1801, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39466 (p : Pattern) (guard : d8118 p = 1) : d1807 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1807, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39121 p hg
    simpa only [d8118, d1807, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1807, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38961 p hg
    simpa only [d8118, d1807, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39467 (p : Pattern) (guard : d8119 p = 1) : d1808 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1808, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39465 p hg
    simpa only [d8119, d1808, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1808, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39466 p hg
    simpa only [d8119, d1808, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39468 (p : Pattern) (guard : d8125 p = 1) : d1814 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d1814, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39467 p hg
    simpa only [d8125, d1814, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d1814, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38967 p hg
    simpa only [d8125, d1814, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39469 (p : Pattern) (guard : d8100 p = 1) : d15 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d15, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35464 p hg
    simpa only [d8100, d15, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d15, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d15, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39470 (p : Pattern) (guard : d8106 p = 1) : d1783 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d1783, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39469 p hg
    simpa only [d8106, d1783, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d1783, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38951 p hg
    simpa only [d8106, d1783, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39471 (p : Pattern) (guard : d8105 p = 1) : d32 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d32, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35470 p hg
    simpa only [d8105, d32, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d32, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d32, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39472 (p : Pattern) (guard : d8111 p = 1) : d1809 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d1809, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39471 p hg
    simpa only [d8111, d1809, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d1809, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15281 p hg
    simpa only [d8111, d1809, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39473 (p : Pattern) (guard : d8112 p = 1) : d1815 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1815, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39470 p hg
    simpa only [d8112, d1815, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1815, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39472 p hg
    simpa only [d8112, d1815, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39474 (p : Pattern) (guard : d8118 p = 1) : d1817 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1817, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39473 p hg
    simpa only [d8118, d1817, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1817, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38973 p hg
    simpa only [d8118, d1817, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39475 (p : Pattern) (guard : d8124 p = 1) : d1820 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1820, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39474 p hg
    simpa only [d8124, d1820, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1820, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38978 p hg
    simpa only [d8124, d1820, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39476 (p : Pattern) (guard : d8130 p = 1) : d1824 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d1824, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39475 p hg
    simpa only [d8130, d1824, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d1824, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38982 p hg
    simpa only [d8130, d1824, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39477 (p : Pattern) (guard : d8131 p = 1) : d1825 p ≤ (0 : Int) + d439 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d1825, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39468 p hg
    simpa only [d8131, d1825, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d1825, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39476 p hg
    simpa only [d8131, d1825, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39478 (p : Pattern) (guard : d8132 p = 1) : d1861 p ≤ (0 : Int) + d440 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d1861, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39460 p hg
    simpa only [d8132, d1861, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d1861, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39477 p hg
    simpa only [d8132, d1861, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39479 (p : Pattern) (guard : d8101 p = 1) : d1774 p ≤ (0 : Int) + d352 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d1774, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39099 p hg
    simpa only [d8101, d1774, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d1774, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38946 p hg
    simpa only [d8101, d1774, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
