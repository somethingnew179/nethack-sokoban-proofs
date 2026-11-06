/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons230
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare32340 (p : Pattern) (guard : d4474 p = 1) : d3010 p ≤ (2 : Int) + d7090 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3010, d7090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32327 p hg
    simpa only [d3010, d7090, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3010, d7090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32339 p hg
    simpa only [d3010, d7090, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32341 (p : Pattern) (guard : d4474 p = 1) : d3011 p ≤ (2 : Int) + d7084 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3011, d7084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32209 p hg
    simpa only [d3011, d7084, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3011, d7084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32127 p hg
    simpa only [d3011, d7084, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32342 (p : Pattern) (guard : d4474 p = 1) : d3012 p ≤ (2 : Int) + d7091 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3012, d7091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32339 p hg
    simpa only [d3012, d7091, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3012, d7091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32341 p hg
    simpa only [d3012, d7091, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32343 (p : Pattern) (guard : d4474 p = 1) : d3013 p ≤ (2 : Int) + d7092 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3013, d7092, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32340 p hg
    simpa only [d3013, d7092, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3013, d7092, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32342 p hg
    simpa only [d3013, d7092, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32344 (p : Pattern) (guard : d4474 p = 1) : d3014 p ≤ (2 : Int) + d7093 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3014, d7093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32315 p hg
    simpa only [d3014, d7093, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3014, d7093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32343 p hg
    simpa only [d3014, d7093, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32345 (p : Pattern) (guard : d1 p = 1) : d3 p ≤ (2 : Int) + d1894 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15951 p hg
    simpa only [d1894, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24795 p hg
    simpa only [d1894, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32346 (p : Pattern) (guard : d1 p = 1) : d116 p ≤ (2 : Int) + d1895 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d116, d1895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32345 p hg
    simpa only [d116, d1895, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d116, d1895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24796 p hg
    simpa only [d116, d1895, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32347 (p : Pattern) (guard : d1 p = 1) : d116 p ≤ (2 : Int) + d2124 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2186 p hg
    simpa only [d2124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32346 p hg
    simpa only [d2124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32348 (p : Pattern) (guard : d1 p = 1) : d116 p ≤ (2 : Int) + d2125 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32347 p hg
    simpa only [d2125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32346 p hg
    simpa only [d2125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32349 (p : Pattern) (guard : d0 p = 1) : d2125 p ≤ (2 : Int) + d2125 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare32350 (p : Pattern) (guard : d4474 p = 1) : d3015 p ≤ (2 : Int) + d2125 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d3015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32348 p hg
    simpa only [d4474, d3015, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d3015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32349 p hg
    simpa only [d4474, d3015, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32351 (p : Pattern) (guard : d1 p = 1) : d1918 p ≤ (2 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4893 p hg
    simpa only [d1918, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4785 p hg
    simpa only [d1918, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32352 (p : Pattern) (guard : d1 p = 1) : d1919 p ≤ (2 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32351 p hg
    simpa only [d1919, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4786 p hg
    simpa only [d1919, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32353 (p : Pattern) (guard : d1 p = 1) : d1920 p ≤ (2 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4895 p hg
    simpa only [d1920, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32352 p hg
    simpa only [d1920, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32354 (p : Pattern) (guard : d1 p = 1) : d1921 p ≤ (2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32353 p hg
    simpa only [d1921, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32352 p hg
    simpa only [d1921, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32355 (p : Pattern) (guard : d4474 p = 1) : d1922 p ≤ (2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d1922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32354 p hg
    simpa only [d4474, d1922, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d1922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6043 p hg
    simpa only [d4474, d1922, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32356 (p : Pattern) (guard : d4474 p = 1) : d3016 p ≤ (2 : Int) + d7094 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3016, d7094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32350 p hg
    simpa only [d3016, d7094, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3016, d7094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32355 p hg
    simpa only [d3016, d7094, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32357 (p : Pattern) (guard : d4474 p = 1) : d3017 p ≤ (2 : Int) + d7095 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3017, d7095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32298 p hg
    simpa only [d3017, d7095, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3017, d7095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32356 p hg
    simpa only [d3017, d7095, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32358 (p : Pattern) (guard : d4474 p = 1) : d3018 p ≤ (2 : Int) + d7096 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3018, d7096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32310 p hg
    simpa only [d3018, d7096, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3018, d7096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32184 p hg
    simpa only [d3018, d7096, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32359 (p : Pattern) (guard : d4474 p = 1) : d3019 p ≤ (2 : Int) + d7097 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3019, d7097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32357 p hg
    simpa only [d3019, d7097, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3019, d7097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32358 p hg
    simpa only [d3019, d7097, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32360 (p : Pattern) (guard : d4474 p = 1) : d3020 p ≤ (2 : Int) + d7098 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3020, d7098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32310 p hg
    simpa only [d3020, d7098, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3020, d7098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32192 p hg
    simpa only [d3020, d7098, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32361 (p : Pattern) (guard : d4474 p = 1) : d3021 p ≤ (2 : Int) + d7099 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3021, d7099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32360 p hg
    simpa only [d3021, d7099, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3021, d7099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32127 p hg
    simpa only [d3021, d7099, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32362 (p : Pattern) (guard : d4474 p = 1) : d3022 p ≤ (2 : Int) + d7100 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3022, d7100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32359 p hg
    simpa only [d3022, d7100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3022, d7100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32361 p hg
    simpa only [d3022, d7100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32363 (p : Pattern) (guard : d1 p = 1) : d3 p ≤ (2 : Int) + d1891 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15951 p hg
    simpa only [d1891, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16260 p hg
    simpa only [d1891, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32364 (p : Pattern) (guard : d1 p = 1) : d116 p ≤ (2 : Int) + d1892 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d116, d1892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32363 p hg
    simpa only [d116, d1892, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d116, d1892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16261 p hg
    simpa only [d116, d1892, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32365 (p : Pattern) (guard : d1 p = 1) : d116 p ≤ (2 : Int) + d1893 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2186 p hg
    simpa only [d1893, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32364 p hg
    simpa only [d1893, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32366 (p : Pattern) (guard : d1 p = 1) : d3 p ≤ (2 : Int) + d115 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15951 p hg
    simpa only [d115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4893 p hg
    simpa only [d115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32367 (p : Pattern) (guard : d1 p = 1) : d116 p ≤ (2 : Int) + d1896 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d116, d1896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32366 p hg
    simpa only [d116, d1896, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d116, d1896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4894 p hg
    simpa only [d116, d1896, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32368 (p : Pattern) (guard : d1 p = 1) : d116 p ≤ (2 : Int) + d1897 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32346 p hg
    simpa only [d1897, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32367 p hg
    simpa only [d1897, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32369 (p : Pattern) (guard : d1 p = 1) : d116 p ≤ (2 : Int) + d1898 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32365 p hg
    simpa only [d1898, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32368 p hg
    simpa only [d1898, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32370 (p : Pattern) (guard : d0 p = 1) : d1898 p ≤ (2 : Int) + d1898 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare32371 (p : Pattern) (guard : d4474 p = 1) : d3023 p ≤ (2 : Int) + d1898 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d3023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32369 p hg
    simpa only [d4474, d3023, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d3023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32370 p hg
    simpa only [d4474, d3023, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32372 (p : Pattern) (guard : d4474 p = 1) : d3024 p ≤ (2 : Int) + d7101 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3024, d7101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32371 p hg
    simpa only [d3024, d7101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3024, d7101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32127 p hg
    simpa only [d3024, d7101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32373 (p : Pattern) (guard : d4474 p = 1) : d3025 p ≤ (2 : Int) + d7102 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3025, d7102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32326 p hg
    simpa only [d3025, d7102, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3025, d7102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32372 p hg
    simpa only [d3025, d7102, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32374 (p : Pattern) (guard : d4474 p = 1) : d3026 p ≤ (2 : Int) + d7103 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3026, d7103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32338 p hg
    simpa only [d3026, d7103, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3026, d7103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32209 p hg
    simpa only [d3026, d7103, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32375 (p : Pattern) (guard : d4474 p = 1) : d3027 p ≤ (2 : Int) + d7104 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3027, d7104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32373 p hg
    simpa only [d3027, d7104, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3027, d7104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32374 p hg
    simpa only [d3027, d7104, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32376 (p : Pattern) (guard : d4474 p = 1) : d3028 p ≤ (2 : Int) + d7105 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3028, d7105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32338 p hg
    simpa only [d3028, d7105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3028, d7105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32211 p hg
    simpa only [d3028, d7105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32377 (p : Pattern) (guard : d4474 p = 1) : d3029 p ≤ (2 : Int) + d7106 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3029, d7106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32376 p hg
    simpa only [d3029, d7106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3029, d7106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32127 p hg
    simpa only [d3029, d7106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32378 (p : Pattern) (guard : d4474 p = 1) : d3030 p ≤ (2 : Int) + d7107 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3030, d7107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32375 p hg
    simpa only [d3030, d7107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3030, d7107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32377 p hg
    simpa only [d3030, d7107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32379 (p : Pattern) (guard : d4474 p = 1) : d3031 p ≤ (2 : Int) + d7108 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3031, d7108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32362 p hg
    simpa only [d3031, d7108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3031, d7108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32378 p hg
    simpa only [d3031, d7108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32380 (p : Pattern) (guard : d4474 p = 1) : d3032 p ≤ (2 : Int) + d7109 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3032, d7109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32344 p hg
    simpa only [d3032, d7109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3032, d7109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32379 p hg
    simpa only [d3032, d7109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32381 (p : Pattern) (guard : d1 p = 1) : d103 p ≤ (2 : Int) + d2107 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32288 p hg
    simpa only [d2107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32317 p hg
    simpa only [d2107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32382 (p : Pattern) (guard : d1 p = 1) : d103 p ≤ (2 : Int) + d2108 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32318 p hg
    simpa only [d2108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32381 p hg
    simpa only [d2108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32383 (p : Pattern) (guard : d0 p = 1) : d2108 p ≤ (2 : Int) + d2108 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare32384 (p : Pattern) (guard : d4474 p = 1) : d3033 p ≤ (2 : Int) + d2108 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d3033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32382 p hg
    simpa only [d4474, d3033, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d3033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32383 p hg
    simpa only [d4474, d3033, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32385 (p : Pattern) (guard : d1 p = 1) : d1941 p ≤ (2 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15999 p hg
    simpa only [d1941, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16004 p hg
    simpa only [d1941, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32386 (p : Pattern) (guard : d1 p = 1) : d1942 p ≤ (2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32385 p hg
    simpa only [d1942, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16004 p hg
    simpa only [d1942, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32387 (p : Pattern) (guard : d4474 p = 1) : d1943 p ≤ (2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d1943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32386 p hg
    simpa only [d4474, d1943, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d1943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6043 p hg
    simpa only [d4474, d1943, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32388 (p : Pattern) (guard : d4474 p = 1) : d3034 p ≤ (2 : Int) + d7110 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3034, d7110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32384 p hg
    simpa only [d3034, d7110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3034, d7110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32387 p hg
    simpa only [d3034, d7110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32389 (p : Pattern) (guard : d1 p = 1) : d1 p ≤ (2 : Int) + d3035 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d3035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15921 p hg
    simpa only [d3035, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d3035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16295 p hg
    simpa only [d3035, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32390 (p : Pattern) (guard : d1 p = 1) : d103 p ≤ (2 : Int) + d3036 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d103, d3036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32389 p hg
    simpa only [d103, d3036, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d103, d3036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4782 p hg
    simpa only [d103, d3036, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32391 (p : Pattern) (guard : d1 p = 1) : d103 p ≤ (2 : Int) + d3037 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d3037, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32288 p hg
    simpa only [d3037, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d3037, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32390 p hg
    simpa only [d3037, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32392 (p : Pattern) (guard : d1 p = 1) : d103 p ≤ (2 : Int) + d3038 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d3038, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32318 p hg
    simpa only [d3038, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d3038, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32391 p hg
    simpa only [d3038, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32393 (p : Pattern) (guard : d0 p = 1) : d3038 p ≤ (2 : Int) + d3038 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare32394 (p : Pattern) (guard : d4474 p = 1) : d3039 p ≤ (2 : Int) + d3038 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d3039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32392 p hg
    simpa only [d4474, d3039, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d3039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32393 p hg
    simpa only [d4474, d3039, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32395 (p : Pattern) (guard : d1 p = 1) : d1948 p ≤ (2 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15997 p hg
    simpa only [d1948, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1822 p hg
    simpa only [d1948, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32396 (p : Pattern) (guard : d1 p = 1) : d1949 p ≤ (2 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32395 p hg
    simpa only [d1949, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1823 p hg
    simpa only [d1949, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32397 (p : Pattern) (guard : d1 p = 1) : d1950 p ≤ (2 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16004 p hg
    simpa only [d1950, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32396 p hg
    simpa only [d1950, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32398 (p : Pattern) (guard : d1 p = 1) : d1951 p ≤ (2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16002 p hg
    simpa only [d1951, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32397 p hg
    simpa only [d1951, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32399 (p : Pattern) (guard : d4474 p = 1) : d1952 p ≤ (2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d1952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32398 p hg
    simpa only [d4474, d1952, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d1952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6043 p hg
    simpa only [d4474, d1952, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32400 (p : Pattern) (guard : d4474 p = 1) : d3040 p ≤ (2 : Int) + d7111 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3040, d7111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32394 p hg
    simpa only [d3040, d7111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3040, d7111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32399 p hg
    simpa only [d3040, d7111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32401 (p : Pattern) (guard : d4474 p = 1) : d3041 p ≤ (2 : Int) + d7112 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3041, d7112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32388 p hg
    simpa only [d3041, d7112, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3041, d7112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32400 p hg
    simpa only [d3041, d7112, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32402 (p : Pattern) (guard : d4474 p = 1) : d3042 p ≤ (2 : Int) + d7087 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3042, d7087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32324 p hg
    simpa only [d3042, d7087, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3042, d7087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16008 p hg
    simpa only [d3042, d7087, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32403 (p : Pattern) (guard : d4474 p = 1) : d3043 p ≤ (2 : Int) + d7088 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3043, d7088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32337 p hg
    simpa only [d3043, d7088, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3043, d7088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16019 p hg
    simpa only [d3043, d7088, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32404 (p : Pattern) (guard : d4474 p = 1) : d3044 p ≤ (2 : Int) + d7089 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3044, d7089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32402 p hg
    simpa only [d3044, d7089, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3044, d7089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32403 p hg
    simpa only [d3044, d7089, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32405 (p : Pattern) (guard : d4474 p = 1) : d3045 p ≤ (2 : Int) + d7113 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3045, d7113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32401 p hg
    simpa only [d3045, d7113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3045, d7113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32404 p hg
    simpa only [d3045, d7113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32406 (p : Pattern) (guard : d4474 p = 1) : d3046 p ≤ (2 : Int) + d7091 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3046, d7091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32404 p hg
    simpa only [d3046, d7091, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3046, d7091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32313 p hg
    simpa only [d3046, d7091, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32407 (p : Pattern) (guard : d4474 p = 1) : d3047 p ≤ (2 : Int) + d7114 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3047, d7114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32405 p hg
    simpa only [d3047, d7114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3047, d7114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32406 p hg
    simpa only [d3047, d7114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32408 (p : Pattern) (guard : d4474 p = 1) : d3048 p ≤ (2 : Int) + d7101 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3048, d7101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32371 p hg
    simpa only [d3048, d7101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3048, d7101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16037 p hg
    simpa only [d3048, d7101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32409 (p : Pattern) (guard : d1 p = 1) : d7 p ≤ (2 : Int) + d119 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15979 p hg
    simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4929 p hg
    simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32410 (p : Pattern) (guard : d1 p = 1) : d120 p ≤ (2 : Int) + d317 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d120, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32409 p hg
    simpa only [d120, d317, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d120, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4930 p hg
    simpa only [d120, d317, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32411 (p : Pattern) (guard : d1 p = 1) : d120 p ≤ (2 : Int) + d1901 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13358 p hg
    simpa only [d1901, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32410 p hg
    simpa only [d1901, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32412 (p : Pattern) (guard : d1 p = 1) : d7 p ≤ (2 : Int) + d1902 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15979 p hg
    simpa only [d1902, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16298 p hg
    simpa only [d1902, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32413 (p : Pattern) (guard : d1 p = 1) : d120 p ≤ (2 : Int) + d1903 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d120, d1903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32412 p hg
    simpa only [d120, d1903, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d120, d1903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16300 p hg
    simpa only [d120, d1903, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32414 (p : Pattern) (guard : d1 p = 1) : d120 p ≤ (2 : Int) + d1904 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32413 p hg
    simpa only [d1904, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32410 p hg
    simpa only [d1904, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32415 (p : Pattern) (guard : d1 p = 1) : d120 p ≤ (2 : Int) + d1905 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32411 p hg
    simpa only [d1905, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32414 p hg
    simpa only [d1905, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32416 (p : Pattern) (guard : d0 p = 1) : d1905 p ≤ (2 : Int) + d1905 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare32417 (p : Pattern) (guard : d4474 p = 1) : d3049 p ≤ (2 : Int) + d1905 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d3049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32415 p hg
    simpa only [d4474, d3049, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d3049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32416 p hg
    simpa only [d4474, d3049, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32418 (p : Pattern) (guard : d4474 p = 1) : d3050 p ≤ (2 : Int) + d7115 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3050, d7115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32417 p hg
    simpa only [d3050, d7115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3050, d7115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16285 p hg
    simpa only [d3050, d7115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32419 (p : Pattern) (guard : d4474 p = 1) : d3051 p ≤ (2 : Int) + d7116 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3051, d7116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32408 p hg
    simpa only [d3051, d7116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3051, d7116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32418 p hg
    simpa only [d3051, d7116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32420 (p : Pattern) (guard : d4474 p = 1) : d3052 p ≤ (2 : Int) + d7117 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3052, d7117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32419 p hg
    simpa only [d3052, d7117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3052, d7117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32127 p hg
    simpa only [d3052, d7117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32421 (p : Pattern) (guard : d4474 p = 1) : d3053 p ≤ (2 : Int) + d7118 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3053, d7118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32420 p hg
    simpa only [d3053, d7118, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3053, d7118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32127 p hg
    simpa only [d3053, d7118, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32422 (p : Pattern) (guard : d4474 p = 1) : d3054 p ≤ (2 : Int) + d7119 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3054, d7119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32407 p hg
    simpa only [d3054, d7119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3054, d7119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32421 p hg
    simpa only [d3054, d7119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32423 (p : Pattern) (guard : d4474 p = 1) : d3055 p ≤ (2 : Int) + d7120 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3055, d7120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32400 p hg
    simpa only [d3055, d7120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3055, d7120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32408 p hg
    simpa only [d3055, d7120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32424 (p : Pattern) (guard : d4474 p = 1) : d3056 p ≤ (2 : Int) + d7103 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3056, d7103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32403 p hg
    simpa only [d3056, d7103, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3056, d7103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32184 p hg
    simpa only [d3056, d7103, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32425 (p : Pattern) (guard : d4474 p = 1) : d3057 p ≤ (2 : Int) + d7121 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3057, d7121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32423 p hg
    simpa only [d3057, d7121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3057, d7121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32424 p hg
    simpa only [d3057, d7121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32426 (p : Pattern) (guard : d4474 p = 1) : d3058 p ≤ (2 : Int) + d7105 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3058, d7105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32403 p hg
    simpa only [d3058, d7105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3058, d7105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32192 p hg
    simpa only [d3058, d7105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32427 (p : Pattern) (guard : d4474 p = 1) : d3059 p ≤ (2 : Int) + d7106 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3059, d7106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32426 p hg
    simpa only [d3059, d7106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3059, d7106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32127 p hg
    simpa only [d3059, d7106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32428 (p : Pattern) (guard : d4474 p = 1) : d3060 p ≤ (2 : Int) + d7122 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3060, d7122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32425 p hg
    simpa only [d3060, d7122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3060, d7122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32427 p hg
    simpa only [d3060, d7122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32429 (p : Pattern) (guard : d4474 p = 1) : d3061 p ≤ (2 : Int) + d7123 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3061, d7123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32418 p hg
    simpa only [d3061, d7123, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3061, d7123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32127 p hg
    simpa only [d3061, d7123, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32430 (p : Pattern) (guard : d4474 p = 1) : d3062 p ≤ (2 : Int) + d7124 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3062, d7124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32429 p hg
    simpa only [d3062, d7124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3062, d7124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32127 p hg
    simpa only [d3062, d7124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32431 (p : Pattern) (guard : d4474 p = 1) : d3063 p ≤ (2 : Int) + d7125 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3063, d7125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32430 p hg
    simpa only [d3063, d7125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3063, d7125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32127 p hg
    simpa only [d3063, d7125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32432 (p : Pattern) (guard : d4474 p = 1) : d3064 p ≤ (2 : Int) + d7126 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3064, d7126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32428 p hg
    simpa only [d3064, d7126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3064, d7126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32431 p hg
    simpa only [d3064, d7126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32433 (p : Pattern) (guard : d4474 p = 1) : d3065 p ≤ (2 : Int) + d7127 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3065, d7127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32422 p hg
    simpa only [d3065, d7127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3065, d7127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32432 p hg
    simpa only [d3065, d7127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32434 (p : Pattern) (guard : d4474 p = 1) : d3066 p ≤ (2 : Int) + d7128 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3066, d7128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32380 p hg
    simpa only [d3066, d7128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3066, d7128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32433 p hg
    simpa only [d3066, d7128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32435 (p : Pattern) (guard : d4474 p = 1) : d3067 p ≤ (2 : Int) + d7129 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3067, d7129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32313 p hg
    simpa only [d3067, d7129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3067, d7129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32127 p hg
    simpa only [d3067, d7129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32436 (p : Pattern) (guard : d4474 p = 1) : d3068 p ≤ (2 : Int) + d7130 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3068, d7130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32435 p hg
    simpa only [d3068, d7130, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3068, d7130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32127 p hg
    simpa only [d3068, d7130, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32437 (p : Pattern) (guard : d4474 p = 1) : d3069 p ≤ (2 : Int) + d7131 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3069, d7131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32436 p hg
    simpa only [d3069, d7131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3069, d7131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32127 p hg
    simpa only [d3069, d7131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32438 (p : Pattern) (guard : d4474 p = 1) : d3070 p ≤ (2 : Int) + d7132 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3070, d7132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32437 p hg
    simpa only [d3070, d7132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3070, d7132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32127 p hg
    simpa only [d3070, d7132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32439 (p : Pattern) (guard : d4474 p = 1) : d3071 p ≤ (2 : Int) + d7133 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3071, d7133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32433 p hg
    simpa only [d3071, d7133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3071, d7133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32438 p hg
    simpa only [d3071, d7133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32440 (p : Pattern) (guard : d4474 p = 1) : d3072 p ≤ (2 : Int) + d7134 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3072, d7134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32434 p hg
    simpa only [d3072, d7134, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3072, d7134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32439 p hg
    simpa only [d3072, d7134, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32441 (p : Pattern) (guard : d4474 p = 1) : d3073 p ≤ (2 : Int) + d7135 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3073, d7135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32433 p hg
    simpa only [d3073, d7135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3073, d7135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32127 p hg
    simpa only [d3073, d7135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32442 (p : Pattern) (guard : d4474 p = 1) : d3074 p ≤ (2 : Int) + d7136 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3074, d7136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32434 p hg
    simpa only [d3074, d7136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3074, d7136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32441 p hg
    simpa only [d3074, d7136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32443 (p : Pattern) (guard : d4474 p = 1) : d3075 p ≤ (2 : Int) + d7137 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3075, d7137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32440 p hg
    simpa only [d3075, d7137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3075, d7137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32442 p hg
    simpa only [d3075, d7137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32444 (p : Pattern) (guard : d4474 p = 1) : d3076 p ≤ (2 : Int) + d7138 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3076, d7138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32286 p hg
    simpa only [d3076, d7138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3076, d7138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32443 p hg
    simpa only [d3076, d7138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32445 (p : Pattern) (guard : d4474 p = 1) : d3077 p ≤ (2 : Int) + d7139 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3077, d7139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32286 p hg
    simpa only [d3077, d7139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3077, d7139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32444 p hg
    simpa only [d3077, d7139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32446 (p : Pattern) (guard : d1 p = 1) : d18 p ≤ (2 : Int) + d3078 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d3078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32102 p hg
    simpa only [d3078, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d3078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32145 p hg
    simpa only [d3078, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32447 (p : Pattern) (guard : d1 p = 1) : d18 p ≤ (2 : Int) + d3079 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d3079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32146 p hg
    simpa only [d3079, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d3079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32446 p hg
    simpa only [d3079, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32448 (p : Pattern) (guard : d0 p = 1) : d3079 p ≤ (2 : Int) + d3079 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare32449 (p : Pattern) (guard : d4474 p = 1) : d3080 p ≤ (2 : Int) + d3079 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d3080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32447 p hg
    simpa only [d4474, d3080, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d3080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32448 p hg
    simpa only [d4474, d3080, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32450 (p : Pattern) (guard : d1 p = 1) : d2011 p ≤ (2 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4713 p hg
    simpa only [d2011, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15797 p hg
    simpa only [d2011, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32451 (p : Pattern) (guard : d1 p = 1) : d2012 p ≤ (2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32450 p hg
    simpa only [d2012, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15797 p hg
    simpa only [d2012, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32452 (p : Pattern) (guard : d4474 p = 1) : d2013 p ≤ (2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d2013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32451 p hg
    simpa only [d4474, d2013, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d2013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6043 p hg
    simpa only [d4474, d2013, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32453 (p : Pattern) (guard : d4474 p = 1) : d3081 p ≤ (2 : Int) + d7140 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3081, d7140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32449 p hg
    simpa only [d3081, d7140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3081, d7140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32452 p hg
    simpa only [d3081, d7140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32454 (p : Pattern) (guard : d4474 p = 1) : d3082 p ≤ (2 : Int) + d7141 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3082, d7141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32224 p hg
    simpa only [d3082, d7141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3082, d7141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32453 p hg
    simpa only [d3082, d7141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32455 (p : Pattern) (guard : d4474 p = 1) : d3083 p ≤ (2 : Int) + d7142 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3083, d7142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32224 p hg
    simpa only [d3083, d7142, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3083, d7142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32454 p hg
    simpa only [d3083, d7142, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32456 (p : Pattern) (guard : d4474 p = 1) : d3084 p ≤ (2 : Int) + d7143 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3084, d7143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32454 p hg
    simpa only [d3084, d7143, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3084, d7143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32244 p hg
    simpa only [d3084, d7143, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32457 (p : Pattern) (guard : d4474 p = 1) : d3085 p ≤ (2 : Int) + d7144 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3085, d7144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32455 p hg
    simpa only [d3085, d7144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3085, d7144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32456 p hg
    simpa only [d3085, d7144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32458 (p : Pattern) (guard : d4474 p = 1) : d3086 p ≤ (2 : Int) + d7039 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3086, d7039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32204 p hg
    simpa only [d3086, d7039, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3086, d7039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16142 p hg
    simpa only [d3086, d7039, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32459 (p : Pattern) (guard : d4474 p = 1) : d3087 p ≤ (2 : Int) + d7039 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32247 p hg
    simpa only [d3087, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32458 p hg
    simpa only [d3087, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32460 (p : Pattern) (guard : d4474 p = 1) : d3088 p ≤ (2 : Int) + d7039 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3088, d7039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32204 p hg
    simpa only [d3088, d7039, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3088, d7039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15857 p hg
    simpa only [d3088, d7039, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32461 (p : Pattern) (guard : d4474 p = 1) : d3089 p ≤ (2 : Int) + d7053 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3089, d7053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32256 p hg
    simpa only [d3089, d7053, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3089, d7053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32127 p hg
    simpa only [d3089, d7053, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32462 (p : Pattern) (guard : d4474 p = 1) : d3090 p ≤ (2 : Int) + d7054 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3090, d7054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32460 p hg
    simpa only [d3090, d7054, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3090, d7054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32461 p hg
    simpa only [d3090, d7054, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32463 (p : Pattern) (guard : d4474 p = 1) : d3091 p ≤ (2 : Int) + d7145 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3091, d7145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32459 p hg
    simpa only [d3091, d7145, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3091, d7145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32462 p hg
    simpa only [d3091, d7145, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32464 (p : Pattern) (guard : d4474 p = 1) : d3092 p ≤ (2 : Int) + d7054 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3092, d7054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32205 p hg
    simpa only [d3092, d7054, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3092, d7054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32461 p hg
    simpa only [d3092, d7054, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32465 (p : Pattern) (guard : d4474 p = 1) : d3093 p ≤ (2 : Int) + d7055 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3093, d7055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32464 p hg
    simpa only [d3093, d7055, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3093, d7055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32212 p hg
    simpa only [d3093, d7055, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32466 (p : Pattern) (guard : d4474 p = 1) : d3094 p ≤ (2 : Int) + d7146 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3094, d7146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32463 p hg
    simpa only [d3094, d7146, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3094, d7146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32465 p hg
    simpa only [d3094, d7146, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32467 (p : Pattern) (guard : d4474 p = 1) : d3095 p ≤ (2 : Int) + d7147 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3095, d7147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32457 p hg
    simpa only [d3095, d7147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3095, d7147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32466 p hg
    simpa only [d3095, d7147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32468 (p : Pattern) (guard : d1 p = 1) : d31 p ≤ (2 : Int) + d3096 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d3096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32164 p hg
    simpa only [d3096, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d3096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32197 p hg
    simpa only [d3096, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32469 (p : Pattern) (guard : d1 p = 1) : d31 p ≤ (2 : Int) + d3097 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d3097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32198 p hg
    simpa only [d3097, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d3097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32468 p hg
    simpa only [d3097, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32470 (p : Pattern) (guard : d0 p = 1) : d3097 p ≤ (2 : Int) + d3097 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare32471 (p : Pattern) (guard : d4474 p = 1) : d3098 p ≤ (2 : Int) + d3097 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d3098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32469 p hg
    simpa only [d4474, d3098, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d3098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32470 p hg
    simpa only [d4474, d3098, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32472 (p : Pattern) (guard : d1 p = 1) : d2029 p ≤ (2 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12153 p hg
    simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15837 p hg
    simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32473 (p : Pattern) (guard : d1 p = 1) : d2030 p ≤ (2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32472 p hg
    simpa only [d2030, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15837 p hg
    simpa only [d2030, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32474 (p : Pattern) (guard : d4474 p = 1) : d2031 p ≤ (2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d2031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32473 p hg
    simpa only [d4474, d2031, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d2031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6043 p hg
    simpa only [d4474, d2031, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32475 (p : Pattern) (guard : d4474 p = 1) : d3099 p ≤ (2 : Int) + d7148 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3099, d7148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32471 p hg
    simpa only [d3099, d7148, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3099, d7148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32474 p hg
    simpa only [d3099, d7148, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32476 (p : Pattern) (guard : d4474 p = 1) : d3100 p ≤ (2 : Int) + d7149 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3100, d7149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32224 p hg
    simpa only [d3100, d7149, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3100, d7149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32475 p hg
    simpa only [d3100, d7149, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32477 (p : Pattern) (guard : d4474 p = 1) : d3101 p ≤ (2 : Int) + d7150 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3101, d7150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32453 p hg
    simpa only [d3101, d7150, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3101, d7150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32243 p hg
    simpa only [d3101, d7150, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32478 (p : Pattern) (guard : d4474 p = 1) : d3102 p ≤ (2 : Int) + d7151 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3102, d7151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32476 p hg
    simpa only [d3102, d7151, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3102, d7151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32477 p hg
    simpa only [d3102, d7151, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32479 (p : Pattern) (guard : d4474 p = 1) : d3103 p ≤ (2 : Int) + d7152 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3103, d7152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32453 p hg
    simpa only [d3103, d7152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3103, d7152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32184 p hg
    simpa only [d3103, d7152, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
