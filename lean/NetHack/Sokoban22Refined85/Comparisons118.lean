/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons117
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare16520 (p : Pattern) (guard : d4474 p = 1) : d1926 p ≤ (0 : Int) + d3019 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1926, d3019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16518 p hg
    simpa only [d1926, d3019, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1926, d3019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16519 p hg
    simpa only [d1926, d3019, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16521 (p : Pattern) (guard : d4474 p = 1) : d1927 p ≤ (0 : Int) + d3020 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1927, d3020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16491 p hg
    simpa only [d1927, d3020, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1927, d3020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16383 p hg
    simpa only [d1927, d3020, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16522 (p : Pattern) (guard : d4474 p = 1) : d1928 p ≤ (0 : Int) + d3021 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1928, d3021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16521 p hg
    simpa only [d1928, d3021, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1928, d3021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d1928, d3021, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16523 (p : Pattern) (guard : d4474 p = 1) : d1929 p ≤ (0 : Int) + d3022 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1929, d3022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16520 p hg
    simpa only [d1929, d3022, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1929, d3022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16522 p hg
    simpa only [d1929, d3022, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16524 (p : Pattern) (guard : d4474 p = 1) : d117 p ≤ (0 : Int) + d3023 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d117, d3023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d4474, d117, d3023, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d117, d3023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12874 p hg
    simpa only [d4474, d117, d3023, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16525 (p : Pattern) (guard : d4474 p = 1) : d1930 p ≤ (0 : Int) + d3024 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1930, d3024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16524 p hg
    simpa only [d1930, d3024, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1930, d3024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d1930, d3024, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16526 (p : Pattern) (guard : d4474 p = 1) : d1931 p ≤ (0 : Int) + d3025 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1931, d3025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16501 p hg
    simpa only [d1931, d3025, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1931, d3025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16525 p hg
    simpa only [d1931, d3025, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16527 (p : Pattern) (guard : d4474 p = 1) : d1932 p ≤ (0 : Int) + d3026 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1932, d3026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16505 p hg
    simpa only [d1932, d3026, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1932, d3026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16392 p hg
    simpa only [d1932, d3026, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16528 (p : Pattern) (guard : d4474 p = 1) : d1933 p ≤ (0 : Int) + d3027 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1933, d3027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16526 p hg
    simpa only [d1933, d3027, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1933, d3027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16527 p hg
    simpa only [d1933, d3027, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16529 (p : Pattern) (guard : d4474 p = 1) : d1934 p ≤ (0 : Int) + d3028 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1934, d3028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16505 p hg
    simpa only [d1934, d3028, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1934, d3028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16394 p hg
    simpa only [d1934, d3028, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16530 (p : Pattern) (guard : d4474 p = 1) : d1935 p ≤ (0 : Int) + d3029 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1935, d3029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16529 p hg
    simpa only [d1935, d3029, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1935, d3029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d1935, d3029, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16531 (p : Pattern) (guard : d4474 p = 1) : d1936 p ≤ (0 : Int) + d3030 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1936, d3030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16528 p hg
    simpa only [d1936, d3030, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1936, d3030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16530 p hg
    simpa only [d1936, d3030, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16532 (p : Pattern) (guard : d4474 p = 1) : d1937 p ≤ (0 : Int) + d3031 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1937, d3031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16523 p hg
    simpa only [d1937, d3031, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1937, d3031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16531 p hg
    simpa only [d1937, d3031, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16533 (p : Pattern) (guard : d4474 p = 1) : d1938 p ≤ (0 : Int) + d3032 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1938, d3032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16511 p hg
    simpa only [d1938, d3032, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1938, d3032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16532 p hg
    simpa only [d1938, d3032, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16534 (p : Pattern) (guard : d4474 p = 1) : d104 p ≤ (0 : Int) + d3033 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d104, d3033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1274 p hg
    simpa only [d4474, d104, d3033, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d104, d3033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13039 p hg
    simpa only [d4474, d104, d3033, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16535 (p : Pattern) (guard : d4474 p = 1) : d1943 p ≤ (0 : Int) + d1943 p := by
  omega
theorem compare16536 (p : Pattern) (guard : d4474 p = 1) : d1944 p ≤ (0 : Int) + d3034 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1944, d3034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16534 p hg
    simpa only [d1944, d3034, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1944, d3034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16535 p hg
    simpa only [d1944, d3034, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16537 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d3038 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare16538 (p : Pattern) (guard : d4474 p = 1) : d104 p ≤ (0 : Int) + d3039 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d104, d3039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1274 p hg
    simpa only [d4474, d104, d3039, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d104, d3039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16537 p hg
    simpa only [d4474, d104, d3039, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16539 (p : Pattern) (guard : d4474 p = 1) : d1952 p ≤ (0 : Int) + d1952 p := by
  omega
theorem compare16540 (p : Pattern) (guard : d4474 p = 1) : d1953 p ≤ (0 : Int) + d3040 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1953, d3040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16538 p hg
    simpa only [d1953, d3040, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1953, d3040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16539 p hg
    simpa only [d1953, d3040, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16541 (p : Pattern) (guard : d4474 p = 1) : d1954 p ≤ (0 : Int) + d3041 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1954, d3041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16536 p hg
    simpa only [d1954, d3041, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1954, d3041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16540 p hg
    simpa only [d1954, d3041, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16542 (p : Pattern) (guard : d4474 p = 1) : d1958 p ≤ (0 : Int) + d1958 p := by
  omega
theorem compare16543 (p : Pattern) (guard : d4474 p = 1) : d1959 p ≤ (0 : Int) + d3042 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1959, d3042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16497 p hg
    simpa only [d1959, d3042, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1959, d3042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16542 p hg
    simpa only [d1959, d3042, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16544 (p : Pattern) (guard : d4474 p = 1) : d1967 p ≤ (0 : Int) + d1967 p := by
  omega
theorem compare16545 (p : Pattern) (guard : d4474 p = 1) : d1968 p ≤ (0 : Int) + d3043 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1968, d3043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16504 p hg
    simpa only [d1968, d3043, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1968, d3043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16544 p hg
    simpa only [d1968, d3043, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16546 (p : Pattern) (guard : d4474 p = 1) : d1969 p ≤ (0 : Int) + d3044 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1969, d3044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16543 p hg
    simpa only [d1969, d3044, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1969, d3044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16545 p hg
    simpa only [d1969, d3044, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16547 (p : Pattern) (guard : d4474 p = 1) : d1970 p ≤ (0 : Int) + d3045 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1970, d3045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16541 p hg
    simpa only [d1970, d3045, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1970, d3045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16546 p hg
    simpa only [d1970, d3045, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16548 (p : Pattern) (guard : d4474 p = 1) : d1971 p ≤ (0 : Int) + d3046 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1971, d3046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16546 p hg
    simpa only [d1971, d3046, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1971, d3046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16494 p hg
    simpa only [d1971, d3046, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16549 (p : Pattern) (guard : d4474 p = 1) : d1972 p ≤ (0 : Int) + d3047 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1972, d3047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16547 p hg
    simpa only [d1972, d3047, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1972, d3047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16548 p hg
    simpa only [d1972, d3047, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16550 (p : Pattern) (guard : d4474 p = 1) : d1973 p ≤ (0 : Int) + d3048 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1973, d3048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16524 p hg
    simpa only [d1973, d3048, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1973, d3048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16498 p hg
    simpa only [d1973, d3048, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16551 (p : Pattern) (guard : d4474 p = 1) : d121 p ≤ (0 : Int) + d3049 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d121, d3049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3159 p hg
    simpa only [d4474, d121, d3049, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d121, d3049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12876 p hg
    simpa only [d4474, d121, d3049, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16552 (p : Pattern) (guard : d4474 p = 1) : d1974 p ≤ (0 : Int) + d3050 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1974, d3050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16551 p hg
    simpa only [d1974, d3050, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1974, d3050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16500 p hg
    simpa only [d1974, d3050, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16553 (p : Pattern) (guard : d4474 p = 1) : d1975 p ≤ (0 : Int) + d3051 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1975, d3051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16550 p hg
    simpa only [d1975, d3051, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1975, d3051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16552 p hg
    simpa only [d1975, d3051, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16554 (p : Pattern) (guard : d4474 p = 1) : d1976 p ≤ (0 : Int) + d3052 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1976, d3052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16553 p hg
    simpa only [d1976, d3052, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1976, d3052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d1976, d3052, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16555 (p : Pattern) (guard : d4474 p = 1) : d1977 p ≤ (0 : Int) + d3053 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1977, d3053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16554 p hg
    simpa only [d1977, d3053, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1977, d3053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d1977, d3053, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16556 (p : Pattern) (guard : d4474 p = 1) : d1978 p ≤ (0 : Int) + d3054 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1978, d3054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16549 p hg
    simpa only [d1978, d3054, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1978, d3054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16555 p hg
    simpa only [d1978, d3054, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16557 (p : Pattern) (guard : d4474 p = 1) : d1979 p ≤ (0 : Int) + d3055 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1979, d3055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16540 p hg
    simpa only [d1979, d3055, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1979, d3055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16550 p hg
    simpa only [d1979, d3055, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16558 (p : Pattern) (guard : d4474 p = 1) : d1980 p ≤ (0 : Int) + d3056 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1980, d3056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16545 p hg
    simpa only [d1980, d3056, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1980, d3056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16380 p hg
    simpa only [d1980, d3056, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16559 (p : Pattern) (guard : d4474 p = 1) : d1981 p ≤ (0 : Int) + d3057 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1981, d3057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16557 p hg
    simpa only [d1981, d3057, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1981, d3057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16558 p hg
    simpa only [d1981, d3057, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16560 (p : Pattern) (guard : d4474 p = 1) : d1982 p ≤ (0 : Int) + d3058 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1982, d3058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16545 p hg
    simpa only [d1982, d3058, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1982, d3058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16383 p hg
    simpa only [d1982, d3058, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16561 (p : Pattern) (guard : d4474 p = 1) : d1983 p ≤ (0 : Int) + d3059 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1983, d3059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16560 p hg
    simpa only [d1983, d3059, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1983, d3059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d1983, d3059, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16562 (p : Pattern) (guard : d4474 p = 1) : d1984 p ≤ (0 : Int) + d3060 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1984, d3060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16559 p hg
    simpa only [d1984, d3060, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1984, d3060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16561 p hg
    simpa only [d1984, d3060, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16563 (p : Pattern) (guard : d4474 p = 1) : d1985 p ≤ (0 : Int) + d3061 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1985, d3061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16552 p hg
    simpa only [d1985, d3061, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1985, d3061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d1985, d3061, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16564 (p : Pattern) (guard : d4474 p = 1) : d1986 p ≤ (0 : Int) + d3062 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1986, d3062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16563 p hg
    simpa only [d1986, d3062, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1986, d3062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d1986, d3062, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16565 (p : Pattern) (guard : d4474 p = 1) : d1987 p ≤ (0 : Int) + d3063 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1987, d3063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16564 p hg
    simpa only [d1987, d3063, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1987, d3063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d1987, d3063, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16566 (p : Pattern) (guard : d4474 p = 1) : d1988 p ≤ (0 : Int) + d3064 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1988, d3064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16562 p hg
    simpa only [d1988, d3064, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1988, d3064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16565 p hg
    simpa only [d1988, d3064, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16567 (p : Pattern) (guard : d4474 p = 1) : d1989 p ≤ (0 : Int) + d3065 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1989, d3065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16556 p hg
    simpa only [d1989, d3065, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1989, d3065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16566 p hg
    simpa only [d1989, d3065, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16568 (p : Pattern) (guard : d4474 p = 1) : d1990 p ≤ (0 : Int) + d3066 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1990, d3066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16533 p hg
    simpa only [d1990, d3066, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1990, d3066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16567 p hg
    simpa only [d1990, d3066, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16569 (p : Pattern) (guard : d4474 p = 1) : d1991 p ≤ (0 : Int) + d3067 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1991, d3067, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16494 p hg
    simpa only [d1991, d3067, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1991, d3067, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d1991, d3067, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16570 (p : Pattern) (guard : d4474 p = 1) : d1992 p ≤ (0 : Int) + d3068 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1992, d3068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16569 p hg
    simpa only [d1992, d3068, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1992, d3068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d1992, d3068, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16571 (p : Pattern) (guard : d4474 p = 1) : d1993 p ≤ (0 : Int) + d3069 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1993, d3069, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16570 p hg
    simpa only [d1993, d3069, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1993, d3069, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d1993, d3069, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16572 (p : Pattern) (guard : d4474 p = 1) : d1994 p ≤ (0 : Int) + d3070 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1994, d3070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16571 p hg
    simpa only [d1994, d3070, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1994, d3070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d1994, d3070, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16573 (p : Pattern) (guard : d4474 p = 1) : d1995 p ≤ (0 : Int) + d3071 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1995, d3071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16567 p hg
    simpa only [d1995, d3071, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1995, d3071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16572 p hg
    simpa only [d1995, d3071, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16574 (p : Pattern) (guard : d4474 p = 1) : d1996 p ≤ (0 : Int) + d3072 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1996, d3072, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16568 p hg
    simpa only [d1996, d3072, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1996, d3072, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16573 p hg
    simpa only [d1996, d3072, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16575 (p : Pattern) (guard : d4474 p = 1) : d1997 p ≤ (0 : Int) + d2998 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1997, d2998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16487 p hg
    simpa only [d1997, d2998, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1997, d2998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16492 p hg
    simpa only [d1997, d2998, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16576 (p : Pattern) (guard : d4474 p = 1) : d1998 p ≤ (0 : Int) + d3001 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1998, d3001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16575 p hg
    simpa only [d1998, d3001, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1998, d3001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16495 p hg
    simpa only [d1998, d3001, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16577 (p : Pattern) (guard : d4474 p = 1) : d1999 p ≤ (0 : Int) + d3014 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1999, d3014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16576 p hg
    simpa only [d1999, d3014, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1999, d3014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16510 p hg
    simpa only [d1999, d3014, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16578 (p : Pattern) (guard : d4474 p = 1) : d2000 p ≤ (0 : Int) + d3017 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2000, d3017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16487 p hg
    simpa only [d2000, d3017, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2000, d3017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16517 p hg
    simpa only [d2000, d3017, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16579 (p : Pattern) (guard : d4474 p = 1) : d2001 p ≤ (0 : Int) + d3019 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2001, d3019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16578 p hg
    simpa only [d2001, d3019, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2001, d3019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16519 p hg
    simpa only [d2001, d3019, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16580 (p : Pattern) (guard : d4474 p = 1) : d2002 p ≤ (0 : Int) + d3022 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2002, d3022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16579 p hg
    simpa only [d2002, d3022, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2002, d3022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16522 p hg
    simpa only [d2002, d3022, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16581 (p : Pattern) (guard : d4474 p = 1) : d2003 p ≤ (0 : Int) + d3031 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2003, d3031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16580 p hg
    simpa only [d2003, d3031, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2003, d3031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16531 p hg
    simpa only [d2003, d3031, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16582 (p : Pattern) (guard : d4474 p = 1) : d2004 p ≤ (0 : Int) + d3032 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2004, d3032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16577 p hg
    simpa only [d2004, d3032, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2004, d3032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16581 p hg
    simpa only [d2004, d3032, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16583 (p : Pattern) (guard : d4474 p = 1) : d2005 p ≤ (0 : Int) + d3066 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2005, d3066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16582 p hg
    simpa only [d2005, d3066, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2005, d3066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16567 p hg
    simpa only [d2005, d3066, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16584 (p : Pattern) (guard : d4474 p = 1) : d2006 p ≤ (0 : Int) + d3073 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2006, d3073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16567 p hg
    simpa only [d2006, d3073, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2006, d3073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d2006, d3073, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16585 (p : Pattern) (guard : d4474 p = 1) : d2007 p ≤ (0 : Int) + d3074 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2007, d3074, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16583 p hg
    simpa only [d2007, d3074, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2007, d3074, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16584 p hg
    simpa only [d2007, d3074, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16586 (p : Pattern) (guard : d4474 p = 1) : d2008 p ≤ (0 : Int) + d3075 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2008, d3075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16574 p hg
    simpa only [d2008, d3075, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2008, d3075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16585 p hg
    simpa only [d2008, d3075, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16587 (p : Pattern) (guard : d4474 p = 1) : d2009 p ≤ (0 : Int) + d3076 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2009, d3076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16459 p hg
    simpa only [d2009, d3076, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2009, d3076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16586 p hg
    simpa only [d2009, d3076, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16588 (p : Pattern) (guard : d4474 p = 1) : d2010 p ≤ (0 : Int) + d3077 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2010, d3077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16481 p hg
    simpa only [d2010, d3077, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2010, d3077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16587 p hg
    simpa only [d2010, d3077, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16589 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d3079 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare16590 (p : Pattern) (guard : d4474 p = 1) : d19 p ≤ (0 : Int) + d3080 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d19, d3080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2003 p hg
    simpa only [d4474, d19, d3080, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d19, d3080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16589 p hg
    simpa only [d4474, d19, d3080, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16591 (p : Pattern) (guard : d4474 p = 1) : d2013 p ≤ (0 : Int) + d2013 p := by
  omega
theorem compare16592 (p : Pattern) (guard : d4474 p = 1) : d2014 p ≤ (0 : Int) + d3081 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2014, d3081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16590 p hg
    simpa only [d2014, d3081, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2014, d3081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16591 p hg
    simpa only [d2014, d3081, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16593 (p : Pattern) (guard : d4474 p = 1) : d2015 p ≤ (0 : Int) + d3082 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2015, d3082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16402 p hg
    simpa only [d2015, d3082, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2015, d3082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16592 p hg
    simpa only [d2015, d3082, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16594 (p : Pattern) (guard : d4474 p = 1) : d2016 p ≤ (0 : Int) + d3083 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2016, d3083, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16402 p hg
    simpa only [d2016, d3083, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2016, d3083, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16593 p hg
    simpa only [d2016, d3083, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16595 (p : Pattern) (guard : d4474 p = 1) : d2017 p ≤ (0 : Int) + d3084 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2017, d3084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16593 p hg
    simpa only [d2017, d3084, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2017, d3084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16415 p hg
    simpa only [d2017, d3084, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16596 (p : Pattern) (guard : d4474 p = 1) : d2018 p ≤ (0 : Int) + d3085 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2018, d3085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16594 p hg
    simpa only [d2018, d3085, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2018, d3085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16595 p hg
    simpa only [d2018, d3085, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16597 (p : Pattern) (guard : d4474 p = 1) : d2019 p ≤ (0 : Int) + d3086 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2019, d3086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16387 p hg
    simpa only [d2019, d3086, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2019, d3086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16353 p hg
    simpa only [d2019, d3086, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16598 (p : Pattern) (guard : d4474 p = 1) : d2020 p ≤ (0 : Int) + d3087 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2020, d3087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16418 p hg
    simpa only [d2020, d3087, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2020, d3087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16597 p hg
    simpa only [d2020, d3087, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16599 (p : Pattern) (guard : d4474 p = 1) : d2021 p ≤ (0 : Int) + d3088 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2021, d3088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16387 p hg
    simpa only [d2021, d3088, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2021, d3088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16356 p hg
    simpa only [d2021, d3088, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16600 (p : Pattern) (guard : d4474 p = 1) : d2022 p ≤ (0 : Int) + d3089 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2022, d3089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16419 p hg
    simpa only [d2022, d3089, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2022, d3089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d2022, d3089, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16601 (p : Pattern) (guard : d4474 p = 1) : d2023 p ≤ (0 : Int) + d3090 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2023, d3090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16599 p hg
    simpa only [d2023, d3090, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2023, d3090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16600 p hg
    simpa only [d2023, d3090, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16602 (p : Pattern) (guard : d4474 p = 1) : d2024 p ≤ (0 : Int) + d3091 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2024, d3091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16598 p hg
    simpa only [d2024, d3091, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2024, d3091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16601 p hg
    simpa only [d2024, d3091, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16603 (p : Pattern) (guard : d4474 p = 1) : d2025 p ≤ (0 : Int) + d3092 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2025, d3092, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16388 p hg
    simpa only [d2025, d3092, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2025, d3092, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16600 p hg
    simpa only [d2025, d3092, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16604 (p : Pattern) (guard : d4474 p = 1) : d2026 p ≤ (0 : Int) + d3093 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2026, d3093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16603 p hg
    simpa only [d2026, d3093, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2026, d3093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16395 p hg
    simpa only [d2026, d3093, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16605 (p : Pattern) (guard : d4474 p = 1) : d2027 p ≤ (0 : Int) + d3094 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2027, d3094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16602 p hg
    simpa only [d2027, d3094, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2027, d3094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16604 p hg
    simpa only [d2027, d3094, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16606 (p : Pattern) (guard : d4474 p = 1) : d2028 p ≤ (0 : Int) + d3095 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2028, d3095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16596 p hg
    simpa only [d2028, d3095, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2028, d3095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16605 p hg
    simpa only [d2028, d3095, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16607 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d3097 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare16608 (p : Pattern) (guard : d4474 p = 1) : d32 p ≤ (0 : Int) + d3098 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d32, d3098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2017 p hg
    simpa only [d4474, d32, d3098, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d32, d3098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16607 p hg
    simpa only [d4474, d32, d3098, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16609 (p : Pattern) (guard : d4474 p = 1) : d2031 p ≤ (0 : Int) + d2031 p := by
  omega
theorem compare16610 (p : Pattern) (guard : d4474 p = 1) : d2032 p ≤ (0 : Int) + d3099 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2032, d3099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16608 p hg
    simpa only [d2032, d3099, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2032, d3099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16609 p hg
    simpa only [d2032, d3099, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16611 (p : Pattern) (guard : d4474 p = 1) : d2033 p ≤ (0 : Int) + d3100 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2033, d3100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16402 p hg
    simpa only [d2033, d3100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2033, d3100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16610 p hg
    simpa only [d2033, d3100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16612 (p : Pattern) (guard : d4474 p = 1) : d2034 p ≤ (0 : Int) + d3101 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2034, d3101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16592 p hg
    simpa only [d2034, d3101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2034, d3101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16414 p hg
    simpa only [d2034, d3101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16613 (p : Pattern) (guard : d4474 p = 1) : d2035 p ≤ (0 : Int) + d3102 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2035, d3102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16611 p hg
    simpa only [d2035, d3102, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2035, d3102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16612 p hg
    simpa only [d2035, d3102, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16614 (p : Pattern) (guard : d4474 p = 1) : d2036 p ≤ (0 : Int) + d3103 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2036, d3103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16592 p hg
    simpa only [d2036, d3103, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2036, d3103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16380 p hg
    simpa only [d2036, d3103, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16615 (p : Pattern) (guard : d4474 p = 1) : d2037 p ≤ (0 : Int) + d3104 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2037, d3104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16614 p hg
    simpa only [d2037, d3104, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2037, d3104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16384 p hg
    simpa only [d2037, d3104, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16616 (p : Pattern) (guard : d4474 p = 1) : d2038 p ≤ (0 : Int) + d3105 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2038, d3105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16613 p hg
    simpa only [d2038, d3105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2038, d3105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16615 p hg
    simpa only [d2038, d3105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16617 (p : Pattern) (guard : d4474 p = 1) : d2039 p ≤ (0 : Int) + d3106 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2039, d3106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16597 p hg
    simpa only [d2039, d3106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2039, d3106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16359 p hg
    simpa only [d2039, d3106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16618 (p : Pattern) (guard : d4474 p = 1) : d2040 p ≤ (0 : Int) + d3107 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2040, d3107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16600 p hg
    simpa only [d2040, d3107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2040, d3107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16394 p hg
    simpa only [d2040, d3107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16619 (p : Pattern) (guard : d4474 p = 1) : d2041 p ≤ (0 : Int) + d3108 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2041, d3108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16617 p hg
    simpa only [d2041, d3108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2041, d3108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16618 p hg
    simpa only [d2041, d3108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16620 (p : Pattern) (guard : d4474 p = 1) : d2042 p ≤ (0 : Int) + d3109 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2042, d3109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16600 p hg
    simpa only [d2042, d3109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2042, d3109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d2042, d3109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16621 (p : Pattern) (guard : d4474 p = 1) : d2043 p ≤ (0 : Int) + d3110 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2043, d3110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16620 p hg
    simpa only [d2043, d3110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2043, d3110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d2043, d3110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16622 (p : Pattern) (guard : d4474 p = 1) : d2044 p ≤ (0 : Int) + d3111 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2044, d3111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16619 p hg
    simpa only [d2044, d3111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2044, d3111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16621 p hg
    simpa only [d2044, d3111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16623 (p : Pattern) (guard : d4474 p = 1) : d2045 p ≤ (0 : Int) + d3112 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2045, d3112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16616 p hg
    simpa only [d2045, d3112, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2045, d3112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16622 p hg
    simpa only [d2045, d3112, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16624 (p : Pattern) (guard : d4474 p = 1) : d2046 p ≤ (0 : Int) + d3113 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2046, d3113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16606 p hg
    simpa only [d2046, d3113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2046, d3113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16623 p hg
    simpa only [d2046, d3113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16625 (p : Pattern) (guard : d4474 p = 1) : d15 p ≤ (0 : Int) + d3114 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d15, d3114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1207 p hg
    simpa only [d4474, d15, d3114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d15, d3114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12772 p hg
    simpa only [d4474, d15, d3114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16626 (p : Pattern) (guard : d4474 p = 1) : d2049 p ≤ (0 : Int) + d2049 p := by
  omega
theorem compare16627 (p : Pattern) (guard : d4474 p = 1) : d2050 p ≤ (0 : Int) + d3115 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2050, d3115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16625 p hg
    simpa only [d2050, d3115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2050, d3115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16626 p hg
    simpa only [d2050, d3115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16628 (p : Pattern) (guard : d4474 p = 1) : d2055 p ≤ (0 : Int) + d2055 p := by
  omega
theorem compare16629 (p : Pattern) (guard : d4474 p = 1) : d2056 p ≤ (0 : Int) + d3116 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2056, d3116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16350 p hg
    simpa only [d2056, d3116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2056, d3116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16628 p hg
    simpa only [d2056, d3116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16630 (p : Pattern) (guard : d4474 p = 1) : d2057 p ≤ (0 : Int) + d3117 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2057, d3117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16627 p hg
    simpa only [d2057, d3117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2057, d3117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16629 p hg
    simpa only [d2057, d3117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16631 (p : Pattern) (guard : d4474 p = 1) : d2058 p ≤ (0 : Int) + d3118 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2058, d3118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16630 p hg
    simpa only [d2058, d3118, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2058, d3118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16421 p hg
    simpa only [d2058, d3118, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16632 (p : Pattern) (guard : d4474 p = 1) : d2059 p ≤ (0 : Int) + d3119 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2059, d3119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16631 p hg
    simpa only [d2059, d3119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2059, d3119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16422 p hg
    simpa only [d2059, d3119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16633 (p : Pattern) (guard : d4474 p = 1) : d192 p ≤ (0 : Int) + d3120 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d192, d3120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5250 p hg
    simpa only [d4474, d192, d3120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d192, d3120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12995 p hg
    simpa only [d4474, d192, d3120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16634 (p : Pattern) (guard : d4474 p = 1) : d2062 p ≤ (0 : Int) + d2062 p := by
  omega
theorem compare16635 (p : Pattern) (guard : d4474 p = 1) : d2063 p ≤ (0 : Int) + d3121 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2063, d3121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16633 p hg
    simpa only [d2063, d3121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2063, d3121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16634 p hg
    simpa only [d2063, d3121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16636 (p : Pattern) (guard : d4474 p = 1) : d2064 p ≤ (0 : Int) + d3122 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2064, d3122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16410 p hg
    simpa only [d2064, d3122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2064, d3122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16635 p hg
    simpa only [d2064, d3122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16637 (p : Pattern) (guard : d4474 p = 1) : d2065 p ≤ (0 : Int) + d3123 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2065, d3123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16636 p hg
    simpa only [d2065, d3123, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2065, d3123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d2065, d3123, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16638 (p : Pattern) (guard : d4474 p = 1) : d2066 p ≤ (0 : Int) + d3124 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2066, d3124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16637 p hg
    simpa only [d2066, d3124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2066, d3124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d2066, d3124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16639 (p : Pattern) (guard : d4474 p = 1) : d2067 p ≤ (0 : Int) + d3125 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2067, d3125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16632 p hg
    simpa only [d2067, d3125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2067, d3125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16638 p hg
    simpa only [d2067, d3125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16640 (p : Pattern) (guard : d4474 p = 1) : d2072 p ≤ (0 : Int) + d2072 p := by
  omega
theorem compare16641 (p : Pattern) (guard : d4474 p = 1) : d2073 p ≤ (0 : Int) + d3126 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2073, d3126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16387 p hg
    simpa only [d2073, d3126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2073, d3126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16640 p hg
    simpa only [d2073, d3126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16642 (p : Pattern) (guard : d4474 p = 1) : d2074 p ≤ (0 : Int) + d3127 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2074, d3127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16641 p hg
    simpa only [d2074, d3127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2074, d3127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16418 p hg
    simpa only [d2074, d3127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16643 (p : Pattern) (guard : d4474 p = 1) : d2075 p ≤ (0 : Int) + d3128 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2075, d3128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16410 p hg
    simpa only [d2075, d3128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2075, d3128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16383 p hg
    simpa only [d2075, d3128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16644 (p : Pattern) (guard : d4474 p = 1) : d2076 p ≤ (0 : Int) + d3129 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2076, d3129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16642 p hg
    simpa only [d2076, d3129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2076, d3129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16643 p hg
    simpa only [d2076, d3129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16645 (p : Pattern) (guard : d4474 p = 1) : d2077 p ≤ (0 : Int) + d3130 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2077, d3130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16644 p hg
    simpa only [d2077, d3130, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2077, d3130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16432 p hg
    simpa only [d2077, d3130, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16646 (p : Pattern) (guard : d4474 p = 1) : d2078 p ≤ (0 : Int) + d3131 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2078, d3131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16635 p hg
    simpa only [d2078, d3131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2078, d3131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d2078, d3131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16647 (p : Pattern) (guard : d4474 p = 1) : d2079 p ≤ (0 : Int) + d3132 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2079, d3132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16646 p hg
    simpa only [d2079, d3132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2079, d3132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d2079, d3132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16648 (p : Pattern) (guard : d4474 p = 1) : d2080 p ≤ (0 : Int) + d3133 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2080, d3133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16647 p hg
    simpa only [d2080, d3133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2080, d3133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d2080, d3133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16649 (p : Pattern) (guard : d4474 p = 1) : d2081 p ≤ (0 : Int) + d3134 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2081, d3134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16645 p hg
    simpa only [d2081, d3134, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2081, d3134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16648 p hg
    simpa only [d2081, d3134, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16650 (p : Pattern) (guard : d4474 p = 1) : d2082 p ≤ (0 : Int) + d3135 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2082, d3135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16639 p hg
    simpa only [d2082, d3135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2082, d3135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16649 p hg
    simpa only [d2082, d3135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16651 (p : Pattern) (guard : d4474 p = 1) : d2083 p ≤ (0 : Int) + d3136 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2083, d3136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16624 p hg
    simpa only [d2083, d3136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2083, d3136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16650 p hg
    simpa only [d2083, d3136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16652 (p : Pattern) (guard : d4474 p = 1) : d2084 p ≤ (0 : Int) + d3137 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2084, d3137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16650 p hg
    simpa only [d2084, d3137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2084, d3137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d2084, d3137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16653 (p : Pattern) (guard : d4474 p = 1) : d2085 p ≤ (0 : Int) + d3138 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2085, d3138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16651 p hg
    simpa only [d2085, d3138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2085, d3138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16652 p hg
    simpa only [d2085, d3138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16654 (p : Pattern) (guard : d4474 p = 1) : d2086 p ≤ (0 : Int) + d3139 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2086, d3139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16473 p hg
    simpa only [d2086, d3139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2086, d3139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16653 p hg
    simpa only [d2086, d3139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16655 (p : Pattern) (guard : d4474 p = 1) : d2087 p ≤ (0 : Int) + d3140 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2087, d3140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16459 p hg
    simpa only [d2087, d3140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2087, d3140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16654 p hg
    simpa only [d2087, d3140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16656 (p : Pattern) (guard : d4474 p = 1) : d2088 p ≤ (0 : Int) + d3141 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2088, d3141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16491 p hg
    simpa only [d2088, d3141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2088, d3141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d2088, d3141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16657 (p : Pattern) (guard : d4474 p = 1) : d2089 p ≤ (0 : Int) + d3142 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2089, d3142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16518 p hg
    simpa only [d2089, d3142, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2089, d3142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16656 p hg
    simpa only [d2089, d3142, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16658 (p : Pattern) (guard : d4474 p = 1) : d2090 p ≤ (0 : Int) + d3143 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2090, d3143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16656 p hg
    simpa only [d2090, d3143, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2090, d3143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d2090, d3143, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16659 (p : Pattern) (guard : d4474 p = 1) : d2091 p ≤ (0 : Int) + d3144 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2091, d3144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16657 p hg
    simpa only [d2091, d3144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2091, d3144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16658 p hg
    simpa only [d2091, d3144, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
