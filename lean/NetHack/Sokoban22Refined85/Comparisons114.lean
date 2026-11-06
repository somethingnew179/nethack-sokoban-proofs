/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons113
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare15960 (p : Pattern) (guard : d4475 p = 1) : d1925 p ≤ (2 : Int) + d4519 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d1925, d4519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15940 p hg
    simpa only [d1925, d4519, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d1925, d4519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15730 p hg
    simpa only [d1925, d4519, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15961 (p : Pattern) (guard : d4475 p = 1) : d1926 p ≤ (2 : Int) + d4520 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d1926, d4520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15959 p hg
    simpa only [d1926, d4520, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d1926, d4520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15960 p hg
    simpa only [d1926, d4520, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15962 (p : Pattern) (guard : d4475 p = 1) : d1927 p ≤ (2 : Int) + d4521 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d1927, d4521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15940 p hg
    simpa only [d1927, d4521, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d1927, d4521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15740 p hg
    simpa only [d1927, d4521, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15963 (p : Pattern) (guard : d4475 p = 1) : d1928 p ≤ (2 : Int) + d4522 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d1928, d4522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15962 p hg
    simpa only [d1928, d4522, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d1928, d4522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15702 p hg
    simpa only [d1928, d4522, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15964 (p : Pattern) (guard : d4475 p = 1) : d1929 p ≤ (2 : Int) + d4523 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d1929, d4523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15961 p hg
    simpa only [d1929, d4523, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d1929, d4523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15963 p hg
    simpa only [d1929, d4523, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15965 (p : Pattern) (guard : d0 p = 1) : d1936 p ≤ (2 : Int) + d4523 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare15966 (p : Pattern) (guard : d4476 p = 1) : d1937 p ≤ (2 : Int) + d4523 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d4476, d1937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15964 p hg
    simpa only [d4476, d1937, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4476, d1937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15965 p hg
    simpa only [d4476, d1937, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15967 (p : Pattern) (guard : d4476 p = 1) : d1938 p ≤ (2 : Int) + d4524 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4476 p = 1 := by simpa only [d1938, d4524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15947 p hg
    simpa only [d1938, d4524, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4476 p = 1 := by simpa only [d1938, d4524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15966 p hg
    simpa only [d1938, d4524, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15968 (p : Pattern) (guard : d0 p = 1) : d104 p ≤ (2 : Int) + d116 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare15969 (p : Pattern) (guard : d1 p = 1) : d1939 p ≤ (2 : Int) + d3 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14090 p hg
    simpa only [d1939, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2187 p hg
    simpa only [d1939, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15970 (p : Pattern) (guard : d1 p = 1) : d1940 p ≤ (2 : Int) + d116 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1940, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15969 p hg
    simpa only [d1940, d116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1940, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2188 p hg
    simpa only [d1940, d116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15971 (p : Pattern) (guard : d1 p = 1) : d1941 p ≤ (2 : Int) + d116 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14092 p hg
    simpa only [d1941, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15970 p hg
    simpa only [d1941, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15972 (p : Pattern) (guard : d1 p = 1) : d1942 p ≤ (2 : Int) + d116 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15971 p hg
    simpa only [d1942, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15970 p hg
    simpa only [d1942, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15973 (p : Pattern) (guard : d4474 p = 1) : d1943 p ≤ (2 : Int) + d116 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d1943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15972 p hg
    simpa only [d4474, d1943, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d1943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15956 p hg
    simpa only [d4474, d1943, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15974 (p : Pattern) (guard : d4475 p = 1) : d1944 p ≤ (2 : Int) + d116 p := by
  cases selected : p 182 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4475, d1944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15968 p hg
    simpa only [d4475, d1944, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d4475, d1944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15973 p hg
    simpa only [d4475, d1944, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15975 (p : Pattern) (guard : d0 p = 1) : d104 p ≤ (2 : Int) + d120 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare15976 (p : Pattern) (guard : d1 p = 1) : d1 p ≤ (2 : Int) + d7 p := by
  change (1 : Int) ≤ (2 : Int) + 7
  decide
theorem compare15977 (p : Pattern) (guard : d1 p = 1) : d102 p ≤ (2 : Int) + d119 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d102, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15976 p hg
    simpa only [d102, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d102, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d102, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15978 (p : Pattern) (guard : d1 p = 1) : d103 p ≤ (2 : Int) + d120 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d103, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15976 p hg
    simpa only [d103, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d103, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15977 p hg
    simpa only [d103, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15979 (p : Pattern) (guard : d1 p = 1) : d7 p ≤ (2 : Int) + d7 p := by
  omega
theorem compare15980 (p : Pattern) (guard : d1 p = 1) : d1945 p ≤ (2 : Int) + d7 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15976 p hg
    simpa only [d1945, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15979 p hg
    simpa only [d1945, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15981 (p : Pattern) (guard : d1 p = 1) : d119 p ≤ (2 : Int) + d119 p := by
  omega
theorem compare15982 (p : Pattern) (guard : d1 p = 1) : d1946 p ≤ (2 : Int) + d120 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1946, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15980 p hg
    simpa only [d1946, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1946, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15981 p hg
    simpa only [d1946, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15983 (p : Pattern) (guard : d1 p = 1) : d1947 p ≤ (2 : Int) + d120 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15978 p hg
    simpa only [d1947, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15982 p hg
    simpa only [d1947, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15984 (p : Pattern) (guard : d1 p = 1) : d5 p ≤ (2 : Int) + d7 p := by
  change (5 : Int) ≤ (2 : Int) + 7
  decide
theorem compare15985 (p : Pattern) (guard : d1 p = 1) : d1939 p ≤ (2 : Int) + d7 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15976 p hg
    simpa only [d1939, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15984 p hg
    simpa only [d1939, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15986 (p : Pattern) (guard : d1 p = 1) : d106 p ≤ (2 : Int) + d119 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d106, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15984 p hg
    simpa only [d106, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d106, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d106, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15987 (p : Pattern) (guard : d1 p = 1) : d1940 p ≤ (2 : Int) + d120 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1940, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15985 p hg
    simpa only [d1940, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1940, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15986 p hg
    simpa only [d1940, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15988 (p : Pattern) (guard : d1 p = 1) : d1948 p ≤ (2 : Int) + d7 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15976 p hg
    simpa only [d1948, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4942 p hg
    simpa only [d1948, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15989 (p : Pattern) (guard : d1 p = 1) : d1949 p ≤ (2 : Int) + d120 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1949, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15988 p hg
    simpa only [d1949, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1949, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4943 p hg
    simpa only [d1949, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15990 (p : Pattern) (guard : d1 p = 1) : d1950 p ≤ (2 : Int) + d120 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15987 p hg
    simpa only [d1950, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15989 p hg
    simpa only [d1950, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15991 (p : Pattern) (guard : d1 p = 1) : d1951 p ≤ (2 : Int) + d120 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15983 p hg
    simpa only [d1951, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15990 p hg
    simpa only [d1951, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15992 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (2 : Int) + d120 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare15993 (p : Pattern) (guard : d4474 p = 1) : d1952 p ≤ (2 : Int) + d120 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d1952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15991 p hg
    simpa only [d4474, d1952, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d1952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15992 p hg
    simpa only [d4474, d1952, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15994 (p : Pattern) (guard : d4475 p = 1) : d1953 p ≤ (2 : Int) + d120 p := by
  cases selected : p 182 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4475, d1953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15975 p hg
    simpa only [d4475, d1953, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d4475, d1953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15993 p hg
    simpa only [d4475, d1953, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15995 (p : Pattern) (guard : d4475 p = 1) : d1954 p ≤ (2 : Int) + d4525 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d1954, d4525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15974 p hg
    simpa only [d1954, d4525, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d1954, d4525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15994 p hg
    simpa only [d1954, d4525, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15996 (p : Pattern) (guard : d0 p = 1) : d104 p ≤ (2 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare15997 (p : Pattern) (guard : d1 p = 1) : d1 p ≤ (2 : Int) + d12 p := by
  change (1 : Int) ≤ (2 : Int) + 12
  decide
theorem compare15998 (p : Pattern) (guard : d1 p = 1) : d102 p ≤ (2 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15997 p hg
    simpa only [d102, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d102, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15999 (p : Pattern) (guard : d1 p = 1) : d103 p ≤ (2 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15997 p hg
    simpa only [d103, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15998 p hg
    simpa only [d103, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16000 (p : Pattern) (guard : d1 p = 1) : d1945 p ≤ (2 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15997 p hg
    simpa only [d1945, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4929 p hg
    simpa only [d1945, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16001 (p : Pattern) (guard : d1 p = 1) : d1946 p ≤ (2 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16000 p hg
    simpa only [d1946, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4930 p hg
    simpa only [d1946, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16002 (p : Pattern) (guard : d1 p = 1) : d1947 p ≤ (2 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15999 p hg
    simpa only [d1947, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16001 p hg
    simpa only [d1947, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16003 (p : Pattern) (guard : d1 p = 1) : d1939 p ≤ (2 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15997 p hg
    simpa only [d1939, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4785 p hg
    simpa only [d1939, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16004 (p : Pattern) (guard : d1 p = 1) : d1940 p ≤ (2 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16003 p hg
    simpa only [d1940, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4786 p hg
    simpa only [d1940, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16005 (p : Pattern) (guard : d1 p = 1) : d1955 p ≤ (2 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15998 p hg
    simpa only [d1955, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1830 p hg
    simpa only [d1955, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16006 (p : Pattern) (guard : d1 p = 1) : d1956 p ≤ (2 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16004 p hg
    simpa only [d1956, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16005 p hg
    simpa only [d1956, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16007 (p : Pattern) (guard : d1 p = 1) : d1957 p ≤ (2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16002 p hg
    simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16006 p hg
    simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16008 (p : Pattern) (guard : d4474 p = 1) : d1958 p ≤ (2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d1958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16007 p hg
    simpa only [d4474, d1958, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d1958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6043 p hg
    simpa only [d4474, d1958, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16009 (p : Pattern) (guard : d4475 p = 1) : d1959 p ≤ (2 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4475, d1959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15996 p hg
    simpa only [d4475, d1959, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d4475, d1959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16008 p hg
    simpa only [d4475, d1959, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16010 (p : Pattern) (guard : d0 p = 1) : d108 p ≤ (2 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare16011 (p : Pattern) (guard : d1 p = 1) : d1960 p ≤ (2 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4785 p hg
    simpa only [d1960, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1755 p hg
    simpa only [d1960, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16012 (p : Pattern) (guard : d1 p = 1) : d1961 p ≤ (2 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16011 p hg
    simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1756 p hg
    simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16013 (p : Pattern) (guard : d1 p = 1) : d1962 p ≤ (2 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4787 p hg
    simpa only [d1962, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16012 p hg
    simpa only [d1962, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16014 (p : Pattern) (guard : d1 p = 1) : d1963 p ≤ (2 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4785 p hg
    simpa only [d1963, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1822 p hg
    simpa only [d1963, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16015 (p : Pattern) (guard : d1 p = 1) : d1964 p ≤ (2 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1964, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16014 p hg
    simpa only [d1964, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1964, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1823 p hg
    simpa only [d1964, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16016 (p : Pattern) (guard : d1 p = 1) : d348 p ≤ (2 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4786 p hg
    simpa only [d348, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d348, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16017 (p : Pattern) (guard : d1 p = 1) : d1965 p ≤ (2 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1965, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16015 p hg
    simpa only [d1965, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1965, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16016 p hg
    simpa only [d1965, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16018 (p : Pattern) (guard : d1 p = 1) : d1966 p ≤ (2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16013 p hg
    simpa only [d1966, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16017 p hg
    simpa only [d1966, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16019 (p : Pattern) (guard : d4474 p = 1) : d1967 p ≤ (2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d1967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16018 p hg
    simpa only [d4474, d1967, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d1967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6043 p hg
    simpa only [d4474, d1967, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16020 (p : Pattern) (guard : d4475 p = 1) : d1968 p ≤ (2 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4475, d1968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16010 p hg
    simpa only [d4475, d1968, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d4475, d1968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16019 p hg
    simpa only [d4475, d1968, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16021 (p : Pattern) (guard : d4475 p = 1) : d1969 p ≤ (2 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d1969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16009 p hg
    simpa only [d1969, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d1969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16020 p hg
    simpa only [d1969, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16022 (p : Pattern) (guard : d4475 p = 1) : d1970 p ≤ (2 : Int) + d4526 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d1970, d4526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15995 p hg
    simpa only [d1970, d4526, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d1970, d4526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16021 p hg
    simpa only [d1970, d4526, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16023 (p : Pattern) (guard : d4475 p = 1) : d1888 p ≤ (2 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d1888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15851 p hg
    simpa only [d1888, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d1888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15702 p hg
    simpa only [d1888, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16024 (p : Pattern) (guard : d4475 p = 1) : d1971 p ≤ (2 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d1971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16021 p hg
    simpa only [d1971, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d1971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16023 p hg
    simpa only [d1971, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16025 (p : Pattern) (guard : d4475 p = 1) : d1972 p ≤ (2 : Int) + d4527 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d1972, d4527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16022 p hg
    simpa only [d1972, d4527, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d1972, d4527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16024 p hg
    simpa only [d1972, d4527, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16026 (p : Pattern) (guard : d0 p = 1) : d1977 p ≤ (2 : Int) + d4527 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare16027 (p : Pattern) (guard : d4476 p = 1) : d1978 p ≤ (2 : Int) + d4527 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d4476, d1978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16025 p hg
    simpa only [d4476, d1978, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4476, d1978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16026 p hg
    simpa only [d4476, d1978, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16028 (p : Pattern) (guard : d0 p = 1) : d117 p ≤ (2 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare16029 (p : Pattern) (guard : d1 p = 1) : d1891 p ≤ (2 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4893 p hg
    simpa only [d1891, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1822 p hg
    simpa only [d1891, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16030 (p : Pattern) (guard : d1 p = 1) : d1892 p ≤ (2 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16029 p hg
    simpa only [d1892, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1823 p hg
    simpa only [d1892, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16031 (p : Pattern) (guard : d1 p = 1) : d1893 p ≤ (2 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4895 p hg
    simpa only [d1893, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16030 p hg
    simpa only [d1893, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16032 (p : Pattern) (guard : d1 p = 1) : d1894 p ≤ (2 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4893 p hg
    simpa only [d1894, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4929 p hg
    simpa only [d1894, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16033 (p : Pattern) (guard : d1 p = 1) : d1895 p ≤ (2 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16032 p hg
    simpa only [d1895, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4930 p hg
    simpa only [d1895, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16034 (p : Pattern) (guard : d1 p = 1) : d1896 p ≤ (2 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4894 p hg
    simpa only [d1896, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d1896, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16035 (p : Pattern) (guard : d1 p = 1) : d1897 p ≤ (2 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16033 p hg
    simpa only [d1897, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16034 p hg
    simpa only [d1897, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16036 (p : Pattern) (guard : d1 p = 1) : d1898 p ≤ (2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16031 p hg
    simpa only [d1898, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16035 p hg
    simpa only [d1898, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16037 (p : Pattern) (guard : d4474 p = 1) : d1899 p ≤ (2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d1899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16036 p hg
    simpa only [d4474, d1899, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d1899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6043 p hg
    simpa only [d4474, d1899, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16038 (p : Pattern) (guard : d4475 p = 1) : d1973 p ≤ (2 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4475, d1973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16028 p hg
    simpa only [d4475, d1973, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d4475, d1973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16037 p hg
    simpa only [d4475, d1973, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16039 (p : Pattern) (guard : d4475 p = 1) : d1979 p ≤ (2 : Int) + d4529 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d1979, d4529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15994 p hg
    simpa only [d1979, d4529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d1979, d4529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16038 p hg
    simpa only [d1979, d4529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16040 (p : Pattern) (guard : d4475 p = 1) : d1980 p ≤ (2 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d1980, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16020 p hg
    simpa only [d1980, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d1980, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15851 p hg
    simpa only [d1980, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16041 (p : Pattern) (guard : d4475 p = 1) : d1981 p ≤ (2 : Int) + d4530 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d1981, d4530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16039 p hg
    simpa only [d1981, d4530, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d1981, d4530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16040 p hg
    simpa only [d1981, d4530, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16042 (p : Pattern) (guard : d4475 p = 1) : d1982 p ≤ (2 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d1982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16020 p hg
    simpa only [d1982, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d1982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15858 p hg
    simpa only [d1982, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16043 (p : Pattern) (guard : d4475 p = 1) : d1983 p ≤ (2 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d1983, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16042 p hg
    simpa only [d1983, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d1983, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15702 p hg
    simpa only [d1983, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16044 (p : Pattern) (guard : d4475 p = 1) : d1984 p ≤ (2 : Int) + d4531 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d1984, d4531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16041 p hg
    simpa only [d1984, d4531, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d1984, d4531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16043 p hg
    simpa only [d1984, d4531, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16045 (p : Pattern) (guard : d0 p = 1) : d1987 p ≤ (2 : Int) + d4531 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare16046 (p : Pattern) (guard : d4476 p = 1) : d1988 p ≤ (2 : Int) + d4531 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d4476, d1988, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16044 p hg
    simpa only [d4476, d1988, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4476, d1988, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16045 p hg
    simpa only [d4476, d1988, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16047 (p : Pattern) (guard : d4476 p = 1) : d1989 p ≤ (2 : Int) + d5512 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4476 p = 1 := by simpa only [d1989, d5512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16027 p hg
    simpa only [d1989, d5512, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4476 p = 1 := by simpa only [d1989, d5512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16046 p hg
    simpa only [d1989, d5512, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16048 (p : Pattern) (guard : d4476 p = 1) : d1990 p ≤ (2 : Int) + d5513 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4476 p = 1 := by simpa only [d1990, d5513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15967 p hg
    simpa only [d1990, d5513, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4476 p = 1 := by simpa only [d1990, d5513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16047 p hg
    simpa only [d1990, d5513, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16049 (p : Pattern) (guard : d4475 p = 1) : d1991 p ≤ (2 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16023 p hg
    simpa only [d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15702 p hg
    simpa only [d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16050 (p : Pattern) (guard : d4475 p = 1) : d1992 p ≤ (2 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d1992, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16049 p hg
    simpa only [d1992, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d1992, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15702 p hg
    simpa only [d1992, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16051 (p : Pattern) (guard : d4476 p = 1) : d1993 p ≤ (2 : Int) + d12 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d4476, d1993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16050 p hg
    simpa only [d4476, d1993, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4476, d1993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6043 p hg
    simpa only [d4476, d1993, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16052 (p : Pattern) (guard : d4476 p = 1) : d1994 p ≤ (2 : Int) + d12 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4476 p = 1 := by simpa only [d1994, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16051 p hg
    simpa only [d1994, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4476 p = 1 := by simpa only [d1994, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15895 p hg
    simpa only [d1994, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16053 (p : Pattern) (guard : d4476 p = 1) : d1995 p ≤ (2 : Int) + d5514 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4476 p = 1 := by simpa only [d1995, d5514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16047 p hg
    simpa only [d1995, d5514, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4476 p = 1 := by simpa only [d1995, d5514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16052 p hg
    simpa only [d1995, d5514, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16054 (p : Pattern) (guard : d4476 p = 1) : d1996 p ≤ (2 : Int) + d5515 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4476 p = 1 := by simpa only [d1996, d5515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16048 p hg
    simpa only [d1996, d5515, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4476 p = 1 := by simpa only [d1996, d5515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16053 p hg
    simpa only [d1996, d5515, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16055 (p : Pattern) (guard : d4475 p = 1) : d1997 p ≤ (2 : Int) + d4514 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d1997, d4514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15930 p hg
    simpa only [d1997, d4514, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d1997, d4514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15941 p hg
    simpa only [d1997, d4514, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16056 (p : Pattern) (guard : d4475 p = 1) : d1998 p ≤ (2 : Int) + d4517 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d1998, d4517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16055 p hg
    simpa only [d1998, d4517, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d1998, d4517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15944 p hg
    simpa only [d1998, d4517, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16057 (p : Pattern) (guard : d4476 p = 1) : d1999 p ≤ (2 : Int) + d4517 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d4476, d1999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16056 p hg
    simpa only [d4476, d1999, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4476, d1999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15946 p hg
    simpa only [d4476, d1999, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16058 (p : Pattern) (guard : d4475 p = 1) : d2000 p ≤ (2 : Int) + d4518 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d2000, d4518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15930 p hg
    simpa only [d2000, d4518, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d2000, d4518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15958 p hg
    simpa only [d2000, d4518, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16059 (p : Pattern) (guard : d4475 p = 1) : d2001 p ≤ (2 : Int) + d4520 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d2001, d4520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16058 p hg
    simpa only [d2001, d4520, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d2001, d4520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15960 p hg
    simpa only [d2001, d4520, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16060 (p : Pattern) (guard : d4475 p = 1) : d2002 p ≤ (2 : Int) + d4523 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d2002, d4523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16059 p hg
    simpa only [d2002, d4523, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d2002, d4523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15963 p hg
    simpa only [d2002, d4523, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16061 (p : Pattern) (guard : d4476 p = 1) : d2003 p ≤ (2 : Int) + d4523 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d4476, d2003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16060 p hg
    simpa only [d4476, d2003, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4476, d2003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15965 p hg
    simpa only [d4476, d2003, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16062 (p : Pattern) (guard : d4476 p = 1) : d2004 p ≤ (2 : Int) + d4524 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4476 p = 1 := by simpa only [d2004, d4524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16057 p hg
    simpa only [d2004, d4524, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4476 p = 1 := by simpa only [d2004, d4524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16061 p hg
    simpa only [d2004, d4524, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16063 (p : Pattern) (guard : d4476 p = 1) : d2005 p ≤ (2 : Int) + d5513 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4476 p = 1 := by simpa only [d2005, d5513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16062 p hg
    simpa only [d2005, d5513, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4476 p = 1 := by simpa only [d2005, d5513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16047 p hg
    simpa only [d2005, d5513, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16064 (p : Pattern) (guard : d4476 p = 1) : d2006 p ≤ (2 : Int) + d5514 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4476 p = 1 := by simpa only [d2006, d5514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16047 p hg
    simpa only [d2006, d5514, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4476 p = 1 := by simpa only [d2006, d5514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15895 p hg
    simpa only [d2006, d5514, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16065 (p : Pattern) (guard : d4476 p = 1) : d2007 p ≤ (2 : Int) + d5515 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4476 p = 1 := by simpa only [d2007, d5515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16063 p hg
    simpa only [d2007, d5515, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4476 p = 1 := by simpa only [d2007, d5515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16064 p hg
    simpa only [d2007, d5515, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16066 (p : Pattern) (guard : d4476 p = 1) : d2008 p ≤ (2 : Int) + d5515 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4476 p = 1 := by simpa only [d2008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16054 p hg
    simpa only [d2008, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4476 p = 1 := by simpa only [d2008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16065 p hg
    simpa only [d2008, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16067 (p : Pattern) (guard : d4476 p = 1) : d2009 p ≤ (2 : Int) + d5516 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4476 p = 1 := by simpa only [d2009, d5516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15898 p hg
    simpa only [d2009, d5516, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4476 p = 1 := by simpa only [d2009, d5516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16066 p hg
    simpa only [d2009, d5516, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16068 (p : Pattern) (guard : d4476 p = 1) : d2010 p ≤ (2 : Int) + d5517 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4476 p = 1 := by simpa only [d2010, d5517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15919 p hg
    simpa only [d2010, d5517, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4476 p = 1 := by simpa only [d2010, d5517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16067 p hg
    simpa only [d2010, d5517, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16069 (p : Pattern) (guard : d0 p = 1) : d19 p ≤ (2 : Int) + d35 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare16070 (p : Pattern) (guard : d1 p = 1) : d18 p ≤ (2 : Int) + d35 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d18, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15763 p hg
    simpa only [d18, d35, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d18, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15765 p hg
    simpa only [d18, d35, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16071 (p : Pattern) (guard : d1 p = 1) : d1794 p ≤ (2 : Int) + d6 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15763 p hg
    simpa only [d1794, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4870 p hg
    simpa only [d1794, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16072 (p : Pattern) (guard : d1 p = 1) : d1795 p ≤ (2 : Int) + d35 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1795, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16071 p hg
    simpa only [d1795, d35, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1795, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4871 p hg
    simpa only [d1795, d35, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16073 (p : Pattern) (guard : d1 p = 1) : d2011 p ≤ (2 : Int) + d35 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16070 p hg
    simpa only [d2011, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16072 p hg
    simpa only [d2011, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16074 (p : Pattern) (guard : d1 p = 1) : d2012 p ≤ (2 : Int) + d35 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16073 p hg
    simpa only [d2012, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16072 p hg
    simpa only [d2012, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16075 (p : Pattern) (guard : d4474 p = 1) : d2013 p ≤ (2 : Int) + d35 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d2013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16074 p hg
    simpa only [d4474, d2013, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d2013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15771 p hg
    simpa only [d4474, d2013, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16076 (p : Pattern) (guard : d4475 p = 1) : d2014 p ≤ (2 : Int) + d35 p := by
  cases selected : p 182 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4475, d2014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16069 p hg
    simpa only [d4475, d2014, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d4475, d2014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16075 p hg
    simpa only [d4475, d2014, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16077 (p : Pattern) (guard : d4475 p = 1) : d2015 p ≤ (2 : Int) + d4490 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d2015, d4490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15753 p hg
    simpa only [d2015, d4490, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d2015, d4490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16076 p hg
    simpa only [d2015, d4490, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16078 (p : Pattern) (guard : d4475 p = 1) : d2016 p ≤ (2 : Int) + d4546 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d2016, d4546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15753 p hg
    simpa only [d2016, d4546, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d2016, d4546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16077 p hg
    simpa only [d2016, d4546, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16079 (p : Pattern) (guard : d4475 p = 1) : d1806 p ≤ (2 : Int) + d4486 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d1806, d4486, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15873 p hg
    simpa only [d1806, d4486, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d1806, d4486, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15702 p hg
    simpa only [d1806, d4486, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16080 (p : Pattern) (guard : d4475 p = 1) : d2017 p ≤ (2 : Int) + d4491 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d2017, d4491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16077 p hg
    simpa only [d2017, d4491, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d2017, d4491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16079 p hg
    simpa only [d2017, d4491, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16081 (p : Pattern) (guard : d4475 p = 1) : d2018 p ≤ (2 : Int) + d4547 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d2018, d4547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16078 p hg
    simpa only [d2018, d4547, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d2018, d4547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16080 p hg
    simpa only [d2018, d4547, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16082 (p : Pattern) (guard : d0 p = 1) : d2027 p ≤ (2 : Int) + d4547 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare16083 (p : Pattern) (guard : d4476 p = 1) : d2028 p ≤ (2 : Int) + d4547 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d4476, d2028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16081 p hg
    simpa only [d4476, d2028, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4476, d2028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16082 p hg
    simpa only [d4476, d2028, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16084 (p : Pattern) (guard : d0 p = 1) : d32 p ≤ (2 : Int) + d18 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare16085 (p : Pattern) (guard : d1 p = 1) : d1713 p ≤ (2 : Int) + d4 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4831 p hg
    simpa only [d1713, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4697 p hg
    simpa only [d1713, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16086 (p : Pattern) (guard : d1 p = 1) : d1714 p ≤ (2 : Int) + d18 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1714, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16085 p hg
    simpa only [d1714, d18, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1714, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4698 p hg
    simpa only [d1714, d18, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16087 (p : Pattern) (guard : d1 p = 1) : d2029 p ≤ (2 : Int) + d18 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4833 p hg
    simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16086 p hg
    simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16088 (p : Pattern) (guard : d1 p = 1) : d2030 p ≤ (2 : Int) + d18 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16087 p hg
    simpa only [d2030, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16086 p hg
    simpa only [d2030, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16089 (p : Pattern) (guard : d4474 p = 1) : d2031 p ≤ (2 : Int) + d18 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d2031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16088 p hg
    simpa only [d4474, d2031, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d2031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15688 p hg
    simpa only [d4474, d2031, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16090 (p : Pattern) (guard : d4475 p = 1) : d2032 p ≤ (2 : Int) + d18 p := by
  cases selected : p 182 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4475, d2032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16084 p hg
    simpa only [d4475, d2032, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d4475, d2032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16089 p hg
    simpa only [d4475, d2032, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16091 (p : Pattern) (guard : d4475 p = 1) : d2033 p ≤ (2 : Int) + d4549 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d2033, d4549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15753 p hg
    simpa only [d2033, d4549, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d2033, d4549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16090 p hg
    simpa only [d2033, d4549, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16092 (p : Pattern) (guard : d4475 p = 1) : d2034 p ≤ (2 : Int) + d4550 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d2034, d4550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16076 p hg
    simpa only [d2034, d4550, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d2034, d4550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15873 p hg
    simpa only [d2034, d4550, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16093 (p : Pattern) (guard : d4475 p = 1) : d2035 p ≤ (2 : Int) + d4551 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d2035, d4551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16091 p hg
    simpa only [d2035, d4551, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d2035, d4551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16092 p hg
    simpa only [d2035, d4551, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16094 (p : Pattern) (guard : d4475 p = 1) : d2036 p ≤ (2 : Int) + d4494 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d2036, d4494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16076 p hg
    simpa only [d2036, d4494, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d2036, d4494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15851 p hg
    simpa only [d2036, d4494, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16095 (p : Pattern) (guard : d4475 p = 1) : d2037 p ≤ (2 : Int) + d4495 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d2037, d4495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16094 p hg
    simpa only [d2037, d4495, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d2037, d4495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15859 p hg
    simpa only [d2037, d4495, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16096 (p : Pattern) (guard : d4475 p = 1) : d2038 p ≤ (2 : Int) + d4552 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d2038, d4552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16093 p hg
    simpa only [d2038, d4552, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d2038, d4552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16095 p hg
    simpa only [d2038, d4552, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16097 (p : Pattern) (guard : d0 p = 1) : d2044 p ≤ (2 : Int) + d4552 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare16098 (p : Pattern) (guard : d4476 p = 1) : d2045 p ≤ (2 : Int) + d4552 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d4476, d2045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16096 p hg
    simpa only [d4476, d2045, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4476, d2045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16097 p hg
    simpa only [d4476, d2045, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16099 (p : Pattern) (guard : d4476 p = 1) : d2046 p ≤ (2 : Int) + d5518 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4476 p = 1 := by simpa only [d2046, d5518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16083 p hg
    simpa only [d2046, d5518, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4476 p = 1 := by simpa only [d2046, d5518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16098 p hg
    simpa only [d2046, d5518, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
