/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Comparisons067
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare9520 (p : Pattern) (guard : d1954 p = 1) : d16 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1949 p = 1 := by simpa only [d1954, d16, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9510 p hg
    simpa only [d1954, d16, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1953 p = 1 := by simpa only [d1954, d16, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9519 p hg
    simpa only [d1954, d16, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9521 (p : Pattern) (guard : d1958 p = 1) : d2 p ≤ (0 : Int) + d2 p := by
  omega
theorem compare9522 (p : Pattern) (guard : d1959 p = 1) : d328 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1954 p = 1 := by simpa only [d1959, d328, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9520 p hg
    simpa only [d1959, d328, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1958 p = 1 := by simpa only [d1959, d328, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9521 p hg
    simpa only [d1959, d328, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9523 (p : Pattern) (guard : d1960 p = 1) : d328 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1955 p = 1 := by simpa only [d1960, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9502 p hg
    simpa only [d1960, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1959 p = 1 := by simpa only [d1960, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9522 p hg
    simpa only [d1960, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9524 (p : Pattern) (guard : d1944 p = 1) : d6 p ≤ (0 : Int) + d19 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1944, d6, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare693 p hg
    simpa only [d1944, d6, d19, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1943 p = 1 := by simpa only [d1944, d6, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9505 p hg
    simpa only [d1944, d6, d19, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9525 (p : Pattern) (guard : d1943 p = 1) : d4 p ≤ (0 : Int) + d21 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1943, d4, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9373 p hg
    simpa only [d1943, d4, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d1943, d4, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1214 p hg
    simpa only [d1943, d4, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9526 (p : Pattern) (guard : d1947 p = 1) : d7 p ≤ (0 : Int) + d23 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1943 p = 1 := by simpa only [d1947, d7, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9525 p hg
    simpa only [d1947, d7, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d1947, d7, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4473 p hg
    simpa only [d1947, d7, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9527 (p : Pattern) (guard : d1948 p = 1) : d8 p ≤ (0 : Int) + d135 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1944 p = 1 := by simpa only [d1948, d8, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9524 p hg
    simpa only [d1948, d8, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1947 p = 1 := by simpa only [d1948, d8, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9526 p hg
    simpa only [d1948, d8, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9528 (p : Pattern) (guard : d1949 p = 1) : d8 p ≤ (0 : Int) + d135 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1945 p = 1 := by simpa only [d1949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9488 p hg
    simpa only [d1949, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1948 p = 1 := by simpa only [d1949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9527 p hg
    simpa only [d1949, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9529 (p : Pattern) (guard : d1954 p = 1) : d16 p ≤ (0 : Int) + d136 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1949 p = 1 := by simpa only [d1954, d16, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9528 p hg
    simpa only [d1954, d16, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1953 p = 1 := by simpa only [d1954, d16, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9519 p hg
    simpa only [d1954, d16, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9530 (p : Pattern) (guard : d1959 p = 1) : d328 p ≤ (0 : Int) + d137 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1954 p = 1 := by simpa only [d1959, d328, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9529 p hg
    simpa only [d1959, d328, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1958 p = 1 := by simpa only [d1959, d328, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9521 p hg
    simpa only [d1959, d328, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9531 (p : Pattern) (guard : d1947 p = 1) : d37 p ≤ (0 : Int) + d2 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1943 p = 1 := by simpa only [d1947, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9505 p hg
    simpa only [d1947, d37, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d1947, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4473 p hg
    simpa only [d1947, d37, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9532 (p : Pattern) (guard : d1948 p = 1) : d38 p ≤ (0 : Int) + d138 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1944 p = 1 := by simpa only [d1948, d38, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9506 p hg
    simpa only [d1948, d38, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1947 p = 1 := by simpa only [d1948, d38, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9531 p hg
    simpa only [d1948, d38, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9533 (p : Pattern) (guard : d1293 p = 1) : d5 p ≤ (0 : Int) + d2 p := by
  cases selected : p 160 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d1293, d5, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9396 p hg
    simpa only [d1293, d5, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1293, d5, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1293, d5, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9534 (p : Pattern) (guard : d1947 p = 1) : d6 p ≤ (0 : Int) + d23 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1943 p = 1 := by simpa only [d1947, d6, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9525 p hg
    simpa only [d1947, d6, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d1947, d6, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9533 p hg
    simpa only [d1947, d6, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9535 (p : Pattern) (guard : d1951 p = 1) : d37 p ≤ (0 : Int) + d2 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d1951, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9533 p hg
    simpa only [d1951, d37, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1951, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1951, d37, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9536 (p : Pattern) (guard : d1952 p = 1) : d38 p ≤ (0 : Int) + d138 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1947 p = 1 := by simpa only [d1952, d38, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9534 p hg
    simpa only [d1952, d38, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1951 p = 1 := by simpa only [d1952, d38, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9535 p hg
    simpa only [d1952, d38, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9537 (p : Pattern) (guard : d1953 p = 1) : d38 p ≤ (0 : Int) + d138 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1948 p = 1 := by simpa only [d1953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9532 p hg
    simpa only [d1953, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1952 p = 1 := by simpa only [d1953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9536 p hg
    simpa only [d1953, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9538 (p : Pattern) (guard : d1947 p = 1) : d6 p ≤ (0 : Int) + d2 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1943 p = 1 := by simpa only [d1947, d6, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9507 p hg
    simpa only [d1947, d6, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d1947, d6, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9533 p hg
    simpa only [d1947, d6, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9539 (p : Pattern) (guard : d1952 p = 1) : d38 p ≤ (0 : Int) + d2 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1947 p = 1 := by simpa only [d1952, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9538 p hg
    simpa only [d1952, d38, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1951 p = 1 := by simpa only [d1952, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9535 p hg
    simpa only [d1952, d38, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9540 (p : Pattern) (guard : d1951 p = 1) : d12 p ≤ (0 : Int) + d2 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d1951, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9516 p hg
    simpa only [d1951, d12, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1951, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2790 p hg
    simpa only [d1951, d12, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9541 (p : Pattern) (guard : d1956 p = 1) : d40 p ≤ (0 : Int) + d2 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1951 p = 1 := by simpa only [d1956, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9540 p hg
    simpa only [d1956, d40, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1956, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2377 p hg
    simpa only [d1956, d40, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9542 (p : Pattern) (guard : d1957 p = 1) : d41 p ≤ (0 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1952 p = 1 := by simpa only [d1957, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9539 p hg
    simpa only [d1957, d41, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1956 p = 1 := by simpa only [d1957, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9541 p hg
    simpa only [d1957, d41, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9543 (p : Pattern) (guard : d1958 p = 1) : d42 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1953 p = 1 := by simpa only [d1958, d42, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9537 p hg
    simpa only [d1958, d42, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1957 p = 1 := by simpa only [d1958, d42, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9542 p hg
    simpa only [d1958, d42, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9544 (p : Pattern) (guard : d1962 p = 1) : d2 p ≤ (0 : Int) + d2 p := by
  omega
theorem compare9545 (p : Pattern) (guard : d1963 p = 1) : d329 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1958 p = 1 := by simpa only [d1963, d329, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9543 p hg
    simpa only [d1963, d329, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1962 p = 1 := by simpa only [d1963, d329, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9544 p hg
    simpa only [d1963, d329, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9546 (p : Pattern) (guard : d1964 p = 1) : d330 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1959 p = 1 := by simpa only [d1964, d330, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9530 p hg
    simpa only [d1964, d330, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1963 p = 1 := by simpa only [d1964, d330, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9545 p hg
    simpa only [d1964, d330, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9547 (p : Pattern) (guard : d1965 p = 1) : d331 p ≤ (0 : Int) + d141 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1960 p = 1 := by simpa only [d1965, d331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9523 p hg
    simpa only [d1965, d331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1964 p = 1 := by simpa only [d1965, d331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9546 p hg
    simpa only [d1965, d331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9548 (p : Pattern) (guard : d1293 p = 1) : d4 p ≤ (0 : Int) + d2 p := by
  cases selected : p 160 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d1293, d4, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9396 p hg
    simpa only [d1293, d4, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1293, d4, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3404 p hg
    simpa only [d1293, d4, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9549 (p : Pattern) (guard : d1951 p = 1) : d7 p ≤ (0 : Int) + d2 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d1951, d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9548 p hg
    simpa only [d1951, d7, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1951, d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1951, d7, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9550 (p : Pattern) (guard : d1952 p = 1) : d8 p ≤ (0 : Int) + d138 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1947 p = 1 := by simpa only [d1952, d8, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9534 p hg
    simpa only [d1952, d8, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1951 p = 1 := by simpa only [d1952, d8, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9549 p hg
    simpa only [d1952, d8, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9551 (p : Pattern) (guard : d1953 p = 1) : d8 p ≤ (0 : Int) + d138 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1948 p = 1 := by simpa only [d1953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9509 p hg
    simpa only [d1953, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1952 p = 1 := by simpa only [d1953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9550 p hg
    simpa only [d1953, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9552 (p : Pattern) (guard : d1952 p = 1) : d8 p ≤ (0 : Int) + d2 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1947 p = 1 := by simpa only [d1952, d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9538 p hg
    simpa only [d1952, d8, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1951 p = 1 := by simpa only [d1952, d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9549 p hg
    simpa only [d1952, d8, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9553 (p : Pattern) (guard : d1956 p = 1) : d14 p ≤ (0 : Int) + d2 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1951 p = 1 := by simpa only [d1956, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9540 p hg
    simpa only [d1956, d14, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1956, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2353 p hg
    simpa only [d1956, d14, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9554 (p : Pattern) (guard : d1957 p = 1) : d15 p ≤ (0 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1952 p = 1 := by simpa only [d1957, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9552 p hg
    simpa only [d1957, d15, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1956 p = 1 := by simpa only [d1957, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9553 p hg
    simpa only [d1957, d15, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9555 (p : Pattern) (guard : d1958 p = 1) : d16 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1953 p = 1 := by simpa only [d1958, d16, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9551 p hg
    simpa only [d1958, d16, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1957 p = 1 := by simpa only [d1958, d16, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9554 p hg
    simpa only [d1958, d16, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9556 (p : Pattern) (guard : d1963 p = 1) : d328 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1958 p = 1 := by simpa only [d1963, d328, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9555 p hg
    simpa only [d1963, d328, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1962 p = 1 := by simpa only [d1963, d328, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9544 p hg
    simpa only [d1963, d328, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9557 (p : Pattern) (guard : d1964 p = 1) : d328 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1959 p = 1 := by simpa only [d1964, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9530 p hg
    simpa only [d1964, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1963 p = 1 := by simpa only [d1964, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9556 p hg
    simpa only [d1964, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9558 (p : Pattern) (guard : d1943 p = 1) : d4 p ≤ (0 : Int) + d17 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1943, d4, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare691 p hg
    simpa only [d1943, d4, d17, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d1943, d4, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1214 p hg
    simpa only [d1943, d4, d17, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9559 (p : Pattern) (guard : d1947 p = 1) : d6 p ≤ (0 : Int) + d19 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1943 p = 1 := by simpa only [d1947, d6, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9558 p hg
    simpa only [d1947, d6, d19, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d1947, d6, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9533 p hg
    simpa only [d1947, d6, d19, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9560 (p : Pattern) (guard : d1293 p = 1) : d4 p ≤ (0 : Int) + d21 p := by
  cases selected : p 160 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d1293, d4, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9415 p hg
    simpa only [d1293, d4, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1293, d4, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3404 p hg
    simpa only [d1293, d4, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9561 (p : Pattern) (guard : d1951 p = 1) : d7 p ≤ (0 : Int) + d23 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d1951, d7, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9560 p hg
    simpa only [d1951, d7, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1951, d7, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1951, d7, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9562 (p : Pattern) (guard : d1952 p = 1) : d8 p ≤ (0 : Int) + d135 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1947 p = 1 := by simpa only [d1952, d8, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9559 p hg
    simpa only [d1952, d8, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1951 p = 1 := by simpa only [d1952, d8, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9561 p hg
    simpa only [d1952, d8, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9563 (p : Pattern) (guard : d1953 p = 1) : d8 p ≤ (0 : Int) + d135 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1948 p = 1 := by simpa only [d1953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9527 p hg
    simpa only [d1953, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1952 p = 1 := by simpa only [d1953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9562 p hg
    simpa only [d1953, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9564 (p : Pattern) (guard : d1958 p = 1) : d16 p ≤ (0 : Int) + d136 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1953 p = 1 := by simpa only [d1958, d16, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9563 p hg
    simpa only [d1958, d16, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1957 p = 1 := by simpa only [d1958, d16, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9554 p hg
    simpa only [d1958, d16, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9565 (p : Pattern) (guard : d1963 p = 1) : d328 p ≤ (0 : Int) + d137 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1958 p = 1 := by simpa only [d1963, d328, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9564 p hg
    simpa only [d1963, d328, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1962 p = 1 := by simpa only [d1963, d328, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9544 p hg
    simpa only [d1963, d328, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9566 (p : Pattern) (guard : d1951 p = 1) : d6 p ≤ (0 : Int) + d23 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d1951, d6, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9560 p hg
    simpa only [d1951, d6, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1951, d6, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2786 p hg
    simpa only [d1951, d6, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9567 (p : Pattern) (guard : d1956 p = 1) : d38 p ≤ (0 : Int) + d138 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1951 p = 1 := by simpa only [d1956, d38, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9566 p hg
    simpa only [d1956, d38, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1956, d38, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2375 p hg
    simpa only [d1956, d38, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9568 (p : Pattern) (guard : d1957 p = 1) : d38 p ≤ (0 : Int) + d138 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1952 p = 1 := by simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9536 p hg
    simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1956 p = 1 := by simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9567 p hg
    simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9569 (p : Pattern) (guard : d1951 p = 1) : d6 p ≤ (0 : Int) + d2 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d1951, d6, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9548 p hg
    simpa only [d1951, d6, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1951, d6, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2786 p hg
    simpa only [d1951, d6, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9570 (p : Pattern) (guard : d1956 p = 1) : d38 p ≤ (0 : Int) + d2 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1951 p = 1 := by simpa only [d1956, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9569 p hg
    simpa only [d1956, d38, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1956, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2375 p hg
    simpa only [d1956, d38, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9571 (p : Pattern) (guard : d1961 p = 1) : d41 p ≤ (0 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1956 p = 1 := by simpa only [d1961, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9570 p hg
    simpa only [d1961, d41, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1961, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1604 p hg
    simpa only [d1961, d41, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9572 (p : Pattern) (guard : d1962 p = 1) : d42 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1957 p = 1 := by simpa only [d1962, d42, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9568 p hg
    simpa only [d1962, d42, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1961 p = 1 := by simpa only [d1962, d42, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9571 p hg
    simpa only [d1962, d42, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9573 (p : Pattern) (guard : d1966 p = 1) : d2 p ≤ (0 : Int) + d2 p := by
  omega
theorem compare9574 (p : Pattern) (guard : d1967 p = 1) : d329 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1962 p = 1 := by simpa only [d1967, d329, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9572 p hg
    simpa only [d1967, d329, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1966 p = 1 := by simpa only [d1967, d329, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9573 p hg
    simpa only [d1967, d329, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9575 (p : Pattern) (guard : d1968 p = 1) : d330 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1963 p = 1 := by simpa only [d1968, d330, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9565 p hg
    simpa only [d1968, d330, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1967 p = 1 := by simpa only [d1968, d330, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9574 p hg
    simpa only [d1968, d330, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9576 (p : Pattern) (guard : d1969 p = 1) : d331 p ≤ (0 : Int) + d141 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1964 p = 1 := by simpa only [d1969, d331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9557 p hg
    simpa only [d1969, d331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1968 p = 1 := by simpa only [d1969, d331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9575 p hg
    simpa only [d1969, d331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9577 (p : Pattern) (guard : d1970 p = 1) : d331 p ≤ (0 : Int) + d141 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1965 p = 1 := by simpa only [d1970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9547 p hg
    simpa only [d1970, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1969 p = 1 := by simpa only [d1970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9576 p hg
    simpa only [d1970, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9578 (p : Pattern) (guard : d1944 p = 1) : d12 p ≤ (0 : Int) + d23 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1944, d12, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare700 p hg
    simpa only [d1944, d12, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1943 p = 1 := by simpa only [d1944, d12, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9494 p hg
    simpa only [d1944, d12, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9579 (p : Pattern) (guard : d1948 p = 1) : d14 p ≤ (0 : Int) + d138 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1944 p = 1 := by simpa only [d1948, d14, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9578 p hg
    simpa only [d1948, d14, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1947 p = 1 := by simpa only [d1948, d14, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9497 p hg
    simpa only [d1948, d14, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9580 (p : Pattern) (guard : d1949 p = 1) : d15 p ≤ (0 : Int) + d138 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1945 p = 1 := by simpa only [d1949, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9504 p hg
    simpa only [d1949, d15, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1948 p = 1 := by simpa only [d1949, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9579 p hg
    simpa only [d1949, d15, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9581 (p : Pattern) (guard : d1954 p = 1) : d15 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1949 p = 1 := by simpa only [d1954, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9580 p hg
    simpa only [d1954, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1953 p = 1 := by simpa only [d1954, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9519 p hg
    simpa only [d1954, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9582 (p : Pattern) (guard : d1959 p = 1) : d332 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1954 p = 1 := by simpa only [d1959, d332, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9581 p hg
    simpa only [d1959, d332, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1958 p = 1 := by simpa only [d1959, d332, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9521 p hg
    simpa only [d1959, d332, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9583 (p : Pattern) (guard : d1958 p = 1) : d15 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1953 p = 1 := by simpa only [d1958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9519 p hg
    simpa only [d1958, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1957 p = 1 := by simpa only [d1958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9554 p hg
    simpa only [d1958, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9584 (p : Pattern) (guard : d1963 p = 1) : d332 p ≤ (0 : Int) + d2 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1958 p = 1 := by simpa only [d1963, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9583 p hg
    simpa only [d1963, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1962 p = 1 := by simpa only [d1963, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9544 p hg
    simpa only [d1963, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9585 (p : Pattern) (guard : d1964 p = 1) : d332 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1959 p = 1 := by simpa only [d1964, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9582 p hg
    simpa only [d1964, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1963 p = 1 := by simpa only [d1964, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9584 p hg
    simpa only [d1964, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9586 (p : Pattern) (guard : d1943 p = 1) : d10 p ≤ (0 : Int) + d21 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1943, d10, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare699 p hg
    simpa only [d1943, d10, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d1943, d10, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1222 p hg
    simpa only [d1943, d10, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9587 (p : Pattern) (guard : d1947 p = 1) : d12 p ≤ (0 : Int) + d23 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1943 p = 1 := by simpa only [d1947, d12, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9586 p hg
    simpa only [d1947, d12, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d1947, d12, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9514 p hg
    simpa only [d1947, d12, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9588 (p : Pattern) (guard : d1952 p = 1) : d14 p ≤ (0 : Int) + d138 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1947 p = 1 := by simpa only [d1952, d14, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9587 p hg
    simpa only [d1952, d14, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1951 p = 1 := by simpa only [d1952, d14, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9517 p hg
    simpa only [d1952, d14, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9589 (p : Pattern) (guard : d1953 p = 1) : d15 p ≤ (0 : Int) + d138 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1948 p = 1 := by simpa only [d1953, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9509 p hg
    simpa only [d1953, d15, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1952 p = 1 := by simpa only [d1953, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9588 p hg
    simpa only [d1953, d15, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9590 (p : Pattern) (guard : d1958 p = 1) : d15 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1953 p = 1 := by simpa only [d1958, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9589 p hg
    simpa only [d1958, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1957 p = 1 := by simpa only [d1958, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9554 p hg
    simpa only [d1958, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9591 (p : Pattern) (guard : d1963 p = 1) : d332 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1958 p = 1 := by simpa only [d1963, d332, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9590 p hg
    simpa only [d1963, d332, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1962 p = 1 := by simpa only [d1963, d332, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9544 p hg
    simpa only [d1963, d332, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9592 (p : Pattern) (guard : d1962 p = 1) : d41 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1957 p = 1 := by simpa only [d1962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9542 p hg
    simpa only [d1962, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1961 p = 1 := by simpa only [d1962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9571 p hg
    simpa only [d1962, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9593 (p : Pattern) (guard : d1967 p = 1) : d333 p ≤ (0 : Int) + d2 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1962 p = 1 := by simpa only [d1967, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9592 p hg
    simpa only [d1967, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1966 p = 1 := by simpa only [d1967, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9573 p hg
    simpa only [d1967, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9594 (p : Pattern) (guard : d1968 p = 1) : d334 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1963 p = 1 := by simpa only [d1968, d334, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9591 p hg
    simpa only [d1968, d334, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1967 p = 1 := by simpa only [d1968, d334, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9593 p hg
    simpa only [d1968, d334, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9595 (p : Pattern) (guard : d1969 p = 1) : d335 p ≤ (0 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1964 p = 1 := by simpa only [d1969, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9585 p hg
    simpa only [d1969, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1968 p = 1 := by simpa only [d1969, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9594 p hg
    simpa only [d1969, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9596 (p : Pattern) (guard : d1956 p = 1) : d2 p ≤ (0 : Int) + d2 p := by
  omega
theorem compare9597 (p : Pattern) (guard : d1957 p = 1) : d52 p ≤ (0 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1952 p = 1 := by simpa only [d1957, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9552 p hg
    simpa only [d1957, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1956 p = 1 := by simpa only [d1957, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9596 p hg
    simpa only [d1957, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9598 (p : Pattern) (guard : d1958 p = 1) : d53 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1953 p = 1 := by simpa only [d1958, d53, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9589 p hg
    simpa only [d1958, d53, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1957 p = 1 := by simpa only [d1958, d53, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9597 p hg
    simpa only [d1958, d53, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9599 (p : Pattern) (guard : d1963 p = 1) : d336 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1958 p = 1 := by simpa only [d1963, d336, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9598 p hg
    simpa only [d1963, d336, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1962 p = 1 := by simpa only [d1963, d336, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9544 p hg
    simpa only [d1963, d336, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9600 (p : Pattern) (guard : d1956 p = 1) : d8 p ≤ (0 : Int) + d2 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1951 p = 1 := by simpa only [d1956, d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9569 p hg
    simpa only [d1956, d8, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1956, d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2350 p hg
    simpa only [d1956, d8, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9601 (p : Pattern) (guard : d1961 p = 1) : d52 p ≤ (0 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1956 p = 1 := by simpa only [d1961, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9600 p hg
    simpa only [d1961, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1961, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1961, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9602 (p : Pattern) (guard : d1962 p = 1) : d53 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1957 p = 1 := by simpa only [d1962, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9554 p hg
    simpa only [d1962, d53, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1961 p = 1 := by simpa only [d1962, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9601 p hg
    simpa only [d1962, d53, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9603 (p : Pattern) (guard : d1967 p = 1) : d336 p ≤ (0 : Int) + d2 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1962 p = 1 := by simpa only [d1967, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9602 p hg
    simpa only [d1967, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1966 p = 1 := by simpa only [d1967, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9573 p hg
    simpa only [d1967, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9604 (p : Pattern) (guard : d1968 p = 1) : d336 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1963 p = 1 := by simpa only [d1968, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9599 p hg
    simpa only [d1968, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1967 p = 1 := by simpa only [d1968, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9603 p hg
    simpa only [d1968, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9605 (p : Pattern) (guard : d1293 p = 1) : d10 p ≤ (0 : Int) + d21 p := by
  cases selected : p 160 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d1293, d10, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3984 p hg
    simpa only [d1293, d10, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1293, d10, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3410 p hg
    simpa only [d1293, d10, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9606 (p : Pattern) (guard : d1951 p = 1) : d12 p ≤ (0 : Int) + d23 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d1951, d12, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9605 p hg
    simpa only [d1951, d12, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1951, d12, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2790 p hg
    simpa only [d1951, d12, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9607 (p : Pattern) (guard : d1956 p = 1) : d14 p ≤ (0 : Int) + d138 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1951 p = 1 := by simpa only [d1956, d14, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9606 p hg
    simpa only [d1956, d14, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1956, d14, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2353 p hg
    simpa only [d1956, d14, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9608 (p : Pattern) (guard : d1957 p = 1) : d15 p ≤ (0 : Int) + d138 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1952 p = 1 := by simpa only [d1957, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9550 p hg
    simpa only [d1957, d15, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1956 p = 1 := by simpa only [d1957, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9607 p hg
    simpa only [d1957, d15, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9609 (p : Pattern) (guard : d1962 p = 1) : d53 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1957 p = 1 := by simpa only [d1962, d53, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9608 p hg
    simpa only [d1962, d53, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1961 p = 1 := by simpa only [d1962, d53, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9601 p hg
    simpa only [d1962, d53, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9610 (p : Pattern) (guard : d1967 p = 1) : d336 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1962 p = 1 := by simpa only [d1967, d336, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9609 p hg
    simpa only [d1967, d336, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1966 p = 1 := by simpa only [d1967, d336, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9573 p hg
    simpa only [d1967, d336, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9611 (p : Pattern) (guard : d1966 p = 1) : d62 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9571 p hg
    simpa only [d1966, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4902 p hg
    simpa only [d1966, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9612 (p : Pattern) (guard : d1971 p = 1) : d337 p ≤ (0 : Int) + d2 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9611 p hg
    simpa only [d1971, d337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1971, d337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9613 (p : Pattern) (guard : d1972 p = 1) : d338 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1967 p = 1 := by simpa only [d1972, d338, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9610 p hg
    simpa only [d1972, d338, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1971 p = 1 := by simpa only [d1972, d338, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9612 p hg
    simpa only [d1972, d338, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9614 (p : Pattern) (guard : d1973 p = 1) : d339 p ≤ (0 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1968 p = 1 := by simpa only [d1973, d339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9604 p hg
    simpa only [d1973, d339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1972 p = 1 := by simpa only [d1973, d339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9613 p hg
    simpa only [d1973, d339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9615 (p : Pattern) (guard : d1974 p = 1) : d340 p ≤ (0 : Int) + d152 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1969 p = 1 := by simpa only [d1974, d340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9595 p hg
    simpa only [d1974, d340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1973 p = 1 := by simpa only [d1974, d340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9614 p hg
    simpa only [d1974, d340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9616 (p : Pattern) (guard : d1975 p = 1) : d341 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1970 p = 1 := by simpa only [d1975, d341, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9577 p hg
    simpa only [d1975, d341, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1974 p = 1 := by simpa only [d1975, d341, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9615 p hg
    simpa only [d1975, d341, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9617 (p : Pattern) (guard : d1951 p = 1) : d39 p ≤ (0 : Int) + d2 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d1951, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9514 p hg
    simpa only [d1951, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1951, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1951, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9618 (p : Pattern) (guard : d1952 p = 1) : d40 p ≤ (0 : Int) + d138 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1947 p = 1 := by simpa only [d1952, d40, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9587 p hg
    simpa only [d1952, d40, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1951 p = 1 := by simpa only [d1952, d40, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9617 p hg
    simpa only [d1952, d40, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9619 (p : Pattern) (guard : d1956 p = 1) : d40 p ≤ (0 : Int) + d138 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1951 p = 1 := by simpa only [d1956, d40, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9606 p hg
    simpa only [d1956, d40, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1956, d40, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2377 p hg
    simpa only [d1956, d40, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9620 (p : Pattern) (guard : d1957 p = 1) : d40 p ≤ (0 : Int) + d138 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1952 p = 1 := by simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9618 p hg
    simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1956 p = 1 := by simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9619 p hg
    simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9621 (p : Pattern) (guard : d1961 p = 1) : d68 p ≤ (0 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1956 p = 1 := by simpa only [d1961, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9541 p hg
    simpa only [d1961, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1961, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1961, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9622 (p : Pattern) (guard : d1962 p = 1) : d69 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1957 p = 1 := by simpa only [d1962, d69, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9620 p hg
    simpa only [d1962, d69, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1961 p = 1 := by simpa only [d1962, d69, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9621 p hg
    simpa only [d1962, d69, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9623 (p : Pattern) (guard : d1967 p = 1) : d342 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1962 p = 1 := by simpa only [d1967, d342, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9622 p hg
    simpa only [d1967, d342, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1966 p = 1 := by simpa only [d1967, d342, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9573 p hg
    simpa only [d1967, d342, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9624 (p : Pattern) (guard : d1968 p = 1) : d343 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1963 p = 1 := by simpa only [d1968, d343, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9565 p hg
    simpa only [d1968, d343, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1967 p = 1 := by simpa only [d1968, d343, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9623 p hg
    simpa only [d1968, d343, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9625 (p : Pattern) (guard : d1969 p = 1) : d344 p ≤ (0 : Int) + d141 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1964 p = 1 := by simpa only [d1969, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9557 p hg
    simpa only [d1969, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1968 p = 1 := by simpa only [d1969, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9624 p hg
    simpa only [d1969, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9626 (p : Pattern) (guard : d1956 p = 1) : d8 p ≤ (0 : Int) + d138 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1951 p = 1 := by simpa only [d1956, d8, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9566 p hg
    simpa only [d1956, d8, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1956, d8, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2350 p hg
    simpa only [d1956, d8, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9627 (p : Pattern) (guard : d1957 p = 1) : d8 p ≤ (0 : Int) + d138 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1952 p = 1 := by simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9550 p hg
    simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1956 p = 1 := by simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9626 p hg
    simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9628 (p : Pattern) (guard : d1961 p = 1) : d15 p ≤ (0 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1956 p = 1 := by simpa only [d1961, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9600 p hg
    simpa only [d1961, d15, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1961, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1580 p hg
    simpa only [d1961, d15, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9629 (p : Pattern) (guard : d1962 p = 1) : d16 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1957 p = 1 := by simpa only [d1962, d16, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9627 p hg
    simpa only [d1962, d16, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1961 p = 1 := by simpa only [d1962, d16, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9628 p hg
    simpa only [d1962, d16, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9630 (p : Pattern) (guard : d1967 p = 1) : d328 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1962 p = 1 := by simpa only [d1967, d328, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9629 p hg
    simpa only [d1967, d328, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1966 p = 1 := by simpa only [d1967, d328, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9573 p hg
    simpa only [d1967, d328, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9631 (p : Pattern) (guard : d1968 p = 1) : d328 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1963 p = 1 := by simpa only [d1968, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9565 p hg
    simpa only [d1968, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1967 p = 1 := by simpa only [d1968, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9630 p hg
    simpa only [d1968, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9632 (p : Pattern) (guard : d1293 p = 1) : d4 p ≤ (0 : Int) + d17 p := by
  cases selected : p 160 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d1293, d4, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3976 p hg
    simpa only [d1293, d4, d17, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1293, d4, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3404 p hg
    simpa only [d1293, d4, d17, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9633 (p : Pattern) (guard : d1951 p = 1) : d6 p ≤ (0 : Int) + d19 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d1951, d6, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9632 p hg
    simpa only [d1951, d6, d19, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1951, d6, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2786 p hg
    simpa only [d1951, d6, d19, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9634 (p : Pattern) (guard : d1956 p = 1) : d8 p ≤ (0 : Int) + d135 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1951 p = 1 := by simpa only [d1956, d8, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9633 p hg
    simpa only [d1956, d8, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1956, d8, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2348 p hg
    simpa only [d1956, d8, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9635 (p : Pattern) (guard : d1957 p = 1) : d8 p ≤ (0 : Int) + d135 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1952 p = 1 := by simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9562 p hg
    simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1956 p = 1 := by simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9634 p hg
    simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9636 (p : Pattern) (guard : d1962 p = 1) : d16 p ≤ (0 : Int) + d136 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1957 p = 1 := by simpa only [d1962, d16, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9635 p hg
    simpa only [d1962, d16, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1961 p = 1 := by simpa only [d1962, d16, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9628 p hg
    simpa only [d1962, d16, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9637 (p : Pattern) (guard : d1967 p = 1) : d328 p ≤ (0 : Int) + d137 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1962 p = 1 := by simpa only [d1967, d328, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9636 p hg
    simpa only [d1967, d328, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1966 p = 1 := by simpa only [d1967, d328, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9573 p hg
    simpa only [d1967, d328, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9638 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d138 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9639 (p : Pattern) (guard : d1961 p = 1) : d68 p ≤ (0 : Int) + d138 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1956 p = 1 := by simpa only [d1961, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9619 p hg
    simpa only [d1961, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1961, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9638 p hg
    simpa only [d1961, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9640 (p : Pattern) (guard : d1966 p = 1) : d68 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9639 p hg
    simpa only [d1966, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1451 p hg
    simpa only [d1966, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9641 (p : Pattern) (guard : d1971 p = 1) : d345 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d345, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9640 p hg
    simpa only [d1971, d345, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d345, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1971, d345, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9642 (p : Pattern) (guard : d1972 p = 1) : d346 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1967 p = 1 := by simpa only [d1972, d346, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9637 p hg
    simpa only [d1972, d346, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1971 p = 1 := by simpa only [d1972, d346, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9641 p hg
    simpa only [d1972, d346, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9643 (p : Pattern) (guard : d1973 p = 1) : d347 p ≤ (0 : Int) + d141 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1968 p = 1 := by simpa only [d1973, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9631 p hg
    simpa only [d1973, d347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1972 p = 1 := by simpa only [d1973, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9642 p hg
    simpa only [d1973, d347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9644 (p : Pattern) (guard : d1974 p = 1) : d348 p ≤ (0 : Int) + d141 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1969 p = 1 := by simpa only [d1974, d348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9625 p hg
    simpa only [d1974, d348, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1973 p = 1 := by simpa only [d1974, d348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9643 p hg
    simpa only [d1974, d348, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9645 (p : Pattern) (guard : d1962 p = 1) : d15 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1957 p = 1 := by simpa only [d1962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9554 p hg
    simpa only [d1962, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1961 p = 1 := by simpa only [d1962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9628 p hg
    simpa only [d1962, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9646 (p : Pattern) (guard : d1967 p = 1) : d332 p ≤ (0 : Int) + d2 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1962 p = 1 := by simpa only [d1967, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9645 p hg
    simpa only [d1967, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1966 p = 1 := by simpa only [d1967, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9573 p hg
    simpa only [d1967, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9647 (p : Pattern) (guard : d1968 p = 1) : d332 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1963 p = 1 := by simpa only [d1968, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9591 p hg
    simpa only [d1968, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1967 p = 1 := by simpa only [d1968, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9646 p hg
    simpa only [d1968, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9648 (p : Pattern) (guard : d1962 p = 1) : d15 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1957 p = 1 := by simpa only [d1962, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9608 p hg
    simpa only [d1962, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1961 p = 1 := by simpa only [d1962, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9628 p hg
    simpa only [d1962, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9649 (p : Pattern) (guard : d1967 p = 1) : d332 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1962 p = 1 := by simpa only [d1967, d332, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9648 p hg
    simpa only [d1967, d332, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1966 p = 1 := by simpa only [d1967, d332, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9573 p hg
    simpa only [d1967, d332, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9650 (p : Pattern) (guard : d1966 p = 1) : d68 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9621 p hg
    simpa only [d1966, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1451 p hg
    simpa only [d1966, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9651 (p : Pattern) (guard : d1971 p = 1) : d345 p ≤ (0 : Int) + d2 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9650 p hg
    simpa only [d1971, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1971, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9652 (p : Pattern) (guard : d1972 p = 1) : d349 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1967 p = 1 := by simpa only [d1972, d349, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9649 p hg
    simpa only [d1972, d349, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1971 p = 1 := by simpa only [d1972, d349, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9651 p hg
    simpa only [d1972, d349, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9653 (p : Pattern) (guard : d1973 p = 1) : d350 p ≤ (0 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1968 p = 1 := by simpa only [d1973, d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9647 p hg
    simpa only [d1973, d350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1972 p = 1 := by simpa only [d1973, d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9652 p hg
    simpa only [d1973, d350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9654 (p : Pattern) (guard : d1966 p = 1) : d53 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9628 p hg
    simpa only [d1966, d53, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4893 p hg
    simpa only [d1966, d53, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9655 (p : Pattern) (guard : d1971 p = 1) : d336 p ≤ (0 : Int) + d2 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9654 p hg
    simpa only [d1971, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1971, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9656 (p : Pattern) (guard : d1972 p = 1) : d336 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1967 p = 1 := by simpa only [d1972, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9610 p hg
    simpa only [d1972, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1971 p = 1 := by simpa only [d1972, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9655 p hg
    simpa only [d1972, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9657 (p : Pattern) (guard : d1961 p = 1) : d15 p ≤ (0 : Int) + d138 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1956 p = 1 := by simpa only [d1961, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9626 p hg
    simpa only [d1961, d15, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1961, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1793 p hg
    simpa only [d1961, d15, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9658 (p : Pattern) (guard : d1966 p = 1) : d53 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d53, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9657 p hg
    simpa only [d1966, d53, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d53, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4893 p hg
    simpa only [d1966, d53, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9659 (p : Pattern) (guard : d1971 p = 1) : d336 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d336, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9658 p hg
    simpa only [d1971, d336, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d336, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1971, d336, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban32Refined
