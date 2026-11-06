/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Comparisons069
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare9800 (p : Pattern) (guard : d1957 p = 1) : d25 p ≤ (0 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1952 p = 1 := by simpa only [d1957, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9796 p hg
    simpa only [d1957, d25, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1956 p = 1 := by simpa only [d1957, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9799 p hg
    simpa only [d1957, d25, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9801 (p : Pattern) (guard : d1958 p = 1) : d26 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1953 p = 1 := by simpa only [d1958, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9797 p hg
    simpa only [d1958, d26, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1957 p = 1 := by simpa only [d1958, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9800 p hg
    simpa only [d1958, d26, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9802 (p : Pattern) (guard : d1959 p = 1) : d27 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1954 p = 1 := by simpa only [d1959, d27, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9520 p hg
    simpa only [d1959, d27, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1958 p = 1 := by simpa only [d1959, d27, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9801 p hg
    simpa only [d1959, d27, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9803 (p : Pattern) (guard : d1960 p = 1) : d28 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1955 p = 1 := by simpa only [d1960, d28, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9788 p hg
    simpa only [d1960, d28, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1959 p = 1 := by simpa only [d1960, d28, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9802 p hg
    simpa only [d1960, d28, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9804 (p : Pattern) (guard : d1943 p = 1) : d30 p ≤ (0 : Int) + d2 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1943, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare672 p hg
    simpa only [d1943, d30, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d1943, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1218 p hg
    simpa only [d1943, d30, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9805 (p : Pattern) (guard : d1944 p = 1) : d31 p ≤ (0 : Int) + d2 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1944, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9490 p hg
    simpa only [d1944, d31, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1943 p = 1 := by simpa only [d1944, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9804 p hg
    simpa only [d1944, d31, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9806 (p : Pattern) (guard : d1947 p = 1) : d32 p ≤ (0 : Int) + d2 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1943 p = 1 := by simpa only [d1947, d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9804 p hg
    simpa only [d1947, d32, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d1947, d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4473 p hg
    simpa only [d1947, d32, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9807 (p : Pattern) (guard : d1948 p = 1) : d33 p ≤ (0 : Int) + d2 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1944 p = 1 := by simpa only [d1948, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9805 p hg
    simpa only [d1948, d33, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1947 p = 1 := by simpa only [d1948, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9806 p hg
    simpa only [d1948, d33, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9808 (p : Pattern) (guard : d985 p = 1) : d29 p ≤ (0 : Int) + d2 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d985, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare660 p hg
    simpa only [d985, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d985, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3983 p hg
    simpa only [d985, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9809 (p : Pattern) (guard : d1293 p = 1) : d30 p ≤ (0 : Int) + d2 p := by
  cases selected : p 160 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d1293, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9808 p hg
    simpa only [d1293, d30, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1293, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1293, d30, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9810 (p : Pattern) (guard : d1947 p = 1) : d31 p ≤ (0 : Int) + d2 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1943 p = 1 := by simpa only [d1947, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9507 p hg
    simpa only [d1947, d31, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d1947, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9809 p hg
    simpa only [d1947, d31, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9811 (p : Pattern) (guard : d1951 p = 1) : d32 p ≤ (0 : Int) + d2 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d1951, d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9809 p hg
    simpa only [d1951, d32, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1951, d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1951, d32, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9812 (p : Pattern) (guard : d1952 p = 1) : d33 p ≤ (0 : Int) + d2 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1947 p = 1 := by simpa only [d1952, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9810 p hg
    simpa only [d1952, d33, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1951 p = 1 := by simpa only [d1952, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9811 p hg
    simpa only [d1952, d33, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9813 (p : Pattern) (guard : d1953 p = 1) : d33 p ≤ (0 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1948 p = 1 := by simpa only [d1953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9807 p hg
    simpa only [d1953, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1952 p = 1 := by simpa only [d1953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9812 p hg
    simpa only [d1953, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9814 (p : Pattern) (guard : d1957 p = 1) : d34 p ≤ (0 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1952 p = 1 := by simpa only [d1957, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9812 p hg
    simpa only [d1957, d34, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1956 p = 1 := by simpa only [d1957, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9799 p hg
    simpa only [d1957, d34, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9815 (p : Pattern) (guard : d1958 p = 1) : d35 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1953 p = 1 := by simpa only [d1958, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9813 p hg
    simpa only [d1958, d35, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1957 p = 1 := by simpa only [d1958, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9814 p hg
    simpa only [d1958, d35, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9816 (p : Pattern) (guard : d1959 p = 1) : d36 p ≤ (0 : Int) + d137 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1954 p = 1 := by simpa only [d1959, d36, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9529 p hg
    simpa only [d1959, d36, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1958 p = 1 := by simpa only [d1959, d36, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9815 p hg
    simpa only [d1959, d36, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9817 (p : Pattern) (guard : d1951 p = 1) : d18 p ≤ (0 : Int) + d2 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d1951, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9548 p hg
    simpa only [d1951, d18, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1951, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2800 p hg
    simpa only [d1951, d18, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9818 (p : Pattern) (guard : d1956 p = 1) : d20 p ≤ (0 : Int) + d2 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1951 p = 1 := by simpa only [d1956, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9817 p hg
    simpa only [d1956, d20, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1956, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2360 p hg
    simpa only [d1956, d20, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9819 (p : Pattern) (guard : d1957 p = 1) : d20 p ≤ (0 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1952 p = 1 := by simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9796 p hg
    simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1956 p = 1 := by simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9818 p hg
    simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9820 (p : Pattern) (guard : d1961 p = 1) : d25 p ≤ (0 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1956 p = 1 := by simpa only [d1961, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9818 p hg
    simpa only [d1961, d25, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1961, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1592 p hg
    simpa only [d1961, d25, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9821 (p : Pattern) (guard : d1962 p = 1) : d26 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1957 p = 1 := by simpa only [d1962, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9819 p hg
    simpa only [d1962, d26, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1961 p = 1 := by simpa only [d1962, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9820 p hg
    simpa only [d1962, d26, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9822 (p : Pattern) (guard : d1963 p = 1) : d43 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1958 p = 1 := by simpa only [d1963, d43, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9543 p hg
    simpa only [d1963, d43, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1962 p = 1 := by simpa only [d1963, d43, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9821 p hg
    simpa only [d1963, d43, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9823 (p : Pattern) (guard : d1964 p = 1) : d44 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1959 p = 1 := by simpa only [d1964, d44, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9816 p hg
    simpa only [d1964, d44, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1963 p = 1 := by simpa only [d1964, d44, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9822 p hg
    simpa only [d1964, d44, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9824 (p : Pattern) (guard : d1965 p = 1) : d45 p ≤ (0 : Int) + d141 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1960 p = 1 := by simpa only [d1965, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9803 p hg
    simpa only [d1965, d45, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1964 p = 1 := by simpa only [d1965, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9823 p hg
    simpa only [d1965, d45, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9825 (p : Pattern) (guard : d1953 p = 1) : d8 p ≤ (0 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1948 p = 1 := by simpa only [d1953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9512 p hg
    simpa only [d1953, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1952 p = 1 := by simpa only [d1953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9552 p hg
    simpa only [d1953, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9826 (p : Pattern) (guard : d1958 p = 1) : d16 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1953 p = 1 := by simpa only [d1958, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9825 p hg
    simpa only [d1958, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1957 p = 1 := by simpa only [d1958, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9554 p hg
    simpa only [d1958, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9827 (p : Pattern) (guard : d1959 p = 1) : d16 p ≤ (0 : Int) + d137 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1954 p = 1 := by simpa only [d1959, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9529 p hg
    simpa only [d1959, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1958 p = 1 := by simpa only [d1959, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9826 p hg
    simpa only [d1959, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9828 (p : Pattern) (guard : d1963 p = 1) : d27 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1958 p = 1 := by simpa only [d1963, d27, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9555 p hg
    simpa only [d1963, d27, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1962 p = 1 := by simpa only [d1963, d27, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9821 p hg
    simpa only [d1963, d27, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9829 (p : Pattern) (guard : d1964 p = 1) : d28 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1959 p = 1 := by simpa only [d1964, d28, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9827 p hg
    simpa only [d1964, d28, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1963 p = 1 := by simpa only [d1964, d28, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9828 p hg
    simpa only [d1964, d28, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9830 (p : Pattern) (guard : d1951 p = 1) : d31 p ≤ (0 : Int) + d2 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d1951, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9548 p hg
    simpa only [d1951, d31, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1951, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6635 p hg
    simpa only [d1951, d31, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9831 (p : Pattern) (guard : d1956 p = 1) : d33 p ≤ (0 : Int) + d2 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1951 p = 1 := by simpa only [d1956, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9830 p hg
    simpa only [d1956, d33, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1956, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2370 p hg
    simpa only [d1956, d33, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9832 (p : Pattern) (guard : d1957 p = 1) : d33 p ≤ (0 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1952 p = 1 := by simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9812 p hg
    simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1956 p = 1 := by simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9831 p hg
    simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9833 (p : Pattern) (guard : d1961 p = 1) : d34 p ≤ (0 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1956 p = 1 := by simpa only [d1961, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9831 p hg
    simpa only [d1961, d34, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1961, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1592 p hg
    simpa only [d1961, d34, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9834 (p : Pattern) (guard : d1962 p = 1) : d35 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1957 p = 1 := by simpa only [d1962, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9832 p hg
    simpa only [d1962, d35, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1961 p = 1 := by simpa only [d1962, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9833 p hg
    simpa only [d1962, d35, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9835 (p : Pattern) (guard : d1963 p = 1) : d36 p ≤ (0 : Int) + d137 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1958 p = 1 := by simpa only [d1963, d36, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9564 p hg
    simpa only [d1963, d36, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1962 p = 1 := by simpa only [d1963, d36, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9834 p hg
    simpa only [d1963, d36, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9836 (p : Pattern) (guard : d1961 p = 1) : d20 p ≤ (0 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1956 p = 1 := by simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9818 p hg
    simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1590 p hg
    simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9837 (p : Pattern) (guard : d1966 p = 1) : d26 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9836 p hg
    simpa only [d1966, d26, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare855 p hg
    simpa only [d1966, d26, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9838 (p : Pattern) (guard : d1967 p = 1) : d43 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1962 p = 1 := by simpa only [d1967, d43, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9572 p hg
    simpa only [d1967, d43, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1966 p = 1 := by simpa only [d1967, d43, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9837 p hg
    simpa only [d1967, d43, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9839 (p : Pattern) (guard : d1968 p = 1) : d44 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1963 p = 1 := by simpa only [d1968, d44, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9835 p hg
    simpa only [d1968, d44, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1967 p = 1 := by simpa only [d1968, d44, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9838 p hg
    simpa only [d1968, d44, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9840 (p : Pattern) (guard : d1969 p = 1) : d45 p ≤ (0 : Int) + d141 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1964 p = 1 := by simpa only [d1969, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9829 p hg
    simpa only [d1969, d45, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1968 p = 1 := by simpa only [d1969, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9839 p hg
    simpa only [d1969, d45, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9841 (p : Pattern) (guard : d1970 p = 1) : d45 p ≤ (0 : Int) + d141 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1965 p = 1 := by simpa only [d1970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9824 p hg
    simpa only [d1970, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1969 p = 1 := by simpa only [d1970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9840 p hg
    simpa only [d1970, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9842 (p : Pattern) (guard : d1959 p = 1) : d15 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1954 p = 1 := by simpa only [d1959, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9581 p hg
    simpa only [d1959, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1958 p = 1 := by simpa only [d1959, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9583 p hg
    simpa only [d1959, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9843 (p : Pattern) (guard : d1962 p = 1) : d25 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1957 p = 1 := by simpa only [d1962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9800 p hg
    simpa only [d1962, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1961 p = 1 := by simpa only [d1962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9820 p hg
    simpa only [d1962, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9844 (p : Pattern) (guard : d1963 p = 1) : d46 p ≤ (0 : Int) + d2 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1958 p = 1 := by simpa only [d1963, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9583 p hg
    simpa only [d1963, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1962 p = 1 := by simpa only [d1963, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9843 p hg
    simpa only [d1963, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9845 (p : Pattern) (guard : d1964 p = 1) : d47 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1959 p = 1 := by simpa only [d1964, d47, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9842 p hg
    simpa only [d1964, d47, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1963 p = 1 := by simpa only [d1964, d47, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9844 p hg
    simpa only [d1964, d47, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9846 (p : Pattern) (guard : d1962 p = 1) : d34 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1957 p = 1 := by simpa only [d1962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9814 p hg
    simpa only [d1962, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1961 p = 1 := by simpa only [d1962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9833 p hg
    simpa only [d1962, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9847 (p : Pattern) (guard : d1963 p = 1) : d48 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1958 p = 1 := by simpa only [d1963, d48, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9590 p hg
    simpa only [d1963, d48, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1962 p = 1 := by simpa only [d1963, d48, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9846 p hg
    simpa only [d1963, d48, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9848 (p : Pattern) (guard : d1966 p = 1) : d25 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9820 p hg
    simpa only [d1966, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare855 p hg
    simpa only [d1966, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9849 (p : Pattern) (guard : d1967 p = 1) : d49 p ≤ (0 : Int) + d2 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1962 p = 1 := by simpa only [d1967, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9592 p hg
    simpa only [d1967, d49, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1966 p = 1 := by simpa only [d1967, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9848 p hg
    simpa only [d1967, d49, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9850 (p : Pattern) (guard : d1968 p = 1) : d50 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1963 p = 1 := by simpa only [d1968, d50, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9847 p hg
    simpa only [d1968, d50, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1967 p = 1 := by simpa only [d1968, d50, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9849 p hg
    simpa only [d1968, d50, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9851 (p : Pattern) (guard : d1969 p = 1) : d51 p ≤ (0 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1964 p = 1 := by simpa only [d1969, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9845 p hg
    simpa only [d1969, d51, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1968 p = 1 := by simpa only [d1969, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9850 p hg
    simpa only [d1969, d51, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9852 (p : Pattern) (guard : d1963 p = 1) : d53 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1958 p = 1 := by simpa only [d1963, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9598 p hg
    simpa only [d1963, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1962 p = 1 := by simpa only [d1963, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9602 p hg
    simpa only [d1963, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9853 (p : Pattern) (guard : d1966 p = 1) : d55 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9820 p hg
    simpa only [d1966, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4895 p hg
    simpa only [d1966, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9854 (p : Pattern) (guard : d1967 p = 1) : d56 p ≤ (0 : Int) + d2 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1962 p = 1 := by simpa only [d1967, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9602 p hg
    simpa only [d1967, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1966 p = 1 := by simpa only [d1967, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9853 p hg
    simpa only [d1967, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9855 (p : Pattern) (guard : d1968 p = 1) : d57 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1963 p = 1 := by simpa only [d1968, d57, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9852 p hg
    simpa only [d1968, d57, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1967 p = 1 := by simpa only [d1968, d57, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9854 p hg
    simpa only [d1968, d57, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9856 (p : Pattern) (guard : d1966 p = 1) : d59 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9833 p hg
    simpa only [d1966, d59, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4899 p hg
    simpa only [d1966, d59, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9857 (p : Pattern) (guard : d1967 p = 1) : d60 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1962 p = 1 := by simpa only [d1967, d60, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9609 p hg
    simpa only [d1967, d60, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1966 p = 1 := by simpa only [d1967, d60, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9856 p hg
    simpa only [d1967, d60, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9858 (p : Pattern) (guard : d1971 p = 1) : d63 p ≤ (0 : Int) + d2 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9611 p hg
    simpa only [d1971, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare865 p hg
    simpa only [d1971, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9859 (p : Pattern) (guard : d1972 p = 1) : d64 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1967 p = 1 := by simpa only [d1972, d64, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9857 p hg
    simpa only [d1972, d64, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1971 p = 1 := by simpa only [d1972, d64, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9858 p hg
    simpa only [d1972, d64, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9860 (p : Pattern) (guard : d1973 p = 1) : d65 p ≤ (0 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1968 p = 1 := by simpa only [d1973, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9855 p hg
    simpa only [d1973, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1972 p = 1 := by simpa only [d1973, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9859 p hg
    simpa only [d1973, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9861 (p : Pattern) (guard : d1974 p = 1) : d66 p ≤ (0 : Int) + d152 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1969 p = 1 := by simpa only [d1974, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9851 p hg
    simpa only [d1974, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1973 p = 1 := by simpa only [d1974, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9860 p hg
    simpa only [d1974, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9862 (p : Pattern) (guard : d1975 p = 1) : d67 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1970 p = 1 := by simpa only [d1975, d67, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9841 p hg
    simpa only [d1975, d67, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1974 p = 1 := by simpa only [d1975, d67, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9861 p hg
    simpa only [d1975, d67, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9863 (p : Pattern) (guard : d1963 p = 1) : d27 p ≤ (0 : Int) + d137 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1958 p = 1 := by simpa only [d1963, d27, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9564 p hg
    simpa only [d1963, d27, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1962 p = 1 := by simpa only [d1963, d27, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9821 p hg
    simpa only [d1963, d27, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9864 (p : Pattern) (guard : d1961 p = 1) : d24 p ≤ (0 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1956 p = 1 := by simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9799 p hg
    simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1592 p hg
    simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9865 (p : Pattern) (guard : d1966 p = 1) : d71 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9864 p hg
    simpa only [d1966, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare882 p hg
    simpa only [d1966, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9866 (p : Pattern) (guard : d1967 p = 1) : d72 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1962 p = 1 := by simpa only [d1967, d72, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9622 p hg
    simpa only [d1967, d72, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1966 p = 1 := by simpa only [d1967, d72, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9865 p hg
    simpa only [d1967, d72, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9867 (p : Pattern) (guard : d1968 p = 1) : d73 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1963 p = 1 := by simpa only [d1968, d73, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9863 p hg
    simpa only [d1968, d73, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1967 p = 1 := by simpa only [d1968, d73, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9866 p hg
    simpa only [d1968, d73, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9868 (p : Pattern) (guard : d1969 p = 1) : d74 p ≤ (0 : Int) + d141 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1964 p = 1 := by simpa only [d1969, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9829 p hg
    simpa only [d1969, d74, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1968 p = 1 := by simpa only [d1969, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9867 p hg
    simpa only [d1969, d74, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9869 (p : Pattern) (guard : d1957 p = 1) : d8 p ≤ (0 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1952 p = 1 := by simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9552 p hg
    simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1956 p = 1 := by simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9600 p hg
    simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9870 (p : Pattern) (guard : d1962 p = 1) : d16 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1957 p = 1 := by simpa only [d1962, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9869 p hg
    simpa only [d1962, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1961 p = 1 := by simpa only [d1962, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9628 p hg
    simpa only [d1962, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9871 (p : Pattern) (guard : d1963 p = 1) : d16 p ≤ (0 : Int) + d137 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1958 p = 1 := by simpa only [d1963, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9564 p hg
    simpa only [d1963, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1962 p = 1 := by simpa only [d1963, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9870 p hg
    simpa only [d1963, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9872 (p : Pattern) (guard : d1967 p = 1) : d27 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1962 p = 1 := by simpa only [d1967, d27, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9629 p hg
    simpa only [d1967, d27, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1966 p = 1 := by simpa only [d1967, d27, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9837 p hg
    simpa only [d1967, d27, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9873 (p : Pattern) (guard : d1968 p = 1) : d28 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1963 p = 1 := by simpa only [d1968, d28, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9871 p hg
    simpa only [d1968, d28, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1967 p = 1 := by simpa only [d1968, d28, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9872 p hg
    simpa only [d1968, d28, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9874 (p : Pattern) (guard : d1967 p = 1) : d27 p ≤ (0 : Int) + d137 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1962 p = 1 := by simpa only [d1967, d27, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9636 p hg
    simpa only [d1967, d27, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1966 p = 1 := by simpa only [d1967, d27, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9837 p hg
    simpa only [d1967, d27, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9875 (p : Pattern) (guard : d1971 p = 1) : d75 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d75, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9640 p hg
    simpa only [d1971, d75, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d75, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare882 p hg
    simpa only [d1971, d75, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9876 (p : Pattern) (guard : d1972 p = 1) : d76 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1967 p = 1 := by simpa only [d1972, d76, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9874 p hg
    simpa only [d1972, d76, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1971 p = 1 := by simpa only [d1972, d76, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9875 p hg
    simpa only [d1972, d76, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9877 (p : Pattern) (guard : d1973 p = 1) : d77 p ≤ (0 : Int) + d141 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1968 p = 1 := by simpa only [d1973, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9873 p hg
    simpa only [d1973, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1972 p = 1 := by simpa only [d1973, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9876 p hg
    simpa only [d1973, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9878 (p : Pattern) (guard : d1974 p = 1) : d78 p ≤ (0 : Int) + d141 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1969 p = 1 := by simpa only [d1974, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9868 p hg
    simpa only [d1974, d78, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1973 p = 1 := by simpa only [d1974, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9877 p hg
    simpa only [d1974, d78, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9879 (p : Pattern) (guard : d1963 p = 1) : d15 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1958 p = 1 := by simpa only [d1963, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9590 p hg
    simpa only [d1963, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1962 p = 1 := by simpa only [d1963, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9645 p hg
    simpa only [d1963, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9880 (p : Pattern) (guard : d1967 p = 1) : d46 p ≤ (0 : Int) + d2 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1962 p = 1 := by simpa only [d1967, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9645 p hg
    simpa only [d1967, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1966 p = 1 := by simpa only [d1967, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9848 p hg
    simpa only [d1967, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9881 (p : Pattern) (guard : d1968 p = 1) : d47 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1963 p = 1 := by simpa only [d1968, d47, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9879 p hg
    simpa only [d1968, d47, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1967 p = 1 := by simpa only [d1968, d47, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9880 p hg
    simpa only [d1968, d47, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9882 (p : Pattern) (guard : d1967 p = 1) : d46 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1962 p = 1 := by simpa only [d1967, d46, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9648 p hg
    simpa only [d1967, d46, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1966 p = 1 := by simpa only [d1967, d46, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9848 p hg
    simpa only [d1967, d46, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9883 (p : Pattern) (guard : d1971 p = 1) : d75 p ≤ (0 : Int) + d2 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9650 p hg
    simpa only [d1971, d75, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare882 p hg
    simpa only [d1971, d75, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9884 (p : Pattern) (guard : d1972 p = 1) : d79 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1967 p = 1 := by simpa only [d1972, d79, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9882 p hg
    simpa only [d1972, d79, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1971 p = 1 := by simpa only [d1972, d79, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9883 p hg
    simpa only [d1972, d79, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9885 (p : Pattern) (guard : d1973 p = 1) : d80 p ≤ (0 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1968 p = 1 := by simpa only [d1973, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9881 p hg
    simpa only [d1973, d80, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1972 p = 1 := by simpa only [d1973, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9884 p hg
    simpa only [d1973, d80, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9886 (p : Pattern) (guard : d1967 p = 1) : d53 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1962 p = 1 := by simpa only [d1967, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9609 p hg
    simpa only [d1967, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1966 p = 1 := by simpa only [d1967, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9654 p hg
    simpa only [d1967, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9887 (p : Pattern) (guard : d1971 p = 1) : d56 p ≤ (0 : Int) + d2 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9654 p hg
    simpa only [d1971, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare865 p hg
    simpa only [d1971, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9888 (p : Pattern) (guard : d1972 p = 1) : d57 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1967 p = 1 := by simpa only [d1972, d57, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9886 p hg
    simpa only [d1972, d57, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1971 p = 1 := by simpa only [d1972, d57, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9887 p hg
    simpa only [d1972, d57, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9889 (p : Pattern) (guard : d1971 p = 1) : d56 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d56, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9658 p hg
    simpa only [d1971, d56, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d56, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare865 p hg
    simpa only [d1971, d56, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9890 (p : Pattern) (guard : d1976 p = 1) : d81 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1971 p = 1 := by simpa only [d1976, d81, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9889 p hg
    simpa only [d1976, d81, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1976, d81, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1140 p hg
    simpa only [d1976, d81, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9891 (p : Pattern) (guard : d1977 p = 1) : d82 p ≤ (0 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1972 p = 1 := by simpa only [d1977, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9888 p hg
    simpa only [d1977, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1976 p = 1 := by simpa only [d1977, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9890 p hg
    simpa only [d1977, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9892 (p : Pattern) (guard : d1978 p = 1) : d83 p ≤ (0 : Int) + d152 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1973 p = 1 := by simpa only [d1978, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9885 p hg
    simpa only [d1978, d83, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1977 p = 1 := by simpa only [d1978, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9891 p hg
    simpa only [d1978, d83, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9893 (p : Pattern) (guard : d1979 p = 1) : d84 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1974 p = 1 := by simpa only [d1979, d84, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9878 p hg
    simpa only [d1979, d84, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1978 p = 1 := by simpa only [d1979, d84, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9892 p hg
    simpa only [d1979, d84, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9894 (p : Pattern) (guard : d1980 p = 1) : d85 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1975 p = 1 := by simpa only [d1980, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9862 p hg
    simpa only [d1980, d85, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1979 p = 1 := by simpa only [d1980, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9893 p hg
    simpa only [d1980, d85, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9895 (p : Pattern) (guard : d1962 p = 1) : d86 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1957 p = 1 := by simpa only [d1962, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9869 p hg
    simpa only [d1962, d86, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1961 p = 1 := by simpa only [d1962, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9601 p hg
    simpa only [d1962, d86, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9896 (p : Pattern) (guard : d1963 p = 1) : d86 p ≤ (0 : Int) + d137 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1958 p = 1 := by simpa only [d1963, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9665 p hg
    simpa only [d1963, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1962 p = 1 := by simpa only [d1963, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9895 p hg
    simpa only [d1963, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9897 (p : Pattern) (guard : d1966 p = 1) : d87 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9836 p hg
    simpa only [d1966, d87, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4895 p hg
    simpa only [d1966, d87, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9898 (p : Pattern) (guard : d1967 p = 1) : d88 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1962 p = 1 := by simpa only [d1967, d88, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9667 p hg
    simpa only [d1967, d88, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1966 p = 1 := by simpa only [d1967, d88, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9897 p hg
    simpa only [d1967, d88, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9899 (p : Pattern) (guard : d1968 p = 1) : d89 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1963 p = 1 := by simpa only [d1968, d89, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9896 p hg
    simpa only [d1968, d89, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1967 p = 1 := by simpa only [d1968, d89, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9898 p hg
    simpa only [d1968, d89, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9900 (p : Pattern) (guard : d1961 p = 1) : d33 p ≤ (0 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1956 p = 1 := by simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9831 p hg
    simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1597 p hg
    simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9901 (p : Pattern) (guard : d1966 p = 1) : d90 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d90, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9900 p hg
    simpa only [d1966, d90, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d90, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4899 p hg
    simpa only [d1966, d90, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9902 (p : Pattern) (guard : d1967 p = 1) : d91 p ≤ (0 : Int) + d137 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1962 p = 1 := by simpa only [d1967, d91, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9670 p hg
    simpa only [d1967, d91, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1966 p = 1 := by simpa only [d1967, d91, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9901 p hg
    simpa only [d1967, d91, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9903 (p : Pattern) (guard : d1971 p = 1) : d93 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d93, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9673 p hg
    simpa only [d1971, d93, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d93, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare896 p hg
    simpa only [d1971, d93, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9904 (p : Pattern) (guard : d1972 p = 1) : d94 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1967 p = 1 := by simpa only [d1972, d94, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9902 p hg
    simpa only [d1972, d94, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1971 p = 1 := by simpa only [d1972, d94, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9903 p hg
    simpa only [d1972, d94, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9905 (p : Pattern) (guard : d1973 p = 1) : d95 p ≤ (0 : Int) + d141 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1968 p = 1 := by simpa only [d1973, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9899 p hg
    simpa only [d1973, d95, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1972 p = 1 := by simpa only [d1973, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9904 p hg
    simpa only [d1973, d95, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9906 (p : Pattern) (guard : d1974 p = 1) : d96 p ≤ (0 : Int) + d141 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1969 p = 1 := by simpa only [d1974, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9840 p hg
    simpa only [d1974, d96, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1973 p = 1 := by simpa only [d1974, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9905 p hg
    simpa only [d1974, d96, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9907 (p : Pattern) (guard : d1963 p = 1) : d98 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1958 p = 1 := by simpa only [d1963, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9680 p hg
    simpa only [d1963, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1962 p = 1 := by simpa only [d1963, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9684 p hg
    simpa only [d1963, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9908 (p : Pattern) (guard : d1967 p = 1) : d99 p ≤ (0 : Int) + d2 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1962 p = 1 := by simpa only [d1967, d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9684 p hg
    simpa only [d1967, d99, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1966 p = 1 := by simpa only [d1967, d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9865 p hg
    simpa only [d1967, d99, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9909 (p : Pattern) (guard : d1968 p = 1) : d100 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1963 p = 1 := by simpa only [d1968, d100, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9907 p hg
    simpa only [d1968, d100, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1967 p = 1 := by simpa only [d1968, d100, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9908 p hg
    simpa only [d1968, d100, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9910 (p : Pattern) (guard : d1967 p = 1) : d99 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1962 p = 1 := by simpa only [d1967, d99, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9688 p hg
    simpa only [d1967, d99, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1966 p = 1 := by simpa only [d1967, d99, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9865 p hg
    simpa only [d1967, d99, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9911 (p : Pattern) (guard : d1971 p = 1) : d72 p ≤ (0 : Int) + d2 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9691 p hg
    simpa only [d1971, d72, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare877 p hg
    simpa only [d1971, d72, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9912 (p : Pattern) (guard : d1972 p = 1) : d101 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1967 p = 1 := by simpa only [d1972, d101, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9910 p hg
    simpa only [d1972, d101, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1971 p = 1 := by simpa only [d1972, d101, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9911 p hg
    simpa only [d1972, d101, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9913 (p : Pattern) (guard : d1973 p = 1) : d102 p ≤ (0 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1968 p = 1 := by simpa only [d1973, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9909 p hg
    simpa only [d1973, d102, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1972 p = 1 := by simpa only [d1973, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9912 p hg
    simpa only [d1973, d102, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9914 (p : Pattern) (guard : d1967 p = 1) : d98 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1962 p = 1 := by simpa only [d1967, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9688 p hg
    simpa only [d1967, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1966 p = 1 := by simpa only [d1967, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9696 p hg
    simpa only [d1967, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9915 (p : Pattern) (guard : d1971 p = 1) : d99 p ≤ (0 : Int) + d2 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9696 p hg
    simpa only [d1971, d99, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare877 p hg
    simpa only [d1971, d99, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9916 (p : Pattern) (guard : d1972 p = 1) : d100 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1967 p = 1 := by simpa only [d1972, d100, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9914 p hg
    simpa only [d1972, d100, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1971 p = 1 := by simpa only [d1972, d100, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9915 p hg
    simpa only [d1972, d100, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9917 (p : Pattern) (guard : d1971 p = 1) : d99 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d99, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9700 p hg
    simpa only [d1971, d99, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d99, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare877 p hg
    simpa only [d1971, d99, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9918 (p : Pattern) (guard : d1976 p = 1) : d101 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1971 p = 1 := by simpa only [d1976, d101, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9917 p hg
    simpa only [d1976, d101, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1976, d101, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1162 p hg
    simpa only [d1976, d101, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9919 (p : Pattern) (guard : d1977 p = 1) : d102 p ≤ (0 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1972 p = 1 := by simpa only [d1977, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9916 p hg
    simpa only [d1977, d102, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1976 p = 1 := by simpa only [d1977, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9918 p hg
    simpa only [d1977, d102, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9920 (p : Pattern) (guard : d1978 p = 1) : d102 p ≤ (0 : Int) + d152 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1973 p = 1 := by simpa only [d1978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9913 p hg
    simpa only [d1978, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1977 p = 1 := by simpa only [d1978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9919 p hg
    simpa only [d1978, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9921 (p : Pattern) (guard : d1979 p = 1) : d103 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1974 p = 1 := by simpa only [d1979, d103, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9906 p hg
    simpa only [d1979, d103, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1978 p = 1 := by simpa only [d1979, d103, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9920 p hg
    simpa only [d1979, d103, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9922 (p : Pattern) (guard : d1961 p = 1) : d8 p ≤ (0 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1956 p = 1 := by simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9600 p hg
    simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1583 p hg
    simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9923 (p : Pattern) (guard : d1966 p = 1) : d86 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9922 p hg
    simpa only [d1966, d86, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4893 p hg
    simpa only [d1966, d86, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9924 (p : Pattern) (guard : d1967 p = 1) : d86 p ≤ (0 : Int) + d137 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1962 p = 1 := by simpa only [d1967, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9670 p hg
    simpa only [d1967, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1966 p = 1 := by simpa only [d1967, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9923 p hg
    simpa only [d1967, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9925 (p : Pattern) (guard : d1971 p = 1) : d88 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d88, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9707 p hg
    simpa only [d1971, d88, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d88, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare896 p hg
    simpa only [d1971, d88, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9926 (p : Pattern) (guard : d1972 p = 1) : d89 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1967 p = 1 := by simpa only [d1972, d89, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9924 p hg
    simpa only [d1972, d89, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1971 p = 1 := by simpa only [d1972, d89, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9925 p hg
    simpa only [d1972, d89, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9927 (p : Pattern) (guard : d1971 p = 1) : d88 p ≤ (0 : Int) + d137 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d88, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9711 p hg
    simpa only [d1971, d88, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d88, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare896 p hg
    simpa only [d1971, d88, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9928 (p : Pattern) (guard : d0 p = 1) : d75 p ≤ (0 : Int) + d140 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9929 (p : Pattern) (guard : d1976 p = 1) : d104 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1971 p = 1 := by simpa only [d1976, d104, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9927 p hg
    simpa only [d1976, d104, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1976, d104, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9928 p hg
    simpa only [d1976, d104, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9930 (p : Pattern) (guard : d1977 p = 1) : d105 p ≤ (0 : Int) + d141 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1972 p = 1 := by simpa only [d1977, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9926 p hg
    simpa only [d1977, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1976 p = 1 := by simpa only [d1977, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9929 p hg
    simpa only [d1977, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9931 (p : Pattern) (guard : d1978 p = 1) : d106 p ≤ (0 : Int) + d141 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1973 p = 1 := by simpa only [d1978, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9877 p hg
    simpa only [d1978, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1977 p = 1 := by simpa only [d1978, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9930 p hg
    simpa only [d1978, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9932 (p : Pattern) (guard : d1976 p = 1) : d107 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1971 p = 1 := by simpa only [d1976, d107, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9917 p hg
    simpa only [d1976, d107, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1976, d107, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1976, d107, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9933 (p : Pattern) (guard : d1977 p = 1) : d108 p ≤ (0 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1972 p = 1 := by simpa only [d1977, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9916 p hg
    simpa only [d1977, d108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1976 p = 1 := by simpa only [d1977, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9932 p hg
    simpa only [d1977, d108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9934 (p : Pattern) (guard : d1971 p = 1) : d97 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9720 p hg
    simpa only [d1971, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare919 p hg
    simpa only [d1971, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9935 (p : Pattern) (guard : d1976 p = 1) : d110 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1971 p = 1 := by simpa only [d1976, d110, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9934 p hg
    simpa only [d1976, d110, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1976, d110, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare832 p hg
    simpa only [d1976, d110, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9936 (p : Pattern) (guard : d0 p = 1) : d111 p ≤ (0 : Int) + d152 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9937 (p : Pattern) (guard : d1981 p = 1) : d112 p ≤ (0 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1976 p = 1 := by simpa only [d1981, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9935 p hg
    simpa only [d1981, d112, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1981, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9936 p hg
    simpa only [d1981, d112, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9938 (p : Pattern) (guard : d1982 p = 1) : d113 p ≤ (0 : Int) + d152 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1977 p = 1 := by simpa only [d1982, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9933 p hg
    simpa only [d1982, d113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1981 p = 1 := by simpa only [d1982, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9937 p hg
    simpa only [d1982, d113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9939 (p : Pattern) (guard : d1983 p = 1) : d114 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1978 p = 1 := by simpa only [d1983, d114, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9931 p hg
    simpa only [d1983, d114, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1982 p = 1 := by simpa only [d1983, d114, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9938 p hg
    simpa only [d1983, d114, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban32Refined
