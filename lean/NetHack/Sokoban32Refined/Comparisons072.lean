/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Comparisons071
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare10080 (p : Pattern) (guard : d1954 p = 1) : d389 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1949 p = 1 := by simpa only [d1954, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9786 p hg
    simpa only [d1954, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1953 p = 1 := by simpa only [d1954, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10079 p hg
    simpa only [d1954, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10081 (p : Pattern) (guard : d1955 p = 1) : d389 p ≤ (0 : Int) + d137 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1950 p = 1 := by simpa only [d1955, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10078 p hg
    simpa only [d1955, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1954 p = 1 := by simpa only [d1955, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10080 p hg
    simpa only [d1955, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10082 (p : Pattern) (guard : d1954 p = 1) : d389 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1949 p = 1 := by simpa only [d1954, d389, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9510 p hg
    simpa only [d1954, d389, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1953 p = 1 := by simpa only [d1954, d389, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10079 p hg
    simpa only [d1954, d389, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10083 (p : Pattern) (guard : d1957 p = 1) : d2 p ≤ (0 : Int) + d2 p := by
  omega
theorem compare10084 (p : Pattern) (guard : d1958 p = 1) : d390 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1953 p = 1 := by simpa only [d1958, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9797 p hg
    simpa only [d1958, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1957 p = 1 := by simpa only [d1958, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10083 p hg
    simpa only [d1958, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10085 (p : Pattern) (guard : d1959 p = 1) : d391 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1954 p = 1 := by simpa only [d1959, d391, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10082 p hg
    simpa only [d1959, d391, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1958 p = 1 := by simpa only [d1959, d391, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10084 p hg
    simpa only [d1959, d391, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10086 (p : Pattern) (guard : d1960 p = 1) : d392 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1955 p = 1 := by simpa only [d1960, d392, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10081 p hg
    simpa only [d1960, d392, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1959 p = 1 := by simpa only [d1960, d392, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10085 p hg
    simpa only [d1960, d392, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10087 (p : Pattern) (guard : d1954 p = 1) : d389 p ≤ (0 : Int) + d136 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1949 p = 1 := by simpa only [d1954, d389, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9528 p hg
    simpa only [d1954, d389, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1953 p = 1 := by simpa only [d1954, d389, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10079 p hg
    simpa only [d1954, d389, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10088 (p : Pattern) (guard : d1958 p = 1) : d393 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1953 p = 1 := by simpa only [d1958, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9813 p hg
    simpa only [d1958, d393, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1957 p = 1 := by simpa only [d1958, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10083 p hg
    simpa only [d1958, d393, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10089 (p : Pattern) (guard : d1959 p = 1) : d394 p ≤ (0 : Int) + d137 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1954 p = 1 := by simpa only [d1959, d394, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10087 p hg
    simpa only [d1959, d394, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1958 p = 1 := by simpa only [d1959, d394, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10088 p hg
    simpa only [d1959, d394, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10090 (p : Pattern) (guard : d1958 p = 1) : d395 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1953 p = 1 := by simpa only [d1958, d395, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9537 p hg
    simpa only [d1958, d395, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1957 p = 1 := by simpa only [d1958, d395, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10083 p hg
    simpa only [d1958, d395, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10091 (p : Pattern) (guard : d1961 p = 1) : d2 p ≤ (0 : Int) + d2 p := by
  omega
theorem compare10092 (p : Pattern) (guard : d1962 p = 1) : d390 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1957 p = 1 := by simpa only [d1962, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9819 p hg
    simpa only [d1962, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1961 p = 1 := by simpa only [d1962, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10091 p hg
    simpa only [d1962, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10093 (p : Pattern) (guard : d1963 p = 1) : d396 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1958 p = 1 := by simpa only [d1963, d396, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10090 p hg
    simpa only [d1963, d396, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1962 p = 1 := by simpa only [d1963, d396, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10092 p hg
    simpa only [d1963, d396, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10094 (p : Pattern) (guard : d1964 p = 1) : d397 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1959 p = 1 := by simpa only [d1964, d397, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d1964, d397, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1963 p = 1 := by simpa only [d1964, d397, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10093 p hg
    simpa only [d1964, d397, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10095 (p : Pattern) (guard : d1965 p = 1) : d398 p ≤ (0 : Int) + d141 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1960 p = 1 := by simpa only [d1965, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10086 p hg
    simpa only [d1965, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1964 p = 1 := by simpa only [d1965, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10094 p hg
    simpa only [d1965, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10096 (p : Pattern) (guard : d1958 p = 1) : d389 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1953 p = 1 := by simpa only [d1958, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9825 p hg
    simpa only [d1958, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1957 p = 1 := by simpa only [d1958, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10083 p hg
    simpa only [d1958, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10097 (p : Pattern) (guard : d1959 p = 1) : d389 p ≤ (0 : Int) + d137 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1954 p = 1 := by simpa only [d1959, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10087 p hg
    simpa only [d1959, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1958 p = 1 := by simpa only [d1959, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10096 p hg
    simpa only [d1959, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10098 (p : Pattern) (guard : d1958 p = 1) : d389 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1953 p = 1 := by simpa only [d1958, d389, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9551 p hg
    simpa only [d1958, d389, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1957 p = 1 := by simpa only [d1958, d389, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10083 p hg
    simpa only [d1958, d389, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10099 (p : Pattern) (guard : d1963 p = 1) : d391 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1958 p = 1 := by simpa only [d1963, d391, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10098 p hg
    simpa only [d1963, d391, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1962 p = 1 := by simpa only [d1963, d391, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10092 p hg
    simpa only [d1963, d391, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10100 (p : Pattern) (guard : d1964 p = 1) : d392 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1959 p = 1 := by simpa only [d1964, d392, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10097 p hg
    simpa only [d1964, d392, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1963 p = 1 := by simpa only [d1964, d392, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10099 p hg
    simpa only [d1964, d392, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10101 (p : Pattern) (guard : d1958 p = 1) : d389 p ≤ (0 : Int) + d136 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1953 p = 1 := by simpa only [d1958, d389, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9563 p hg
    simpa only [d1958, d389, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1957 p = 1 := by simpa only [d1958, d389, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10083 p hg
    simpa only [d1958, d389, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10102 (p : Pattern) (guard : d1962 p = 1) : d393 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1957 p = 1 := by simpa only [d1962, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9832 p hg
    simpa only [d1962, d393, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1961 p = 1 := by simpa only [d1962, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10091 p hg
    simpa only [d1962, d393, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10103 (p : Pattern) (guard : d1963 p = 1) : d394 p ≤ (0 : Int) + d137 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1958 p = 1 := by simpa only [d1963, d394, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10101 p hg
    simpa only [d1963, d394, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1962 p = 1 := by simpa only [d1963, d394, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10102 p hg
    simpa only [d1963, d394, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10104 (p : Pattern) (guard : d1962 p = 1) : d395 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1957 p = 1 := by simpa only [d1962, d395, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9568 p hg
    simpa only [d1962, d395, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1961 p = 1 := by simpa only [d1962, d395, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10091 p hg
    simpa only [d1962, d395, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10105 (p : Pattern) (guard : d1966 p = 1) : d390 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9836 p hg
    simpa only [d1966, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1966, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10106 (p : Pattern) (guard : d1967 p = 1) : d396 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1962 p = 1 := by simpa only [d1967, d396, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10104 p hg
    simpa only [d1967, d396, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1966 p = 1 := by simpa only [d1967, d396, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10105 p hg
    simpa only [d1967, d396, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10107 (p : Pattern) (guard : d1968 p = 1) : d397 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1963 p = 1 := by simpa only [d1968, d397, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10103 p hg
    simpa only [d1968, d397, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1967 p = 1 := by simpa only [d1968, d397, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10106 p hg
    simpa only [d1968, d397, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10108 (p : Pattern) (guard : d1969 p = 1) : d398 p ≤ (0 : Int) + d141 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1964 p = 1 := by simpa only [d1969, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10100 p hg
    simpa only [d1969, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1968 p = 1 := by simpa only [d1969, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10107 p hg
    simpa only [d1969, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10109 (p : Pattern) (guard : d1970 p = 1) : d398 p ≤ (0 : Int) + d141 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1965 p = 1 := by simpa only [d1970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10095 p hg
    simpa only [d1970, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1969 p = 1 := by simpa only [d1970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10108 p hg
    simpa only [d1970, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10110 (p : Pattern) (guard : d1954 p = 1) : d399 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1949 p = 1 := by simpa only [d1954, d399, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9580 p hg
    simpa only [d1954, d399, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1953 p = 1 := by simpa only [d1954, d399, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10079 p hg
    simpa only [d1954, d399, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10111 (p : Pattern) (guard : d1958 p = 1) : d399 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1953 p = 1 := by simpa only [d1958, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9519 p hg
    simpa only [d1958, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1957 p = 1 := by simpa only [d1958, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10083 p hg
    simpa only [d1958, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10112 (p : Pattern) (guard : d1959 p = 1) : d399 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1954 p = 1 := by simpa only [d1959, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10110 p hg
    simpa only [d1959, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1958 p = 1 := by simpa only [d1959, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10111 p hg
    simpa only [d1959, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10113 (p : Pattern) (guard : d1962 p = 1) : d400 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1957 p = 1 := by simpa only [d1962, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9800 p hg
    simpa only [d1962, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1961 p = 1 := by simpa only [d1962, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10091 p hg
    simpa only [d1962, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10114 (p : Pattern) (guard : d1963 p = 1) : d401 p ≤ (0 : Int) + d2 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1958 p = 1 := by simpa only [d1963, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10111 p hg
    simpa only [d1963, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1962 p = 1 := by simpa only [d1963, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10113 p hg
    simpa only [d1963, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10115 (p : Pattern) (guard : d1964 p = 1) : d402 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1959 p = 1 := by simpa only [d1964, d402, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10112 p hg
    simpa only [d1964, d402, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1963 p = 1 := by simpa only [d1964, d402, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10114 p hg
    simpa only [d1964, d402, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10116 (p : Pattern) (guard : d1958 p = 1) : d399 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1953 p = 1 := by simpa only [d1958, d399, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9589 p hg
    simpa only [d1958, d399, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1957 p = 1 := by simpa only [d1958, d399, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10083 p hg
    simpa only [d1958, d399, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10117 (p : Pattern) (guard : d1962 p = 1) : d403 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1957 p = 1 := by simpa only [d1962, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9814 p hg
    simpa only [d1962, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1961 p = 1 := by simpa only [d1962, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10091 p hg
    simpa only [d1962, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10118 (p : Pattern) (guard : d1963 p = 1) : d404 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1958 p = 1 := by simpa only [d1963, d404, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10116 p hg
    simpa only [d1963, d404, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1962 p = 1 := by simpa only [d1963, d404, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10117 p hg
    simpa only [d1963, d404, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10119 (p : Pattern) (guard : d1962 p = 1) : d405 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1957 p = 1 := by simpa only [d1962, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9542 p hg
    simpa only [d1962, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1961 p = 1 := by simpa only [d1962, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10091 p hg
    simpa only [d1962, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10120 (p : Pattern) (guard : d1966 p = 1) : d400 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9820 p hg
    simpa only [d1966, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1966, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10121 (p : Pattern) (guard : d1967 p = 1) : d406 p ≤ (0 : Int) + d2 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1962 p = 1 := by simpa only [d1967, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10119 p hg
    simpa only [d1967, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1966 p = 1 := by simpa only [d1967, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10120 p hg
    simpa only [d1967, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10122 (p : Pattern) (guard : d1968 p = 1) : d407 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1963 p = 1 := by simpa only [d1968, d407, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10118 p hg
    simpa only [d1968, d407, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1967 p = 1 := by simpa only [d1968, d407, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10121 p hg
    simpa only [d1968, d407, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10123 (p : Pattern) (guard : d1969 p = 1) : d408 p ≤ (0 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1964 p = 1 := by simpa only [d1969, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10115 p hg
    simpa only [d1969, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1968 p = 1 := by simpa only [d1969, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10122 p hg
    simpa only [d1969, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10124 (p : Pattern) (guard : d1962 p = 1) : d399 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1957 p = 1 := by simpa only [d1962, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9554 p hg
    simpa only [d1962, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1961 p = 1 := by simpa only [d1962, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10091 p hg
    simpa only [d1962, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10125 (p : Pattern) (guard : d1963 p = 1) : d399 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1958 p = 1 := by simpa only [d1963, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10116 p hg
    simpa only [d1963, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1962 p = 1 := by simpa only [d1963, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10124 p hg
    simpa only [d1963, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10126 (p : Pattern) (guard : d1967 p = 1) : d401 p ≤ (0 : Int) + d2 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1962 p = 1 := by simpa only [d1967, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10124 p hg
    simpa only [d1967, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1966 p = 1 := by simpa only [d1967, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10120 p hg
    simpa only [d1967, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10127 (p : Pattern) (guard : d1968 p = 1) : d402 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1963 p = 1 := by simpa only [d1968, d402, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10125 p hg
    simpa only [d1968, d402, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1967 p = 1 := by simpa only [d1968, d402, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10126 p hg
    simpa only [d1968, d402, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10128 (p : Pattern) (guard : d1962 p = 1) : d399 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1957 p = 1 := by simpa only [d1962, d399, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9608 p hg
    simpa only [d1962, d399, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1961 p = 1 := by simpa only [d1962, d399, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10091 p hg
    simpa only [d1962, d399, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10129 (p : Pattern) (guard : d1966 p = 1) : d403 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9833 p hg
    simpa only [d1966, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1966, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10130 (p : Pattern) (guard : d1967 p = 1) : d404 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1962 p = 1 := by simpa only [d1967, d404, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10128 p hg
    simpa only [d1967, d404, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1966 p = 1 := by simpa only [d1967, d404, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10129 p hg
    simpa only [d1967, d404, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10131 (p : Pattern) (guard : d1966 p = 1) : d405 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9571 p hg
    simpa only [d1966, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1966, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10132 (p : Pattern) (guard : d0 p = 1) : d400 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10133 (p : Pattern) (guard : d1971 p = 1) : d406 p ≤ (0 : Int) + d2 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10131 p hg
    simpa only [d1971, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10132 p hg
    simpa only [d1971, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10134 (p : Pattern) (guard : d1972 p = 1) : d407 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1967 p = 1 := by simpa only [d1972, d407, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10130 p hg
    simpa only [d1972, d407, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1971 p = 1 := by simpa only [d1972, d407, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10133 p hg
    simpa only [d1972, d407, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10135 (p : Pattern) (guard : d1973 p = 1) : d408 p ≤ (0 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1968 p = 1 := by simpa only [d1973, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10127 p hg
    simpa only [d1973, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1972 p = 1 := by simpa only [d1973, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10134 p hg
    simpa only [d1973, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10136 (p : Pattern) (guard : d1974 p = 1) : d408 p ≤ (0 : Int) + d152 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1969 p = 1 := by simpa only [d1974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10123 p hg
    simpa only [d1974, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1973 p = 1 := by simpa only [d1974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10135 p hg
    simpa only [d1974, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10137 (p : Pattern) (guard : d1975 p = 1) : d409 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1970 p = 1 := by simpa only [d1975, d409, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10109 p hg
    simpa only [d1975, d409, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1974 p = 1 := by simpa only [d1975, d409, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10136 p hg
    simpa only [d1975, d409, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10138 (p : Pattern) (guard : d1963 p = 1) : d391 p ≤ (0 : Int) + d137 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1958 p = 1 := by simpa only [d1963, d391, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10101 p hg
    simpa only [d1963, d391, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1962 p = 1 := by simpa only [d1963, d391, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10092 p hg
    simpa only [d1963, d391, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10139 (p : Pattern) (guard : d1962 p = 1) : d410 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1957 p = 1 := by simpa only [d1962, d410, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9620 p hg
    simpa only [d1962, d410, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1961 p = 1 := by simpa only [d1962, d410, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10091 p hg
    simpa only [d1962, d410, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10140 (p : Pattern) (guard : d1966 p = 1) : d411 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9864 p hg
    simpa only [d1966, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1966, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10141 (p : Pattern) (guard : d1967 p = 1) : d412 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1962 p = 1 := by simpa only [d1967, d412, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10139 p hg
    simpa only [d1967, d412, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1966 p = 1 := by simpa only [d1967, d412, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10140 p hg
    simpa only [d1967, d412, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10142 (p : Pattern) (guard : d1968 p = 1) : d413 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1963 p = 1 := by simpa only [d1968, d413, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10138 p hg
    simpa only [d1968, d413, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1967 p = 1 := by simpa only [d1968, d413, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10141 p hg
    simpa only [d1968, d413, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10143 (p : Pattern) (guard : d1969 p = 1) : d414 p ≤ (0 : Int) + d141 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1964 p = 1 := by simpa only [d1969, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10100 p hg
    simpa only [d1969, d414, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1968 p = 1 := by simpa only [d1969, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10142 p hg
    simpa only [d1969, d414, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10144 (p : Pattern) (guard : d1962 p = 1) : d389 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1957 p = 1 := by simpa only [d1962, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9869 p hg
    simpa only [d1962, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1961 p = 1 := by simpa only [d1962, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10091 p hg
    simpa only [d1962, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10145 (p : Pattern) (guard : d1963 p = 1) : d389 p ≤ (0 : Int) + d137 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1958 p = 1 := by simpa only [d1963, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10101 p hg
    simpa only [d1963, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1962 p = 1 := by simpa only [d1963, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10144 p hg
    simpa only [d1963, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10146 (p : Pattern) (guard : d1962 p = 1) : d389 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1957 p = 1 := by simpa only [d1962, d389, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9627 p hg
    simpa only [d1962, d389, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1961 p = 1 := by simpa only [d1962, d389, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10091 p hg
    simpa only [d1962, d389, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10147 (p : Pattern) (guard : d1967 p = 1) : d391 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1962 p = 1 := by simpa only [d1967, d391, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10146 p hg
    simpa only [d1967, d391, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1966 p = 1 := by simpa only [d1967, d391, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10105 p hg
    simpa only [d1967, d391, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10148 (p : Pattern) (guard : d1968 p = 1) : d392 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1963 p = 1 := by simpa only [d1968, d392, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10145 p hg
    simpa only [d1968, d392, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1967 p = 1 := by simpa only [d1968, d392, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10147 p hg
    simpa only [d1968, d392, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10149 (p : Pattern) (guard : d1962 p = 1) : d389 p ≤ (0 : Int) + d136 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1957 p = 1 := by simpa only [d1962, d389, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9635 p hg
    simpa only [d1962, d389, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1961 p = 1 := by simpa only [d1962, d389, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10091 p hg
    simpa only [d1962, d389, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10150 (p : Pattern) (guard : d1967 p = 1) : d391 p ≤ (0 : Int) + d137 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1962 p = 1 := by simpa only [d1967, d391, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10149 p hg
    simpa only [d1967, d391, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1966 p = 1 := by simpa only [d1967, d391, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10105 p hg
    simpa only [d1967, d391, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10151 (p : Pattern) (guard : d1966 p = 1) : d199 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d199, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9639 p hg
    simpa only [d1966, d199, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d199, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1966, d199, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10152 (p : Pattern) (guard : d0 p = 1) : d200 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10153 (p : Pattern) (guard : d1971 p = 1) : d201 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d201, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10151 p hg
    simpa only [d1971, d201, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d201, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10152 p hg
    simpa only [d1971, d201, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10154 (p : Pattern) (guard : d1972 p = 1) : d415 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1967 p = 1 := by simpa only [d1972, d415, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10150 p hg
    simpa only [d1972, d415, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1971 p = 1 := by simpa only [d1972, d415, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10153 p hg
    simpa only [d1972, d415, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10155 (p : Pattern) (guard : d1973 p = 1) : d416 p ≤ (0 : Int) + d141 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1968 p = 1 := by simpa only [d1973, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10148 p hg
    simpa only [d1973, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1972 p = 1 := by simpa only [d1973, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10154 p hg
    simpa only [d1973, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10156 (p : Pattern) (guard : d1974 p = 1) : d417 p ≤ (0 : Int) + d141 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1969 p = 1 := by simpa only [d1974, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10143 p hg
    simpa only [d1974, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1973 p = 1 := by simpa only [d1974, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10155 p hg
    simpa only [d1974, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10157 (p : Pattern) (guard : d1967 p = 1) : d401 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1962 p = 1 := by simpa only [d1967, d401, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10128 p hg
    simpa only [d1967, d401, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1966 p = 1 := by simpa only [d1967, d401, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10120 p hg
    simpa only [d1967, d401, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10158 (p : Pattern) (guard : d1966 p = 1) : d199 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9621 p hg
    simpa only [d1966, d199, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1966, d199, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10159 (p : Pattern) (guard : d1971 p = 1) : d201 p ≤ (0 : Int) + d2 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10158 p hg
    simpa only [d1971, d201, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10152 p hg
    simpa only [d1971, d201, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10160 (p : Pattern) (guard : d1972 p = 1) : d418 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1967 p = 1 := by simpa only [d1972, d418, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10157 p hg
    simpa only [d1972, d418, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1971 p = 1 := by simpa only [d1972, d418, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10159 p hg
    simpa only [d1972, d418, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10161 (p : Pattern) (guard : d1973 p = 1) : d419 p ≤ (0 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1968 p = 1 := by simpa only [d1973, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10127 p hg
    simpa only [d1973, d419, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1972 p = 1 := by simpa only [d1973, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10160 p hg
    simpa only [d1973, d419, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10162 (p : Pattern) (guard : d1966 p = 1) : d399 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9628 p hg
    simpa only [d1966, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1966, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10163 (p : Pattern) (guard : d1967 p = 1) : d399 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1962 p = 1 := by simpa only [d1967, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10128 p hg
    simpa only [d1967, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1966 p = 1 := by simpa only [d1967, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10162 p hg
    simpa only [d1967, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10164 (p : Pattern) (guard : d1971 p = 1) : d401 p ≤ (0 : Int) + d2 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10162 p hg
    simpa only [d1971, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10132 p hg
    simpa only [d1971, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10165 (p : Pattern) (guard : d1972 p = 1) : d402 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1967 p = 1 := by simpa only [d1972, d402, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10163 p hg
    simpa only [d1972, d402, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1971 p = 1 := by simpa only [d1972, d402, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10164 p hg
    simpa only [d1972, d402, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10166 (p : Pattern) (guard : d1966 p = 1) : d399 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d399, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9657 p hg
    simpa only [d1966, d399, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d399, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1966, d399, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10167 (p : Pattern) (guard : d1971 p = 1) : d401 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d401, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10166 p hg
    simpa only [d1971, d401, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d401, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10132 p hg
    simpa only [d1971, d401, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10168 (p : Pattern) (guard : d0 p = 1) : d201 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10169 (p : Pattern) (guard : d1976 p = 1) : d418 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1971 p = 1 := by simpa only [d1976, d418, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10167 p hg
    simpa only [d1976, d418, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1976, d418, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10168 p hg
    simpa only [d1976, d418, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10170 (p : Pattern) (guard : d1977 p = 1) : d419 p ≤ (0 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1972 p = 1 := by simpa only [d1977, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10165 p hg
    simpa only [d1977, d419, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1976 p = 1 := by simpa only [d1977, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10169 p hg
    simpa only [d1977, d419, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10171 (p : Pattern) (guard : d1978 p = 1) : d419 p ≤ (0 : Int) + d152 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1973 p = 1 := by simpa only [d1978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10161 p hg
    simpa only [d1978, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1977 p = 1 := by simpa only [d1978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10170 p hg
    simpa only [d1978, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10172 (p : Pattern) (guard : d1979 p = 1) : d420 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1974 p = 1 := by simpa only [d1979, d420, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10156 p hg
    simpa only [d1979, d420, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1978 p = 1 := by simpa only [d1979, d420, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10171 p hg
    simpa only [d1979, d420, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10173 (p : Pattern) (guard : d1980 p = 1) : d421 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1975 p = 1 := by simpa only [d1980, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10137 p hg
    simpa only [d1980, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1979 p = 1 := by simpa only [d1980, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10172 p hg
    simpa only [d1980, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10174 (p : Pattern) (guard : d1966 p = 1) : d393 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9900 p hg
    simpa only [d1966, d393, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1966, d393, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10175 (p : Pattern) (guard : d1967 p = 1) : d394 p ≤ (0 : Int) + d137 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1962 p = 1 := by simpa only [d1967, d394, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10149 p hg
    simpa only [d1967, d394, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1966 p = 1 := by simpa only [d1967, d394, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10174 p hg
    simpa only [d1967, d394, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10176 (p : Pattern) (guard : d1966 p = 1) : d395 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d395, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9672 p hg
    simpa only [d1966, d395, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d395, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1966, d395, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10177 (p : Pattern) (guard : d0 p = 1) : d390 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10178 (p : Pattern) (guard : d1971 p = 1) : d396 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d396, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10176 p hg
    simpa only [d1971, d396, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d396, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10177 p hg
    simpa only [d1971, d396, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10179 (p : Pattern) (guard : d1972 p = 1) : d397 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1967 p = 1 := by simpa only [d1972, d397, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10175 p hg
    simpa only [d1972, d397, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1971 p = 1 := by simpa only [d1972, d397, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10178 p hg
    simpa only [d1972, d397, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10180 (p : Pattern) (guard : d1973 p = 1) : d398 p ≤ (0 : Int) + d141 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1968 p = 1 := by simpa only [d1973, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10148 p hg
    simpa only [d1973, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1972 p = 1 := by simpa only [d1973, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10179 p hg
    simpa only [d1973, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10181 (p : Pattern) (guard : d1974 p = 1) : d398 p ≤ (0 : Int) + d141 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1969 p = 1 := by simpa only [d1974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10108 p hg
    simpa only [d1974, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1973 p = 1 := by simpa only [d1974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10180 p hg
    simpa only [d1974, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10182 (p : Pattern) (guard : d1958 p = 1) : d422 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1953 p = 1 := by simpa only [d1958, d422, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9678 p hg
    simpa only [d1958, d422, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1957 p = 1 := by simpa only [d1958, d422, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10083 p hg
    simpa only [d1958, d422, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10183 (p : Pattern) (guard : d1962 p = 1) : d422 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1957 p = 1 := by simpa only [d1962, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9682 p hg
    simpa only [d1962, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1961 p = 1 := by simpa only [d1962, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10091 p hg
    simpa only [d1962, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10184 (p : Pattern) (guard : d1963 p = 1) : d422 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1958 p = 1 := by simpa only [d1963, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10182 p hg
    simpa only [d1963, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1962 p = 1 := by simpa only [d1963, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10183 p hg
    simpa only [d1963, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10185 (p : Pattern) (guard : d1967 p = 1) : d423 p ≤ (0 : Int) + d2 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1962 p = 1 := by simpa only [d1967, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10183 p hg
    simpa only [d1967, d423, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1966 p = 1 := by simpa only [d1967, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10140 p hg
    simpa only [d1967, d423, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10186 (p : Pattern) (guard : d1968 p = 1) : d424 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1963 p = 1 := by simpa only [d1968, d424, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10184 p hg
    simpa only [d1968, d424, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1967 p = 1 := by simpa only [d1968, d424, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10185 p hg
    simpa only [d1968, d424, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10187 (p : Pattern) (guard : d1962 p = 1) : d422 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1957 p = 1 := by simpa only [d1962, d422, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9687 p hg
    simpa only [d1962, d422, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1961 p = 1 := by simpa only [d1962, d422, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10091 p hg
    simpa only [d1962, d422, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10188 (p : Pattern) (guard : d1967 p = 1) : d423 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1962 p = 1 := by simpa only [d1967, d423, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10187 p hg
    simpa only [d1967, d423, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1966 p = 1 := by simpa only [d1967, d423, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10140 p hg
    simpa only [d1967, d423, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10189 (p : Pattern) (guard : d1966 p = 1) : d410 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9690 p hg
    simpa only [d1966, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1966, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10190 (p : Pattern) (guard : d0 p = 1) : d411 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10191 (p : Pattern) (guard : d1971 p = 1) : d412 p ≤ (0 : Int) + d2 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10189 p hg
    simpa only [d1971, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10190 p hg
    simpa only [d1971, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10192 (p : Pattern) (guard : d1972 p = 1) : d425 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1967 p = 1 := by simpa only [d1972, d425, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10188 p hg
    simpa only [d1972, d425, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1971 p = 1 := by simpa only [d1972, d425, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10191 p hg
    simpa only [d1972, d425, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10193 (p : Pattern) (guard : d1973 p = 1) : d426 p ≤ (0 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1968 p = 1 := by simpa only [d1973, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10186 p hg
    simpa only [d1973, d426, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1972 p = 1 := by simpa only [d1973, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10192 p hg
    simpa only [d1973, d426, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10194 (p : Pattern) (guard : d1966 p = 1) : d422 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9695 p hg
    simpa only [d1966, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1966, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10195 (p : Pattern) (guard : d1967 p = 1) : d422 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1962 p = 1 := by simpa only [d1967, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10187 p hg
    simpa only [d1967, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1966 p = 1 := by simpa only [d1967, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10194 p hg
    simpa only [d1967, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10196 (p : Pattern) (guard : d1971 p = 1) : d423 p ≤ (0 : Int) + d2 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10194 p hg
    simpa only [d1971, d423, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10190 p hg
    simpa only [d1971, d423, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10197 (p : Pattern) (guard : d1972 p = 1) : d424 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1967 p = 1 := by simpa only [d1972, d424, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10195 p hg
    simpa only [d1972, d424, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1971 p = 1 := by simpa only [d1972, d424, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10196 p hg
    simpa only [d1972, d424, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10198 (p : Pattern) (guard : d1966 p = 1) : d422 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d422, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9699 p hg
    simpa only [d1966, d422, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d422, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1966, d422, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10199 (p : Pattern) (guard : d1971 p = 1) : d423 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d423, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10198 p hg
    simpa only [d1971, d423, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d423, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10190 p hg
    simpa only [d1971, d423, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10200 (p : Pattern) (guard : d0 p = 1) : d412 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10201 (p : Pattern) (guard : d1976 p = 1) : d425 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1971 p = 1 := by simpa only [d1976, d425, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10199 p hg
    simpa only [d1976, d425, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1976, d425, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10200 p hg
    simpa only [d1976, d425, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10202 (p : Pattern) (guard : d1977 p = 1) : d426 p ≤ (0 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1972 p = 1 := by simpa only [d1977, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10197 p hg
    simpa only [d1977, d426, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1976 p = 1 := by simpa only [d1977, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10201 p hg
    simpa only [d1977, d426, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10203 (p : Pattern) (guard : d1978 p = 1) : d426 p ≤ (0 : Int) + d152 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1973 p = 1 := by simpa only [d1978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10193 p hg
    simpa only [d1978, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1977 p = 1 := by simpa only [d1978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10202 p hg
    simpa only [d1978, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10204 (p : Pattern) (guard : d1979 p = 1) : d427 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1974 p = 1 := by simpa only [d1979, d427, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10181 p hg
    simpa only [d1979, d427, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1978 p = 1 := by simpa only [d1979, d427, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10203 p hg
    simpa only [d1979, d427, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10205 (p : Pattern) (guard : d1966 p = 1) : d389 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9922 p hg
    simpa only [d1966, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1966, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10206 (p : Pattern) (guard : d1967 p = 1) : d389 p ≤ (0 : Int) + d137 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1962 p = 1 := by simpa only [d1967, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10149 p hg
    simpa only [d1967, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1966 p = 1 := by simpa only [d1967, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10205 p hg
    simpa only [d1967, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10207 (p : Pattern) (guard : d1966 p = 1) : d389 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d389, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9706 p hg
    simpa only [d1966, d389, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d389, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1966, d389, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10208 (p : Pattern) (guard : d1971 p = 1) : d391 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d391, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10207 p hg
    simpa only [d1971, d391, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d391, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10177 p hg
    simpa only [d1971, d391, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10209 (p : Pattern) (guard : d1972 p = 1) : d392 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1967 p = 1 := by simpa only [d1972, d392, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10206 p hg
    simpa only [d1972, d392, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1971 p = 1 := by simpa only [d1972, d392, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10208 p hg
    simpa only [d1972, d392, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10210 (p : Pattern) (guard : d1966 p = 1) : d389 p ≤ (0 : Int) + d136 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d389, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9710 p hg
    simpa only [d1966, d389, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d389, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1966, d389, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10211 (p : Pattern) (guard : d1971 p = 1) : d391 p ≤ (0 : Int) + d137 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d391, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10210 p hg
    simpa only [d1971, d391, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d391, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10177 p hg
    simpa only [d1971, d391, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10212 (p : Pattern) (guard : d0 p = 1) : d201 p ≤ (0 : Int) + d140 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10213 (p : Pattern) (guard : d1976 p = 1) : d415 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1971 p = 1 := by simpa only [d1976, d415, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10211 p hg
    simpa only [d1976, d415, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1976, d415, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10212 p hg
    simpa only [d1976, d415, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10214 (p : Pattern) (guard : d1977 p = 1) : d416 p ≤ (0 : Int) + d141 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1972 p = 1 := by simpa only [d1977, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10209 p hg
    simpa only [d1977, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1976 p = 1 := by simpa only [d1977, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10213 p hg
    simpa only [d1977, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10215 (p : Pattern) (guard : d1978 p = 1) : d416 p ≤ (0 : Int) + d141 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1973 p = 1 := by simpa only [d1978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10155 p hg
    simpa only [d1978, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1977 p = 1 := by simpa only [d1978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10214 p hg
    simpa only [d1978, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10216 (p : Pattern) (guard : d1976 p = 1) : d428 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1971 p = 1 := by simpa only [d1976, d428, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10199 p hg
    simpa only [d1976, d428, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1976, d428, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1976, d428, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10217 (p : Pattern) (guard : d1977 p = 1) : d429 p ≤ (0 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1972 p = 1 := by simpa only [d1977, d429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10197 p hg
    simpa only [d1977, d429, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1976 p = 1 := by simpa only [d1977, d429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10216 p hg
    simpa only [d1977, d429, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10218 (p : Pattern) (guard : d1966 p = 1) : d430 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d430, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9719 p hg
    simpa only [d1966, d430, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d430, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1966, d430, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10219 (p : Pattern) (guard : d0 p = 1) : d430 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
end NetHack.Sokoban32Refined
