/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Comparisons075
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare10640 (p : Pattern) (guard : d1975 p = 1) : d476 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1970 p = 1 := by simpa only [d1975, d476, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10618 p hg
    simpa only [d1975, d476, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1974 p = 1 := by simpa only [d1975, d476, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10639 p hg
    simpa only [d1975, d476, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10641 (p : Pattern) (guard : d1963 p = 1) : d477 p ≤ (0 : Int) + d137 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1958 p = 1 := by simpa only [d1963, d477, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10607 p hg
    simpa only [d1963, d477, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1962 p = 1 := by simpa only [d1963, d477, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10595 p hg
    simpa only [d1963, d477, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10642 (p : Pattern) (guard : d1957 p = 1) : d478 p ≤ (0 : Int) + d138 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1952 p = 1 := by simpa only [d1957, d478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9618 p hg
    simpa only [d1957, d478, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1956 p = 1 := by simpa only [d1957, d478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10019 p hg
    simpa only [d1957, d478, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10643 (p : Pattern) (guard : d1962 p = 1) : d479 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1957 p = 1 := by simpa only [d1962, d479, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10642 p hg
    simpa only [d1962, d479, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1961 p = 1 := by simpa only [d1962, d479, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9621 p hg
    simpa only [d1962, d479, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10644 (p : Pattern) (guard : d1961 p = 1) : d70 p ≤ (0 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1956 p = 1 := by simpa only [d1961, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9799 p hg
    simpa only [d1961, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1961, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1961, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10645 (p : Pattern) (guard : d1966 p = 1) : d70 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10644 p hg
    simpa only [d1966, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare882 p hg
    simpa only [d1966, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10646 (p : Pattern) (guard : d1967 p = 1) : d480 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1962 p = 1 := by simpa only [d1967, d480, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10643 p hg
    simpa only [d1967, d480, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1966 p = 1 := by simpa only [d1967, d480, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10645 p hg
    simpa only [d1967, d480, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10647 (p : Pattern) (guard : d1968 p = 1) : d481 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1963 p = 1 := by simpa only [d1968, d481, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10641 p hg
    simpa only [d1968, d481, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1967 p = 1 := by simpa only [d1968, d481, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10646 p hg
    simpa only [d1968, d481, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10648 (p : Pattern) (guard : d1969 p = 1) : d482 p ≤ (0 : Int) + d141 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1964 p = 1 := by simpa only [d1969, d482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10604 p hg
    simpa only [d1969, d482, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1968 p = 1 := by simpa only [d1969, d482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10647 p hg
    simpa only [d1969, d482, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10649 (p : Pattern) (guard : d1963 p = 1) : d458 p ≤ (0 : Int) + d137 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1958 p = 1 := by simpa only [d1963, d458, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10607 p hg
    simpa only [d1963, d458, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1962 p = 1 := by simpa only [d1963, d458, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10627 p hg
    simpa only [d1963, d458, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10650 (p : Pattern) (guard : d1967 p = 1) : d461 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1962 p = 1 := by simpa only [d1967, d461, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10632 p hg
    simpa only [d1967, d461, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1966 p = 1 := by simpa only [d1967, d461, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10614 p hg
    simpa only [d1967, d461, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10651 (p : Pattern) (guard : d1968 p = 1) : d462 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1963 p = 1 := by simpa only [d1968, d462, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10649 p hg
    simpa only [d1968, d462, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1967 p = 1 := by simpa only [d1968, d462, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10650 p hg
    simpa only [d1968, d462, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10652 (p : Pattern) (guard : d1951 p = 1) : d19 p ≤ (0 : Int) + d19 p := by
  omega
theorem compare10653 (p : Pattern) (guard : d1956 p = 1) : d142 p ≤ (0 : Int) + d135 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1951 p = 1 := by simpa only [d1956, d142, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10652 p hg
    simpa only [d1956, d142, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1956, d142, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6387 p hg
    simpa only [d1956, d142, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10654 (p : Pattern) (guard : d1957 p = 1) : d483 p ≤ (0 : Int) + d135 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1952 p = 1 := by simpa only [d1957, d483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9562 p hg
    simpa only [d1957, d483, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1956 p = 1 := by simpa only [d1957, d483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10653 p hg
    simpa only [d1957, d483, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10655 (p : Pattern) (guard : d1962 p = 1) : d484 p ≤ (0 : Int) + d136 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1957 p = 1 := by simpa only [d1962, d484, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10654 p hg
    simpa only [d1962, d484, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1961 p = 1 := by simpa only [d1962, d484, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9601 p hg
    simpa only [d1962, d484, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10656 (p : Pattern) (guard : d1967 p = 1) : d485 p ≤ (0 : Int) + d137 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1962 p = 1 := by simpa only [d1967, d485, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10655 p hg
    simpa only [d1967, d485, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1966 p = 1 := by simpa only [d1967, d485, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10614 p hg
    simpa only [d1967, d485, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10657 (p : Pattern) (guard : d1972 p = 1) : d486 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1967 p = 1 := by simpa only [d1972, d486, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10656 p hg
    simpa only [d1972, d486, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1971 p = 1 := by simpa only [d1972, d486, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9875 p hg
    simpa only [d1972, d486, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10658 (p : Pattern) (guard : d1973 p = 1) : d487 p ≤ (0 : Int) + d141 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1968 p = 1 := by simpa only [d1973, d487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10651 p hg
    simpa only [d1973, d487, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1972 p = 1 := by simpa only [d1973, d487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10657 p hg
    simpa only [d1973, d487, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10659 (p : Pattern) (guard : d1974 p = 1) : d488 p ≤ (0 : Int) + d141 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1969 p = 1 := by simpa only [d1974, d488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10648 p hg
    simpa only [d1974, d488, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1973 p = 1 := by simpa only [d1974, d488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10658 p hg
    simpa only [d1974, d488, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10660 (p : Pattern) (guard : d1972 p = 1) : d489 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1967 p = 1 := by simpa only [d1972, d489, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10650 p hg
    simpa only [d1972, d489, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1971 p = 1 := by simpa only [d1972, d489, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9883 p hg
    simpa only [d1972, d489, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10661 (p : Pattern) (guard : d1973 p = 1) : d490 p ≤ (0 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1968 p = 1 := by simpa only [d1973, d490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10630 p hg
    simpa only [d1973, d490, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1972 p = 1 := by simpa only [d1973, d490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10660 p hg
    simpa only [d1973, d490, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10662 (p : Pattern) (guard : d1966 p = 1) : d52 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9601 p hg
    simpa only [d1966, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4893 p hg
    simpa only [d1966, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10663 (p : Pattern) (guard : d1967 p = 1) : d469 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1962 p = 1 := by simpa only [d1967, d469, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10632 p hg
    simpa only [d1967, d469, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1966 p = 1 := by simpa only [d1967, d469, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10662 p hg
    simpa only [d1967, d469, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10664 (p : Pattern) (guard : d1971 p = 1) : d470 p ≤ (0 : Int) + d2 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10662 p hg
    simpa only [d1971, d470, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4895 p hg
    simpa only [d1971, d470, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10665 (p : Pattern) (guard : d1972 p = 1) : d471 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1967 p = 1 := by simpa only [d1972, d471, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10663 p hg
    simpa only [d1972, d471, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1971 p = 1 := by simpa only [d1972, d471, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10664 p hg
    simpa only [d1972, d471, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10666 (p : Pattern) (guard : d1961 p = 1) : d52 p ≤ (0 : Int) + d138 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1956 p = 1 := by simpa only [d1961, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9626 p hg
    simpa only [d1961, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1961, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9638 p hg
    simpa only [d1961, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10667 (p : Pattern) (guard : d1966 p = 1) : d52 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10666 p hg
    simpa only [d1966, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4893 p hg
    simpa only [d1966, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10668 (p : Pattern) (guard : d1971 p = 1) : d470 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d470, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10667 p hg
    simpa only [d1971, d470, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d470, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4895 p hg
    simpa only [d1971, d470, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10669 (p : Pattern) (guard : d1976 p = 1) : d491 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1971 p = 1 := by simpa only [d1976, d491, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10668 p hg
    simpa only [d1976, d491, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1976, d491, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1140 p hg
    simpa only [d1976, d491, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10670 (p : Pattern) (guard : d1977 p = 1) : d492 p ≤ (0 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1972 p = 1 := by simpa only [d1977, d492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10665 p hg
    simpa only [d1977, d492, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1976 p = 1 := by simpa only [d1977, d492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10669 p hg
    simpa only [d1977, d492, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10671 (p : Pattern) (guard : d1978 p = 1) : d493 p ≤ (0 : Int) + d152 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1973 p = 1 := by simpa only [d1978, d493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10661 p hg
    simpa only [d1978, d493, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1977 p = 1 := by simpa only [d1978, d493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10670 p hg
    simpa only [d1978, d493, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10672 (p : Pattern) (guard : d1979 p = 1) : d494 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1974 p = 1 := by simpa only [d1979, d494, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10659 p hg
    simpa only [d1979, d494, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1978 p = 1 := by simpa only [d1979, d494, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10671 p hg
    simpa only [d1979, d494, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10673 (p : Pattern) (guard : d1980 p = 1) : d495 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1975 p = 1 := by simpa only [d1980, d495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10640 p hg
    simpa only [d1980, d495, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1979 p = 1 := by simpa only [d1980, d495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10672 p hg
    simpa only [d1980, d495, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10674 (p : Pattern) (guard : d1967 p = 1) : d496 p ≤ (0 : Int) + d137 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1962 p = 1 := by simpa only [d1967, d496, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10655 p hg
    simpa only [d1967, d496, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1966 p = 1 := by simpa only [d1967, d496, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10633 p hg
    simpa only [d1967, d496, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10675 (p : Pattern) (guard : d1961 p = 1) : d61 p ≤ (0 : Int) + d138 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1956 p = 1 := by simpa only [d1961, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9567 p hg
    simpa only [d1961, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1961, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9638 p hg
    simpa only [d1961, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10676 (p : Pattern) (guard : d1966 p = 1) : d61 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10675 p hg
    simpa only [d1966, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4902 p hg
    simpa only [d1966, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10677 (p : Pattern) (guard : d1971 p = 1) : d473 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d473, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10676 p hg
    simpa only [d1971, d473, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d473, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4895 p hg
    simpa only [d1971, d473, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10678 (p : Pattern) (guard : d1972 p = 1) : d497 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1967 p = 1 := by simpa only [d1972, d497, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10674 p hg
    simpa only [d1972, d497, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1971 p = 1 := by simpa only [d1972, d497, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10677 p hg
    simpa only [d1972, d497, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10679 (p : Pattern) (guard : d1973 p = 1) : d498 p ≤ (0 : Int) + d141 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1968 p = 1 := by simpa only [d1973, d498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10651 p hg
    simpa only [d1973, d498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1972 p = 1 := by simpa only [d1973, d498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10678 p hg
    simpa only [d1973, d498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10680 (p : Pattern) (guard : d1974 p = 1) : d499 p ≤ (0 : Int) + d141 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1969 p = 1 := by simpa only [d1974, d499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10617 p hg
    simpa only [d1974, d499, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1973 p = 1 := by simpa only [d1974, d499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10679 p hg
    simpa only [d1974, d499, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10681 (p : Pattern) (guard : d1953 p = 1) : d500 p ≤ (0 : Int) + d138 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1948 p = 1 := by simpa only [d1953, d500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9579 p hg
    simpa only [d1953, d500, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1952 p = 1 := by simpa only [d1953, d500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10590 p hg
    simpa only [d1953, d500, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10682 (p : Pattern) (guard : d1958 p = 1) : d501 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1953 p = 1 := by simpa only [d1958, d501, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10681 p hg
    simpa only [d1958, d501, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1957 p = 1 := by simpa only [d1958, d501, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9679 p hg
    simpa only [d1958, d501, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10683 (p : Pattern) (guard : d1962 p = 1) : d97 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1957 p = 1 := by simpa only [d1962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9679 p hg
    simpa only [d1962, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1961 p = 1 := by simpa only [d1962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9683 p hg
    simpa only [d1962, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10684 (p : Pattern) (guard : d1963 p = 1) : d502 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1958 p = 1 := by simpa only [d1963, d502, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10682 p hg
    simpa only [d1963, d502, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1962 p = 1 := by simpa only [d1963, d502, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10683 p hg
    simpa only [d1963, d502, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10685 (p : Pattern) (guard : d1967 p = 1) : d109 p ≤ (0 : Int) + d2 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1962 p = 1 := by simpa only [d1967, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10683 p hg
    simpa only [d1967, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1966 p = 1 := by simpa only [d1967, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10645 p hg
    simpa only [d1967, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10686 (p : Pattern) (guard : d1968 p = 1) : d503 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1963 p = 1 := by simpa only [d1968, d503, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10684 p hg
    simpa only [d1968, d503, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1967 p = 1 := by simpa only [d1968, d503, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10685 p hg
    simpa only [d1968, d503, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10687 (p : Pattern) (guard : d1957 p = 1) : d500 p ≤ (0 : Int) + d138 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1952 p = 1 := by simpa only [d1957, d500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9588 p hg
    simpa only [d1957, d500, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1956 p = 1 := by simpa only [d1957, d500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10019 p hg
    simpa only [d1957, d500, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10688 (p : Pattern) (guard : d1962 p = 1) : d501 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1957 p = 1 := by simpa only [d1962, d501, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10687 p hg
    simpa only [d1962, d501, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1961 p = 1 := by simpa only [d1962, d501, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9683 p hg
    simpa only [d1962, d501, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10689 (p : Pattern) (guard : d1967 p = 1) : d504 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1962 p = 1 := by simpa only [d1967, d504, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10688 p hg
    simpa only [d1967, d504, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1966 p = 1 := by simpa only [d1967, d504, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10645 p hg
    simpa only [d1967, d504, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10690 (p : Pattern) (guard : d1972 p = 1) : d505 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1967 p = 1 := by simpa only [d1972, d505, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10689 p hg
    simpa only [d1972, d505, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1971 p = 1 := by simpa only [d1972, d505, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9883 p hg
    simpa only [d1972, d505, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10691 (p : Pattern) (guard : d1973 p = 1) : d506 p ≤ (0 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1968 p = 1 := by simpa only [d1973, d506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10686 p hg
    simpa only [d1973, d506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1972 p = 1 := by simpa only [d1973, d506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10690 p hg
    simpa only [d1973, d506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10692 (p : Pattern) (guard : d1966 p = 1) : d97 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9683 p hg
    simpa only [d1966, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare919 p hg
    simpa only [d1966, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10693 (p : Pattern) (guard : d1967 p = 1) : d502 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1962 p = 1 := by simpa only [d1967, d502, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10688 p hg
    simpa only [d1967, d502, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1966 p = 1 := by simpa only [d1967, d502, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10692 p hg
    simpa only [d1967, d502, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10694 (p : Pattern) (guard : d1971 p = 1) : d109 p ≤ (0 : Int) + d2 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10692 p hg
    simpa only [d1971, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare882 p hg
    simpa only [d1971, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10695 (p : Pattern) (guard : d1972 p = 1) : d503 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1967 p = 1 := by simpa only [d1972, d503, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10693 p hg
    simpa only [d1972, d503, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1971 p = 1 := by simpa only [d1972, d503, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10694 p hg
    simpa only [d1972, d503, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10696 (p : Pattern) (guard : d1971 p = 1) : d109 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d109, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9720 p hg
    simpa only [d1971, d109, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d109, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare882 p hg
    simpa only [d1971, d109, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10697 (p : Pattern) (guard : d1976 p = 1) : d125 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1971 p = 1 := by simpa only [d1976, d125, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10696 p hg
    simpa only [d1976, d125, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1976, d125, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1140 p hg
    simpa only [d1976, d125, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10698 (p : Pattern) (guard : d1977 p = 1) : d507 p ≤ (0 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1972 p = 1 := by simpa only [d1977, d507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10695 p hg
    simpa only [d1977, d507, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1976 p = 1 := by simpa only [d1977, d507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10697 p hg
    simpa only [d1977, d507, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10699 (p : Pattern) (guard : d1978 p = 1) : d508 p ≤ (0 : Int) + d152 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1973 p = 1 := by simpa only [d1978, d508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10691 p hg
    simpa only [d1978, d508, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1977 p = 1 := by simpa only [d1978, d508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10698 p hg
    simpa only [d1978, d508, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10700 (p : Pattern) (guard : d1979 p = 1) : d509 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1974 p = 1 := by simpa only [d1979, d509, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10680 p hg
    simpa only [d1979, d509, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1978 p = 1 := by simpa only [d1979, d509, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10699 p hg
    simpa only [d1979, d509, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10701 (p : Pattern) (guard : d1967 p = 1) : d510 p ≤ (0 : Int) + d137 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1962 p = 1 := by simpa only [d1967, d510, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10655 p hg
    simpa only [d1967, d510, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1966 p = 1 := by simpa only [d1967, d510, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10662 p hg
    simpa only [d1967, d510, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10702 (p : Pattern) (guard : d1972 p = 1) : d511 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1967 p = 1 := by simpa only [d1972, d511, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10701 p hg
    simpa only [d1972, d511, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1971 p = 1 := by simpa only [d1972, d511, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10668 p hg
    simpa only [d1972, d511, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10703 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d135 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10704 (p : Pattern) (guard : d1961 p = 1) : d52 p ≤ (0 : Int) + d135 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1956 p = 1 := by simpa only [d1961, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9634 p hg
    simpa only [d1961, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1961, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10703 p hg
    simpa only [d1961, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10705 (p : Pattern) (guard : d1966 p = 1) : d52 p ≤ (0 : Int) + d136 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10704 p hg
    simpa only [d1966, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4893 p hg
    simpa only [d1966, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10706 (p : Pattern) (guard : d1971 p = 1) : d470 p ≤ (0 : Int) + d137 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d470, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10705 p hg
    simpa only [d1971, d470, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d470, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4895 p hg
    simpa only [d1971, d470, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10707 (p : Pattern) (guard : d1976 p = 1) : d491 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1971 p = 1 := by simpa only [d1976, d491, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10706 p hg
    simpa only [d1976, d491, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1976, d491, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9928 p hg
    simpa only [d1976, d491, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10708 (p : Pattern) (guard : d1977 p = 1) : d512 p ≤ (0 : Int) + d141 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1972 p = 1 := by simpa only [d1977, d512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10702 p hg
    simpa only [d1977, d512, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1976 p = 1 := by simpa only [d1977, d512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10707 p hg
    simpa only [d1977, d512, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10709 (p : Pattern) (guard : d1978 p = 1) : d513 p ≤ (0 : Int) + d141 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1973 p = 1 := by simpa only [d1978, d513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10658 p hg
    simpa only [d1978, d513, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1977 p = 1 := by simpa only [d1978, d513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10708 p hg
    simpa only [d1978, d513, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10710 (p : Pattern) (guard : d1976 p = 1) : d111 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1971 p = 1 := by simpa only [d1976, d111, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10696 p hg
    simpa only [d1976, d111, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1976, d111, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1976, d111, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10711 (p : Pattern) (guard : d1977 p = 1) : d514 p ≤ (0 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1972 p = 1 := by simpa only [d1977, d514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10695 p hg
    simpa only [d1977, d514, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1976 p = 1 := by simpa only [d1977, d514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10710 p hg
    simpa only [d1977, d514, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10712 (p : Pattern) (guard : d1982 p = 1) : d515 p ≤ (0 : Int) + d152 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1977 p = 1 := by simpa only [d1982, d515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10711 p hg
    simpa only [d1982, d515, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1981 p = 1 := by simpa only [d1982, d515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9937 p hg
    simpa only [d1982, d515, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10713 (p : Pattern) (guard : d1983 p = 1) : d516 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1978 p = 1 := by simpa only [d1983, d516, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10709 p hg
    simpa only [d1983, d516, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1982 p = 1 := by simpa only [d1983, d516, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10712 p hg
    simpa only [d1983, d516, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10714 (p : Pattern) (guard : d1984 p = 1) : d517 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1979 p = 1 := by simpa only [d1984, d517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10700 p hg
    simpa only [d1984, d517, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1983 p = 1 := by simpa only [d1984, d517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10713 p hg
    simpa only [d1984, d517, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10715 (p : Pattern) (guard : d1985 p = 1) : d518 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1980 p = 1 := by simpa only [d1985, d518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10673 p hg
    simpa only [d1985, d518, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1984 p = 1 := by simpa only [d1985, d518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10714 p hg
    simpa only [d1985, d518, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10716 (p : Pattern) (guard : d1971 p = 1) : d519 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d519, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10667 p hg
    simpa only [d1971, d519, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d519, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4899 p hg
    simpa only [d1971, d519, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10717 (p : Pattern) (guard : d0 p = 1) : d473 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10718 (p : Pattern) (guard : d1976 p = 1) : d520 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1971 p = 1 := by simpa only [d1976, d520, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10716 p hg
    simpa only [d1976, d520, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1976, d520, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10717 p hg
    simpa only [d1976, d520, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10719 (p : Pattern) (guard : d1977 p = 1) : d521 p ≤ (0 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1972 p = 1 := by simpa only [d1977, d521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10665 p hg
    simpa only [d1977, d521, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1976 p = 1 := by simpa only [d1977, d521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10718 p hg
    simpa only [d1977, d521, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10720 (p : Pattern) (guard : d1978 p = 1) : d522 p ≤ (0 : Int) + d152 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1973 p = 1 := by simpa only [d1978, d522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10638 p hg
    simpa only [d1978, d522, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1977 p = 1 := by simpa only [d1978, d522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10719 p hg
    simpa only [d1978, d522, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10721 (p : Pattern) (guard : d1979 p = 1) : d523 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1974 p = 1 := by simpa only [d1979, d523, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10680 p hg
    simpa only [d1979, d523, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1978 p = 1 := by simpa only [d1979, d523, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10720 p hg
    simpa only [d1979, d523, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10722 (p : Pattern) (guard : d1971 p = 1) : d52 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10667 p hg
    simpa only [d1971, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4893 p hg
    simpa only [d1971, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10723 (p : Pattern) (guard : d0 p = 1) : d470 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10724 (p : Pattern) (guard : d1976 p = 1) : d524 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1971 p = 1 := by simpa only [d1976, d524, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10722 p hg
    simpa only [d1976, d524, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1976, d524, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10723 p hg
    simpa only [d1976, d524, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10725 (p : Pattern) (guard : d0 p = 1) : d491 p ≤ (0 : Int) + d152 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10726 (p : Pattern) (guard : d1981 p = 1) : d525 p ≤ (0 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1976 p = 1 := by simpa only [d1981, d525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10724 p hg
    simpa only [d1981, d525, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1981, d525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10725 p hg
    simpa only [d1981, d525, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10727 (p : Pattern) (guard : d1982 p = 1) : d526 p ≤ (0 : Int) + d152 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1977 p = 1 := by simpa only [d1982, d526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10670 p hg
    simpa only [d1982, d526, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1981 p = 1 := by simpa only [d1982, d526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10726 p hg
    simpa only [d1982, d526, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10728 (p : Pattern) (guard : d1983 p = 1) : d527 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1978 p = 1 := by simpa only [d1983, d527, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10709 p hg
    simpa only [d1983, d527, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1982 p = 1 := by simpa only [d1983, d527, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10727 p hg
    simpa only [d1983, d527, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10729 (p : Pattern) (guard : d1984 p = 1) : d528 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1979 p = 1 := by simpa only [d1984, d528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10721 p hg
    simpa only [d1984, d528, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1983 p = 1 := by simpa only [d1984, d528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10728 p hg
    simpa only [d1984, d528, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10730 (p : Pattern) (guard : d1971 p = 1) : d519 p ≤ (0 : Int) + d137 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d519, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10705 p hg
    simpa only [d1971, d519, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d519, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4899 p hg
    simpa only [d1971, d519, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10731 (p : Pattern) (guard : d0 p = 1) : d473 p ≤ (0 : Int) + d140 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10732 (p : Pattern) (guard : d1976 p = 1) : d520 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1971 p = 1 := by simpa only [d1976, d520, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10730 p hg
    simpa only [d1976, d520, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1976, d520, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10731 p hg
    simpa only [d1976, d520, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10733 (p : Pattern) (guard : d1977 p = 1) : d529 p ≤ (0 : Int) + d141 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1972 p = 1 := by simpa only [d1977, d529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10702 p hg
    simpa only [d1977, d529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1976 p = 1 := by simpa only [d1977, d529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10732 p hg
    simpa only [d1977, d529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10734 (p : Pattern) (guard : d1978 p = 1) : d530 p ≤ (0 : Int) + d141 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1973 p = 1 := by simpa only [d1978, d530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10679 p hg
    simpa only [d1978, d530, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1977 p = 1 := by simpa only [d1978, d530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10733 p hg
    simpa only [d1978, d530, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10735 (p : Pattern) (guard : d1982 p = 1) : d531 p ≤ (0 : Int) + d152 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1977 p = 1 := by simpa only [d1982, d531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10698 p hg
    simpa only [d1982, d531, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1981 p = 1 := by simpa only [d1982, d531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9985 p hg
    simpa only [d1982, d531, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10736 (p : Pattern) (guard : d1983 p = 1) : d532 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1978 p = 1 := by simpa only [d1983, d532, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10734 p hg
    simpa only [d1983, d532, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1982 p = 1 := by simpa only [d1983, d532, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10735 p hg
    simpa only [d1983, d532, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10737 (p : Pattern) (guard : d1971 p = 1) : d52 p ≤ (0 : Int) + d137 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10705 p hg
    simpa only [d1971, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4893 p hg
    simpa only [d1971, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10738 (p : Pattern) (guard : d0 p = 1) : d470 p ≤ (0 : Int) + d140 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10739 (p : Pattern) (guard : d1976 p = 1) : d524 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1971 p = 1 := by simpa only [d1976, d524, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10737 p hg
    simpa only [d1976, d524, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1976, d524, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10738 p hg
    simpa only [d1976, d524, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10740 (p : Pattern) (guard : d0 p = 1) : d491 p ≤ (0 : Int) + d141 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10741 (p : Pattern) (guard : d1981 p = 1) : d525 p ≤ (0 : Int) + d141 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1976 p = 1 := by simpa only [d1981, d525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10739 p hg
    simpa only [d1981, d525, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1981, d525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10740 p hg
    simpa only [d1981, d525, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10742 (p : Pattern) (guard : d1982 p = 1) : d533 p ≤ (0 : Int) + d141 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1977 p = 1 := by simpa only [d1982, d533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10708 p hg
    simpa only [d1982, d533, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1981 p = 1 := by simpa only [d1982, d533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10741 p hg
    simpa only [d1982, d533, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10743 (p : Pattern) (guard : d1987 p = 1) : d534 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1982 p = 1 := by simpa only [d1987, d534, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10742 p hg
    simpa only [d1987, d534, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1986 p = 1 := by simpa only [d1987, d534, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9994 p hg
    simpa only [d1987, d534, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10744 (p : Pattern) (guard : d1988 p = 1) : d535 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1983 p = 1 := by simpa only [d1988, d535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10736 p hg
    simpa only [d1988, d535, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1987 p = 1 := by simpa only [d1988, d535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10743 p hg
    simpa only [d1988, d535, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10745 (p : Pattern) (guard : d1989 p = 1) : d536 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1984 p = 1 := by simpa only [d1989, d536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10729 p hg
    simpa only [d1989, d536, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1988 p = 1 := by simpa only [d1989, d536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10744 p hg
    simpa only [d1989, d536, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10746 (p : Pattern) (guard : d1990 p = 1) : d537 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 80 with
  | false =>
    have hg : d1985 p = 1 := by simpa only [d1990, d537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10715 p hg
    simpa only [d1990, d537, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1989 p = 1 := by simpa only [d1990, d537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10745 p hg
    simpa only [d1990, d537, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10747 (p : Pattern) (guard : d1974 p = 1) : d152 p ≤ (0 : Int) + d152 p := by
  omega
theorem compare10748 (p : Pattern) (guard : d1975 p = 1) : d184 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1970 p = 1 := by simpa only [d1975, d184, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9841 p hg
    simpa only [d1975, d184, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1974 p = 1 := by simpa only [d1975, d184, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10747 p hg
    simpa only [d1975, d184, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10749 (p : Pattern) (guard : d1973 p = 1) : d152 p ≤ (0 : Int) + d152 p := by
  omega
theorem compare10750 (p : Pattern) (guard : d1972 p = 1) : d152 p ≤ (0 : Int) + d152 p := by
  omega
theorem compare10751 (p : Pattern) (guard : d1976 p = 1) : d153 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1971 p = 1 := by simpa only [d1976, d153, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10022 p hg
    simpa only [d1976, d153, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1976, d153, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1976, d153, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10752 (p : Pattern) (guard : d1977 p = 1) : d154 p ≤ (0 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1972 p = 1 := by simpa only [d1977, d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10750 p hg
    simpa only [d1977, d154, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1976 p = 1 := by simpa only [d1977, d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10751 p hg
    simpa only [d1977, d154, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10753 (p : Pattern) (guard : d1978 p = 1) : d155 p ≤ (0 : Int) + d152 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1973 p = 1 := by simpa only [d1978, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10749 p hg
    simpa only [d1978, d155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1977 p = 1 := by simpa only [d1978, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10752 p hg
    simpa only [d1978, d155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10754 (p : Pattern) (guard : d1979 p = 1) : d185 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1974 p = 1 := by simpa only [d1979, d185, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9878 p hg
    simpa only [d1979, d185, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1978 p = 1 := by simpa only [d1979, d185, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10753 p hg
    simpa only [d1979, d185, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10755 (p : Pattern) (guard : d1980 p = 1) : d186 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1975 p = 1 := by simpa only [d1980, d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10748 p hg
    simpa only [d1980, d186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1979 p = 1 := by simpa only [d1980, d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10754 p hg
    simpa only [d1980, d186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10756 (p : Pattern) (guard : d1958 p = 1) : d187 p ≤ (0 : Int) + d136 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1953 p = 1 := by simpa only [d1958, d187, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9563 p hg
    simpa only [d1958, d187, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1957 p = 1 := by simpa only [d1958, d187, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9679 p hg
    simpa only [d1958, d187, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10757 (p : Pattern) (guard : d1962 p = 1) : d187 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1957 p = 1 := by simpa only [d1962, d187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9869 p hg
    simpa only [d1962, d187, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1961 p = 1 := by simpa only [d1962, d187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9683 p hg
    simpa only [d1962, d187, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10758 (p : Pattern) (guard : d1963 p = 1) : d187 p ≤ (0 : Int) + d137 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1958 p = 1 := by simpa only [d1963, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10756 p hg
    simpa only [d1963, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1962 p = 1 := by simpa only [d1963, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10757 p hg
    simpa only [d1963, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10759 (p : Pattern) (guard : d1962 p = 1) : d187 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1957 p = 1 := by simpa only [d1962, d187, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9627 p hg
    simpa only [d1962, d187, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1961 p = 1 := by simpa only [d1962, d187, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9683 p hg
    simpa only [d1962, d187, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10760 (p : Pattern) (guard : d1966 p = 1) : d188 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9836 p hg
    simpa only [d1966, d188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare882 p hg
    simpa only [d1966, d188, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10761 (p : Pattern) (guard : d1967 p = 1) : d189 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1962 p = 1 := by simpa only [d1967, d189, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10759 p hg
    simpa only [d1967, d189, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1966 p = 1 := by simpa only [d1967, d189, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10760 p hg
    simpa only [d1967, d189, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10762 (p : Pattern) (guard : d1968 p = 1) : d190 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1963 p = 1 := by simpa only [d1968, d190, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10758 p hg
    simpa only [d1968, d190, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1967 p = 1 := by simpa only [d1968, d190, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10761 p hg
    simpa only [d1968, d190, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10763 (p : Pattern) (guard : d1962 p = 1) : d187 p ≤ (0 : Int) + d136 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1957 p = 1 := by simpa only [d1962, d187, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9635 p hg
    simpa only [d1962, d187, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1961 p = 1 := by simpa only [d1962, d187, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9683 p hg
    simpa only [d1962, d187, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10764 (p : Pattern) (guard : d1966 p = 1) : d191 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9900 p hg
    simpa only [d1966, d191, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare882 p hg
    simpa only [d1966, d191, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10765 (p : Pattern) (guard : d1967 p = 1) : d192 p ≤ (0 : Int) + d137 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1962 p = 1 := by simpa only [d1967, d192, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10763 p hg
    simpa only [d1967, d192, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1966 p = 1 := by simpa only [d1967, d192, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10764 p hg
    simpa only [d1967, d192, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10766 (p : Pattern) (guard : d1966 p = 1) : d193 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d193, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9672 p hg
    simpa only [d1966, d193, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d193, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1451 p hg
    simpa only [d1966, d193, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10767 (p : Pattern) (guard : d0 p = 1) : d188 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10768 (p : Pattern) (guard : d1971 p = 1) : d194 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d194, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10766 p hg
    simpa only [d1971, d194, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d194, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10767 p hg
    simpa only [d1971, d194, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10769 (p : Pattern) (guard : d1972 p = 1) : d195 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1967 p = 1 := by simpa only [d1972, d195, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10765 p hg
    simpa only [d1972, d195, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1971 p = 1 := by simpa only [d1972, d195, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10768 p hg
    simpa only [d1972, d195, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10770 (p : Pattern) (guard : d1973 p = 1) : d196 p ≤ (0 : Int) + d141 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1968 p = 1 := by simpa only [d1973, d196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10762 p hg
    simpa only [d1973, d196, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1972 p = 1 := by simpa only [d1973, d196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10769 p hg
    simpa only [d1973, d196, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10771 (p : Pattern) (guard : d1974 p = 1) : d197 p ≤ (0 : Int) + d141 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1969 p = 1 := by simpa only [d1974, d197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9840 p hg
    simpa only [d1974, d197, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1973 p = 1 := by simpa only [d1974, d197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10770 p hg
    simpa only [d1974, d197, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10772 (p : Pattern) (guard : d1979 p = 1) : d198 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1974 p = 1 := by simpa only [d1979, d198, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10771 p hg
    simpa only [d1979, d198, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1978 p = 1 := by simpa only [d1979, d198, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10753 p hg
    simpa only [d1979, d198, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10773 (p : Pattern) (guard : d1966 p = 1) : d187 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9922 p hg
    simpa only [d1966, d187, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare919 p hg
    simpa only [d1966, d187, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10774 (p : Pattern) (guard : d1967 p = 1) : d187 p ≤ (0 : Int) + d137 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1962 p = 1 := by simpa only [d1967, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10763 p hg
    simpa only [d1967, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1966 p = 1 := by simpa only [d1967, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10773 p hg
    simpa only [d1967, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10775 (p : Pattern) (guard : d1966 p = 1) : d187 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d187, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9706 p hg
    simpa only [d1966, d187, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d187, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare919 p hg
    simpa only [d1966, d187, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10776 (p : Pattern) (guard : d1971 p = 1) : d189 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d189, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10775 p hg
    simpa only [d1971, d189, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d189, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10767 p hg
    simpa only [d1971, d189, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10777 (p : Pattern) (guard : d1972 p = 1) : d190 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1967 p = 1 := by simpa only [d1972, d190, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10774 p hg
    simpa only [d1972, d190, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1971 p = 1 := by simpa only [d1972, d190, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10776 p hg
    simpa only [d1972, d190, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10778 (p : Pattern) (guard : d1966 p = 1) : d187 p ≤ (0 : Int) + d136 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d187, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9710 p hg
    simpa only [d1966, d187, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d187, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare919 p hg
    simpa only [d1966, d187, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10779 (p : Pattern) (guard : d1971 p = 1) : d189 p ≤ (0 : Int) + d137 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d189, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10778 p hg
    simpa only [d1971, d189, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d189, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10767 p hg
    simpa only [d1971, d189, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban32Refined
