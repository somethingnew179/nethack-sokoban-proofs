/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Comparisons082
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare11620 (p : Pattern) (guard : d0 p = 1) : d773 p ≤ (0 : Int) + d140 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11621 (p : Pattern) (guard : d1976 p = 1) : d801 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1971 p = 1 := by simpa only [d1976, d801, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11619 p hg
    simpa only [d1976, d801, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1976, d801, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11620 p hg
    simpa only [d1976, d801, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11622 (p : Pattern) (guard : d1977 p = 1) : d802 p ≤ (0 : Int) + d141 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1972 p = 1 := by simpa only [d1977, d802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11615 p hg
    simpa only [d1977, d802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1976 p = 1 := by simpa only [d1977, d802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11621 p hg
    simpa only [d1977, d802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11623 (p : Pattern) (guard : d1978 p = 1) : d803 p ≤ (0 : Int) + d141 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1973 p = 1 := by simpa only [d1978, d803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11538 p hg
    simpa only [d1978, d803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1977 p = 1 := by simpa only [d1978, d803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11622 p hg
    simpa only [d1978, d803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11624 (p : Pattern) (guard : d1976 p = 1) : d804 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1971 p = 1 := by simpa only [d1976, d804, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11602 p hg
    simpa only [d1976, d804, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1976, d804, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1976, d804, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11625 (p : Pattern) (guard : d1977 p = 1) : d805 p ≤ (0 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1972 p = 1 := by simpa only [d1977, d805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11599 p hg
    simpa only [d1977, d805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1976 p = 1 := by simpa only [d1977, d805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11624 p hg
    simpa only [d1977, d805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11626 (p : Pattern) (guard : d1961 p = 1) : d794 p ≤ (0 : Int) + d138 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1956 p = 1 := by simpa only [d1961, d794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11497 p hg
    simpa only [d1961, d794, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1961, d794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9638 p hg
    simpa only [d1961, d794, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11627 (p : Pattern) (guard : d1966 p = 1) : d794 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11626 p hg
    simpa only [d1966, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8884 p hg
    simpa only [d1966, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11628 (p : Pattern) (guard : d1971 p = 1) : d794 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11627 p hg
    simpa only [d1971, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8884 p hg
    simpa only [d1971, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11629 (p : Pattern) (guard : d0 p = 1) : d806 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11630 (p : Pattern) (guard : d1976 p = 1) : d807 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1971 p = 1 := by simpa only [d1976, d807, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11628 p hg
    simpa only [d1976, d807, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1976, d807, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11629 p hg
    simpa only [d1976, d807, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11631 (p : Pattern) (guard : d0 p = 1) : d808 p ≤ (0 : Int) + d152 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11632 (p : Pattern) (guard : d1981 p = 1) : d809 p ≤ (0 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1976 p = 1 := by simpa only [d1981, d809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11630 p hg
    simpa only [d1981, d809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1981, d809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11631 p hg
    simpa only [d1981, d809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11633 (p : Pattern) (guard : d1982 p = 1) : d810 p ≤ (0 : Int) + d152 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1977 p = 1 := by simpa only [d1982, d810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11625 p hg
    simpa only [d1982, d810, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1981 p = 1 := by simpa only [d1982, d810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11632 p hg
    simpa only [d1982, d810, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11634 (p : Pattern) (guard : d1983 p = 1) : d811 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1978 p = 1 := by simpa only [d1983, d811, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11623 p hg
    simpa only [d1983, d811, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1982 p = 1 := by simpa only [d1983, d811, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11633 p hg
    simpa only [d1983, d811, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11635 (p : Pattern) (guard : d1984 p = 1) : d812 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1979 p = 1 := by simpa only [d1984, d812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11606 p hg
    simpa only [d1984, d812, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1983 p = 1 := by simpa only [d1984, d812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11634 p hg
    simpa only [d1984, d812, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11636 (p : Pattern) (guard : d1985 p = 1) : d813 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1980 p = 1 := by simpa only [d1985, d813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11563 p hg
    simpa only [d1985, d813, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1984 p = 1 := by simpa only [d1985, d813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11635 p hg
    simpa only [d1985, d813, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11637 (p : Pattern) (guard : d1966 p = 1) : d754 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d754, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11574 p hg
    simpa only [d1966, d754, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d754, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8831 p hg
    simpa only [d1966, d754, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11638 (p : Pattern) (guard : d1971 p = 1) : d754 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11637 p hg
    simpa only [d1971, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8823 p hg
    simpa only [d1971, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11639 (p : Pattern) (guard : d1972 p = 1) : d757 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1967 p = 1 := by simpa only [d1972, d757, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11533 p hg
    simpa only [d1972, d757, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1971 p = 1 := by simpa only [d1972, d757, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11638 p hg
    simpa only [d1972, d757, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11640 (p : Pattern) (guard : d1973 p = 1) : d758 p ≤ (0 : Int) + d141 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1968 p = 1 := by simpa only [d1973, d758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11526 p hg
    simpa only [d1973, d758, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1972 p = 1 := by simpa only [d1973, d758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11639 p hg
    simpa only [d1973, d758, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11641 (p : Pattern) (guard : d1974 p = 1) : d758 p ≤ (0 : Int) + d141 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1969 p = 1 := by simpa only [d1974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11462 p hg
    simpa only [d1974, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1973 p = 1 := by simpa only [d1974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11640 p hg
    simpa only [d1974, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11642 (p : Pattern) (guard : d1971 p = 1) : d753 p ≤ (0 : Int) + d2 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11480 p hg
    simpa only [d1971, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8831 p hg
    simpa only [d1971, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11643 (p : Pattern) (guard : d1972 p = 1) : d761 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1967 p = 1 := by simpa only [d1972, d761, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11545 p hg
    simpa only [d1972, d761, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1971 p = 1 := by simpa only [d1972, d761, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11642 p hg
    simpa only [d1972, d761, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11644 (p : Pattern) (guard : d1973 p = 1) : d762 p ≤ (0 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1968 p = 1 := by simpa only [d1973, d762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11543 p hg
    simpa only [d1973, d762, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1972 p = 1 := by simpa only [d1973, d762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11643 p hg
    simpa only [d1973, d762, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11645 (p : Pattern) (guard : d1976 p = 1) : d769 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1971 p = 1 := by simpa only [d1976, d769, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11558 p hg
    simpa only [d1976, d769, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1976, d769, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8839 p hg
    simpa only [d1976, d769, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11646 (p : Pattern) (guard : d1977 p = 1) : d770 p ≤ (0 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1972 p = 1 := by simpa only [d1977, d770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11554 p hg
    simpa only [d1977, d770, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1976 p = 1 := by simpa only [d1977, d770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11645 p hg
    simpa only [d1977, d770, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11647 (p : Pattern) (guard : d1978 p = 1) : d771 p ≤ (0 : Int) + d152 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1973 p = 1 := by simpa only [d1978, d771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11644 p hg
    simpa only [d1978, d771, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1977 p = 1 := by simpa only [d1978, d771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11646 p hg
    simpa only [d1978, d771, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11648 (p : Pattern) (guard : d1979 p = 1) : d772 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1974 p = 1 := by simpa only [d1979, d772, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11641 p hg
    simpa only [d1979, d772, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1978 p = 1 := by simpa only [d1979, d772, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11647 p hg
    simpa only [d1979, d772, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11649 (p : Pattern) (guard : d1966 p = 1) : d750 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11608 p hg
    simpa only [d1966, d750, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8829 p hg
    simpa only [d1966, d750, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11650 (p : Pattern) (guard : d1967 p = 1) : d750 p ≤ (0 : Int) + d137 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1962 p = 1 := by simpa only [d1967, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11532 p hg
    simpa only [d1967, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1966 p = 1 := by simpa only [d1967, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11649 p hg
    simpa only [d1967, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11651 (p : Pattern) (guard : d1966 p = 1) : d750 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d750, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11612 p hg
    simpa only [d1966, d750, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d750, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8829 p hg
    simpa only [d1966, d750, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11652 (p : Pattern) (guard : d1971 p = 1) : d755 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d755, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11651 p hg
    simpa only [d1971, d755, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d755, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8823 p hg
    simpa only [d1971, d755, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11653 (p : Pattern) (guard : d1972 p = 1) : d756 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1967 p = 1 := by simpa only [d1972, d756, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11650 p hg
    simpa only [d1972, d756, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1971 p = 1 := by simpa only [d1972, d756, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11652 p hg
    simpa only [d1972, d756, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11654 (p : Pattern) (guard : d1966 p = 1) : d750 p ≤ (0 : Int) + d136 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d750, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11617 p hg
    simpa only [d1966, d750, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d750, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8829 p hg
    simpa only [d1966, d750, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11655 (p : Pattern) (guard : d1971 p = 1) : d755 p ≤ (0 : Int) + d137 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d755, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11654 p hg
    simpa only [d1971, d755, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d755, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8823 p hg
    simpa only [d1971, d755, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11656 (p : Pattern) (guard : d1976 p = 1) : d777 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1971 p = 1 := by simpa only [d1976, d777, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11655 p hg
    simpa only [d1976, d777, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1976, d777, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11620 p hg
    simpa only [d1976, d777, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11657 (p : Pattern) (guard : d1977 p = 1) : d778 p ≤ (0 : Int) + d141 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1972 p = 1 := by simpa only [d1977, d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11653 p hg
    simpa only [d1977, d778, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1976 p = 1 := by simpa only [d1977, d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11656 p hg
    simpa only [d1977, d778, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11658 (p : Pattern) (guard : d1978 p = 1) : d778 p ≤ (0 : Int) + d141 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1973 p = 1 := by simpa only [d1978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11538 p hg
    simpa only [d1978, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1977 p = 1 := by simpa only [d1978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11657 p hg
    simpa only [d1978, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11659 (p : Pattern) (guard : d1966 p = 1) : d749 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11519 p hg
    simpa only [d1966, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8829 p hg
    simpa only [d1966, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11660 (p : Pattern) (guard : d1967 p = 1) : d749 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1962 p = 1 := by simpa only [d1967, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11544 p hg
    simpa only [d1967, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1966 p = 1 := by simpa only [d1967, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11659 p hg
    simpa only [d1967, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11661 (p : Pattern) (guard : d1971 p = 1) : d759 p ≤ (0 : Int) + d2 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11659 p hg
    simpa only [d1971, d759, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8831 p hg
    simpa only [d1971, d759, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11662 (p : Pattern) (guard : d1972 p = 1) : d760 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1967 p = 1 := by simpa only [d1972, d760, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11660 p hg
    simpa only [d1972, d760, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1971 p = 1 := by simpa only [d1972, d760, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11661 p hg
    simpa only [d1972, d760, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11663 (p : Pattern) (guard : d1966 p = 1) : d749 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11556 p hg
    simpa only [d1966, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8829 p hg
    simpa only [d1966, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11664 (p : Pattern) (guard : d1971 p = 1) : d759 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d759, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11663 p hg
    simpa only [d1971, d759, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d759, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8831 p hg
    simpa only [d1971, d759, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11665 (p : Pattern) (guard : d1976 p = 1) : d780 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1971 p = 1 := by simpa only [d1976, d780, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11664 p hg
    simpa only [d1976, d780, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1976, d780, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8851 p hg
    simpa only [d1976, d780, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11666 (p : Pattern) (guard : d1977 p = 1) : d781 p ≤ (0 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1972 p = 1 := by simpa only [d1977, d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11662 p hg
    simpa only [d1977, d781, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1976 p = 1 := by simpa only [d1977, d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11665 p hg
    simpa only [d1977, d781, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11667 (p : Pattern) (guard : d1971 p = 1) : d764 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11557 p hg
    simpa only [d1971, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8837 p hg
    simpa only [d1971, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11668 (p : Pattern) (guard : d0 p = 1) : d767 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11669 (p : Pattern) (guard : d1976 p = 1) : d768 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1971 p = 1 := by simpa only [d1976, d768, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11667 p hg
    simpa only [d1976, d768, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1976, d768, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11668 p hg
    simpa only [d1976, d768, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11670 (p : Pattern) (guard : d0 p = 1) : d782 p ≤ (0 : Int) + d152 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11671 (p : Pattern) (guard : d1981 p = 1) : d783 p ≤ (0 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1976 p = 1 := by simpa only [d1981, d783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11669 p hg
    simpa only [d1981, d783, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1981, d783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11670 p hg
    simpa only [d1981, d783, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11672 (p : Pattern) (guard : d1982 p = 1) : d784 p ≤ (0 : Int) + d152 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1977 p = 1 := by simpa only [d1982, d784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11666 p hg
    simpa only [d1982, d784, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1981 p = 1 := by simpa only [d1982, d784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11671 p hg
    simpa only [d1982, d784, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11673 (p : Pattern) (guard : d1983 p = 1) : d814 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1978 p = 1 := by simpa only [d1983, d814, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11658 p hg
    simpa only [d1983, d814, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1982 p = 1 := by simpa only [d1983, d814, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11672 p hg
    simpa only [d1983, d814, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11674 (p : Pattern) (guard : d1984 p = 1) : d815 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1979 p = 1 := by simpa only [d1984, d815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11648 p hg
    simpa only [d1984, d815, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1983 p = 1 := by simpa only [d1984, d815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11673 p hg
    simpa only [d1984, d815, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11675 (p : Pattern) (guard : d0 p = 1) : d788 p ≤ (0 : Int) + d140 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11676 (p : Pattern) (guard : d1976 p = 1) : d791 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1971 p = 1 := by simpa only [d1976, d791, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11619 p hg
    simpa only [d1976, d791, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1976, d791, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11675 p hg
    simpa only [d1976, d791, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11677 (p : Pattern) (guard : d1977 p = 1) : d792 p ≤ (0 : Int) + d141 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1972 p = 1 := by simpa only [d1977, d792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11615 p hg
    simpa only [d1977, d792, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1976 p = 1 := by simpa only [d1977, d792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11676 p hg
    simpa only [d1977, d792, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11678 (p : Pattern) (guard : d1978 p = 1) : d793 p ≤ (0 : Int) + d141 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1973 p = 1 := by simpa only [d1978, d793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11640 p hg
    simpa only [d1978, d793, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1977 p = 1 := by simpa only [d1978, d793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11677 p hg
    simpa only [d1978, d793, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11679 (p : Pattern) (guard : d0 p = 1) : d816 p ≤ (0 : Int) + d152 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11680 (p : Pattern) (guard : d1981 p = 1) : d817 p ≤ (0 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1976 p = 1 := by simpa only [d1981, d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11630 p hg
    simpa only [d1981, d817, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1981, d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11679 p hg
    simpa only [d1981, d817, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11681 (p : Pattern) (guard : d1982 p = 1) : d818 p ≤ (0 : Int) + d152 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1977 p = 1 := by simpa only [d1982, d818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11604 p hg
    simpa only [d1982, d818, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1981 p = 1 := by simpa only [d1982, d818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11680 p hg
    simpa only [d1982, d818, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11682 (p : Pattern) (guard : d1983 p = 1) : d819 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1978 p = 1 := by simpa only [d1983, d819, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11678 p hg
    simpa only [d1983, d819, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1982 p = 1 := by simpa only [d1983, d819, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11681 p hg
    simpa only [d1983, d819, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11683 (p : Pattern) (guard : d0 p = 1) : d748 p ≤ (0 : Int) + d135 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11684 (p : Pattern) (guard : d1961 p = 1) : d749 p ≤ (0 : Int) + d135 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1956 p = 1 := by simpa only [d1961, d749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11530 p hg
    simpa only [d1961, d749, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1961, d749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11683 p hg
    simpa only [d1961, d749, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11685 (p : Pattern) (guard : d1966 p = 1) : d764 p ≤ (0 : Int) + d136 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d764, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11684 p hg
    simpa only [d1966, d764, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d764, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11550 p hg
    simpa only [d1966, d764, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11686 (p : Pattern) (guard : d1971 p = 1) : d764 p ≤ (0 : Int) + d137 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11685 p hg
    simpa only [d1971, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8837 p hg
    simpa only [d1971, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11687 (p : Pattern) (guard : d0 p = 1) : d767 p ≤ (0 : Int) + d140 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11688 (p : Pattern) (guard : d1976 p = 1) : d768 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1971 p = 1 := by simpa only [d1976, d768, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11686 p hg
    simpa only [d1976, d768, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1976, d768, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11687 p hg
    simpa only [d1976, d768, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11689 (p : Pattern) (guard : d0 p = 1) : d782 p ≤ (0 : Int) + d141 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11690 (p : Pattern) (guard : d1981 p = 1) : d783 p ≤ (0 : Int) + d141 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1976 p = 1 := by simpa only [d1981, d783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11688 p hg
    simpa only [d1981, d783, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1981, d783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11689 p hg
    simpa only [d1981, d783, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11691 (p : Pattern) (guard : d1982 p = 1) : d820 p ≤ (0 : Int) + d141 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1977 p = 1 := by simpa only [d1982, d820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11657 p hg
    simpa only [d1982, d820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1981 p = 1 := by simpa only [d1982, d820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11690 p hg
    simpa only [d1982, d820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11692 (p : Pattern) (guard : d1986 p = 1) : d821 p ≤ (0 : Int) + d152 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1981 p = 1 := by simpa only [d1986, d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11632 p hg
    simpa only [d1986, d821, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1986, d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9780 p hg
    simpa only [d1986, d821, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11693 (p : Pattern) (guard : d1987 p = 1) : d822 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1982 p = 1 := by simpa only [d1987, d822, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11691 p hg
    simpa only [d1987, d822, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1986 p = 1 := by simpa only [d1987, d822, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11692 p hg
    simpa only [d1987, d822, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11694 (p : Pattern) (guard : d1988 p = 1) : d823 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1983 p = 1 := by simpa only [d1988, d823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11682 p hg
    simpa only [d1988, d823, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1987 p = 1 := by simpa only [d1988, d823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11693 p hg
    simpa only [d1988, d823, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11695 (p : Pattern) (guard : d1989 p = 1) : d824 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1984 p = 1 := by simpa only [d1989, d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11674 p hg
    simpa only [d1989, d824, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1988 p = 1 := by simpa only [d1989, d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11694 p hg
    simpa only [d1989, d824, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11696 (p : Pattern) (guard : d1990 p = 1) : d825 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 80 with
  | false =>
    have hg : d1985 p = 1 := by simpa only [d1990, d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11636 p hg
    simpa only [d1990, d825, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1989 p = 1 := by simpa only [d1990, d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11695 p hg
    simpa only [d1990, d825, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11697 (p : Pattern) (guard : d1970 p = 1) : d228 p ≤ (0 : Int) + d141 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1965 p = 1 := by simpa only [d1970, d228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9824 p hg
    simpa only [d1970, d228, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1969 p = 1 := by simpa only [d1970, d228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11113 p hg
    simpa only [d1970, d228, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11698 (p : Pattern) (guard : d1974 p = 1) : d229 p ≤ (0 : Int) + d152 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1969 p = 1 := by simpa only [d1974, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9851 p hg
    simpa only [d1974, d229, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1973 p = 1 := by simpa only [d1974, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10749 p hg
    simpa only [d1974, d229, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11699 (p : Pattern) (guard : d1975 p = 1) : d230 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1970 p = 1 := by simpa only [d1975, d230, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11697 p hg
    simpa only [d1975, d230, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1974 p = 1 := by simpa only [d1975, d230, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11698 p hg
    simpa only [d1975, d230, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11700 (p : Pattern) (guard : d1974 p = 1) : d231 p ≤ (0 : Int) + d141 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1969 p = 1 := by simpa only [d1974, d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9868 p hg
    simpa only [d1974, d231, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1973 p = 1 := by simpa only [d1974, d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11114 p hg
    simpa only [d1974, d231, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11701 (p : Pattern) (guard : d1978 p = 1) : d232 p ≤ (0 : Int) + d152 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1973 p = 1 := by simpa only [d1978, d232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9885 p hg
    simpa only [d1978, d232, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1977 p = 1 := by simpa only [d1978, d232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10752 p hg
    simpa only [d1978, d232, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11702 (p : Pattern) (guard : d1979 p = 1) : d233 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1974 p = 1 := by simpa only [d1979, d233, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11700 p hg
    simpa only [d1979, d233, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1978 p = 1 := by simpa only [d1979, d233, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11701 p hg
    simpa only [d1979, d233, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11703 (p : Pattern) (guard : d1980 p = 1) : d234 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1975 p = 1 := by simpa only [d1980, d234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11699 p hg
    simpa only [d1980, d234, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1979 p = 1 := by simpa only [d1980, d234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11702 p hg
    simpa only [d1980, d234, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11704 (p : Pattern) (guard : d1974 p = 1) : d235 p ≤ (0 : Int) + d141 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1969 p = 1 := by simpa only [d1974, d235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9840 p hg
    simpa only [d1974, d235, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1973 p = 1 := by simpa only [d1974, d235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11114 p hg
    simpa only [d1974, d235, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11705 (p : Pattern) (guard : d1978 p = 1) : d236 p ≤ (0 : Int) + d152 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1973 p = 1 := by simpa only [d1978, d236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9913 p hg
    simpa only [d1978, d236, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1977 p = 1 := by simpa only [d1978, d236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10752 p hg
    simpa only [d1978, d236, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11706 (p : Pattern) (guard : d1979 p = 1) : d237 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1974 p = 1 := by simpa only [d1979, d237, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11704 p hg
    simpa only [d1979, d237, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1978 p = 1 := by simpa only [d1979, d237, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11705 p hg
    simpa only [d1979, d237, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11707 (p : Pattern) (guard : d1978 p = 1) : d238 p ≤ (0 : Int) + d141 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1973 p = 1 := by simpa only [d1978, d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9877 p hg
    simpa only [d1978, d238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1977 p = 1 := by simpa only [d1978, d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11117 p hg
    simpa only [d1978, d238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11708 (p : Pattern) (guard : d1982 p = 1) : d239 p ≤ (0 : Int) + d152 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1977 p = 1 := by simpa only [d1982, d239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9933 p hg
    simpa only [d1982, d239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1981 p = 1 := by simpa only [d1982, d239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10783 p hg
    simpa only [d1982, d239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11709 (p : Pattern) (guard : d1983 p = 1) : d240 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1978 p = 1 := by simpa only [d1983, d240, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11707 p hg
    simpa only [d1983, d240, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1982 p = 1 := by simpa only [d1983, d240, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11708 p hg
    simpa only [d1983, d240, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11710 (p : Pattern) (guard : d1984 p = 1) : d241 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1979 p = 1 := by simpa only [d1984, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11706 p hg
    simpa only [d1984, d241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1983 p = 1 := by simpa only [d1984, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11709 p hg
    simpa only [d1984, d241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11711 (p : Pattern) (guard : d1985 p = 1) : d242 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1980 p = 1 := by simpa only [d1985, d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11703 p hg
    simpa only [d1985, d242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1984 p = 1 := by simpa only [d1985, d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11710 p hg
    simpa only [d1985, d242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11712 (p : Pattern) (guard : d1978 p = 1) : d243 p ≤ (0 : Int) + d152 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1973 p = 1 := by simpa only [d1978, d243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9952 p hg
    simpa only [d1978, d243, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1977 p = 1 := by simpa only [d1978, d243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10752 p hg
    simpa only [d1978, d243, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11713 (p : Pattern) (guard : d1979 p = 1) : d244 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1974 p = 1 := by simpa only [d1979, d244, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11704 p hg
    simpa only [d1979, d244, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1978 p = 1 := by simpa only [d1979, d244, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11712 p hg
    simpa only [d1979, d244, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11714 (p : Pattern) (guard : d1982 p = 1) : d245 p ≤ (0 : Int) + d152 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1977 p = 1 := by simpa only [d1982, d245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9971 p hg
    simpa only [d1982, d245, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1981 p = 1 := by simpa only [d1982, d245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10783 p hg
    simpa only [d1982, d245, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11715 (p : Pattern) (guard : d1983 p = 1) : d246 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1978 p = 1 := by simpa only [d1983, d246, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11707 p hg
    simpa only [d1983, d246, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1982 p = 1 := by simpa only [d1983, d246, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11714 p hg
    simpa only [d1983, d246, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11716 (p : Pattern) (guard : d1984 p = 1) : d247 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1979 p = 1 := by simpa only [d1984, d247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11713 p hg
    simpa only [d1984, d247, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1983 p = 1 := by simpa only [d1984, d247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11715 p hg
    simpa only [d1984, d247, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11717 (p : Pattern) (guard : d1978 p = 1) : d248 p ≤ (0 : Int) + d141 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1973 p = 1 := by simpa only [d1978, d248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9946 p hg
    simpa only [d1978, d248, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1977 p = 1 := by simpa only [d1978, d248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11117 p hg
    simpa only [d1978, d248, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11718 (p : Pattern) (guard : d1982 p = 1) : d249 p ≤ (0 : Int) + d152 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1977 p = 1 := by simpa only [d1982, d249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9919 p hg
    simpa only [d1982, d249, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1981 p = 1 := by simpa only [d1982, d249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10783 p hg
    simpa only [d1982, d249, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11719 (p : Pattern) (guard : d1983 p = 1) : d250 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1978 p = 1 := by simpa only [d1983, d250, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11717 p hg
    simpa only [d1983, d250, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1982 p = 1 := by simpa only [d1983, d250, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11718 p hg
    simpa only [d1983, d250, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11720 (p : Pattern) (guard : d1982 p = 1) : d251 p ≤ (0 : Int) + d141 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1977 p = 1 := by simpa only [d1982, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9964 p hg
    simpa only [d1982, d251, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1981 p = 1 := by simpa only [d1982, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11121 p hg
    simpa only [d1982, d251, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11721 (p : Pattern) (guard : d1987 p = 1) : d252 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1982 p = 1 := by simpa only [d1987, d252, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11720 p hg
    simpa only [d1987, d252, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1986 p = 1 := by simpa only [d1987, d252, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9994 p hg
    simpa only [d1987, d252, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11722 (p : Pattern) (guard : d1988 p = 1) : d253 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1983 p = 1 := by simpa only [d1988, d253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11719 p hg
    simpa only [d1988, d253, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1987 p = 1 := by simpa only [d1988, d253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11721 p hg
    simpa only [d1988, d253, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11723 (p : Pattern) (guard : d1989 p = 1) : d254 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1984 p = 1 := by simpa only [d1989, d254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11716 p hg
    simpa only [d1989, d254, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1988 p = 1 := by simpa only [d1989, d254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11722 p hg
    simpa only [d1989, d254, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11724 (p : Pattern) (guard : d1990 p = 1) : d255 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 80 with
  | false =>
    have hg : d1985 p = 1 := by simpa only [d1990, d255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11711 p hg
    simpa only [d1990, d255, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1989 p = 1 := by simpa only [d1990, d255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11723 p hg
    simpa only [d1990, d255, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban32Refined
