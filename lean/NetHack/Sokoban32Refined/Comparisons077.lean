/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Comparisons076
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare10780 (p : Pattern) (guard : d1976 p = 1) : d202 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1971 p = 1 := by simpa only [d1976, d202, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10779 p hg
    simpa only [d1976, d202, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1976, d202, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10212 p hg
    simpa only [d1976, d202, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10781 (p : Pattern) (guard : d1977 p = 1) : d203 p ≤ (0 : Int) + d141 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1972 p = 1 := by simpa only [d1977, d203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10777 p hg
    simpa only [d1977, d203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1976 p = 1 := by simpa only [d1977, d203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10780 p hg
    simpa only [d1977, d203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10782 (p : Pattern) (guard : d1978 p = 1) : d204 p ≤ (0 : Int) + d141 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1973 p = 1 := by simpa only [d1978, d204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9877 p hg
    simpa only [d1978, d204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1977 p = 1 := by simpa only [d1978, d204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10781 p hg
    simpa only [d1978, d204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10783 (p : Pattern) (guard : d1981 p = 1) : d163 p ≤ (0 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1976 p = 1 := by simpa only [d1981, d163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10751 p hg
    simpa only [d1981, d163, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1981, d163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9780 p hg
    simpa only [d1981, d163, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10784 (p : Pattern) (guard : d1982 p = 1) : d164 p ≤ (0 : Int) + d152 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1977 p = 1 := by simpa only [d1982, d164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10752 p hg
    simpa only [d1982, d164, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1981 p = 1 := by simpa only [d1982, d164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10783 p hg
    simpa only [d1982, d164, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10785 (p : Pattern) (guard : d1983 p = 1) : d205 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1978 p = 1 := by simpa only [d1983, d205, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10782 p hg
    simpa only [d1983, d205, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1982 p = 1 := by simpa only [d1983, d205, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10784 p hg
    simpa only [d1983, d205, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10786 (p : Pattern) (guard : d1984 p = 1) : d206 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1979 p = 1 := by simpa only [d1984, d206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10772 p hg
    simpa only [d1984, d206, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1983 p = 1 := by simpa only [d1984, d206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10785 p hg
    simpa only [d1984, d206, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10787 (p : Pattern) (guard : d1985 p = 1) : d207 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1980 p = 1 := by simpa only [d1985, d207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10755 p hg
    simpa only [d1985, d207, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1984 p = 1 := by simpa only [d1985, d207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10786 p hg
    simpa only [d1985, d207, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10788 (p : Pattern) (guard : d1979 p = 1) : d208 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1974 p = 1 := by simpa only [d1979, d208, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9947 p hg
    simpa only [d1979, d208, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1978 p = 1 := by simpa only [d1979, d208, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10753 p hg
    simpa only [d1979, d208, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10789 (p : Pattern) (guard : d1983 p = 1) : d209 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1978 p = 1 := by simpa only [d1983, d209, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9965 p hg
    simpa only [d1983, d209, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1982 p = 1 := by simpa only [d1983, d209, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10784 p hg
    simpa only [d1983, d209, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10790 (p : Pattern) (guard : d1984 p = 1) : d210 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1979 p = 1 := by simpa only [d1984, d210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10788 p hg
    simpa only [d1984, d210, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1983 p = 1 := by simpa only [d1984, d210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10789 p hg
    simpa only [d1984, d210, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10791 (p : Pattern) (guard : d0 p = 1) : d211 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10792 (p : Pattern) (guard : d1971 p = 1) : d212 p ≤ (0 : Int) + d137 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d212, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10778 p hg
    simpa only [d1971, d212, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d212, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10791 p hg
    simpa only [d1971, d212, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10793 (p : Pattern) (guard : d0 p = 1) : d194 p ≤ (0 : Int) + d140 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10794 (p : Pattern) (guard : d1976 p = 1) : d213 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1971 p = 1 := by simpa only [d1976, d213, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10792 p hg
    simpa only [d1976, d213, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1976, d213, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10793 p hg
    simpa only [d1976, d213, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10795 (p : Pattern) (guard : d1977 p = 1) : d214 p ≤ (0 : Int) + d141 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1972 p = 1 := by simpa only [d1977, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10777 p hg
    simpa only [d1977, d214, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1976 p = 1 := by simpa only [d1977, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10794 p hg
    simpa only [d1977, d214, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10796 (p : Pattern) (guard : d1978 p = 1) : d215 p ≤ (0 : Int) + d141 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1973 p = 1 := by simpa only [d1978, d215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9946 p hg
    simpa only [d1978, d215, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1977 p = 1 := by simpa only [d1978, d215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10795 p hg
    simpa only [d1978, d215, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10797 (p : Pattern) (guard : d1983 p = 1) : d216 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1978 p = 1 := by simpa only [d1983, d216, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10796 p hg
    simpa only [d1983, d216, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1982 p = 1 := by simpa only [d1983, d216, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10784 p hg
    simpa only [d1983, d216, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10798 (p : Pattern) (guard : d1966 p = 1) : d217 p ≤ (0 : Int) + d136 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d217, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9772 p hg
    simpa only [d1966, d217, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d217, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare919 p hg
    simpa only [d1966, d217, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10799 (p : Pattern) (guard : d0 p = 1) : d217 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10800 (p : Pattern) (guard : d1971 p = 1) : d217 p ≤ (0 : Int) + d137 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10798 p hg
    simpa only [d1971, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10799 p hg
    simpa only [d1971, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10801 (p : Pattern) (guard : d0 p = 1) : d219 p ≤ (0 : Int) + d140 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10802 (p : Pattern) (guard : d1976 p = 1) : d220 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1971 p = 1 := by simpa only [d1976, d220, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10800 p hg
    simpa only [d1976, d220, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1976, d220, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10801 p hg
    simpa only [d1976, d220, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10803 (p : Pattern) (guard : d0 p = 1) : d221 p ≤ (0 : Int) + d141 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10804 (p : Pattern) (guard : d1981 p = 1) : d222 p ≤ (0 : Int) + d141 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1976 p = 1 := by simpa only [d1981, d222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10802 p hg
    simpa only [d1981, d222, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1981, d222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10803 p hg
    simpa only [d1981, d222, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10805 (p : Pattern) (guard : d1982 p = 1) : d223 p ≤ (0 : Int) + d141 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1977 p = 1 := by simpa only [d1982, d223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9964 p hg
    simpa only [d1982, d223, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1981 p = 1 := by simpa only [d1982, d223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10804 p hg
    simpa only [d1982, d223, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10806 (p : Pattern) (guard : d1986 p = 1) : d169 p ≤ (0 : Int) + d152 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1981 p = 1 := by simpa only [d1986, d169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10783 p hg
    simpa only [d1986, d169, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1986, d169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9780 p hg
    simpa only [d1986, d169, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10807 (p : Pattern) (guard : d1987 p = 1) : d224 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1982 p = 1 := by simpa only [d1987, d224, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10805 p hg
    simpa only [d1987, d224, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1986 p = 1 := by simpa only [d1987, d224, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10806 p hg
    simpa only [d1987, d224, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10808 (p : Pattern) (guard : d1988 p = 1) : d225 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1983 p = 1 := by simpa only [d1988, d225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10797 p hg
    simpa only [d1988, d225, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1987 p = 1 := by simpa only [d1988, d225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10807 p hg
    simpa only [d1988, d225, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10809 (p : Pattern) (guard : d1989 p = 1) : d226 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1984 p = 1 := by simpa only [d1989, d226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10790 p hg
    simpa only [d1989, d226, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1988 p = 1 := by simpa only [d1989, d226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10808 p hg
    simpa only [d1989, d226, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10810 (p : Pattern) (guard : d1990 p = 1) : d227 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 80 with
  | false =>
    have hg : d1985 p = 1 := by simpa only [d1990, d227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10787 p hg
    simpa only [d1990, d227, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1989 p = 1 := by simpa only [d1990, d227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10809 p hg
    simpa only [d1990, d227, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10811 (p : Pattern) (guard : d1964 p = 1) : d141 p ≤ (0 : Int) + d141 p := by
  omega
theorem compare10812 (p : Pattern) (guard : d1965 p = 1) : d256 p ≤ (0 : Int) + d141 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1960 p = 1 := by simpa only [d1965, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9803 p hg
    simpa only [d1965, d256, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1964 p = 1 := by simpa only [d1965, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10811 p hg
    simpa only [d1965, d256, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10813 (p : Pattern) (guard : d1968 p = 1) : d141 p ≤ (0 : Int) + d141 p := by
  omega
theorem compare10814 (p : Pattern) (guard : d1969 p = 1) : d256 p ≤ (0 : Int) + d141 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1964 p = 1 := by simpa only [d1969, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9829 p hg
    simpa only [d1969, d256, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1968 p = 1 := by simpa only [d1969, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10813 p hg
    simpa only [d1969, d256, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10815 (p : Pattern) (guard : d1970 p = 1) : d256 p ≤ (0 : Int) + d141 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1965 p = 1 := by simpa only [d1970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10812 p hg
    simpa only [d1970, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1969 p = 1 := by simpa only [d1970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10814 p hg
    simpa only [d1970, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10816 (p : Pattern) (guard : d1968 p = 1) : d152 p ≤ (0 : Int) + d152 p := by
  omega
theorem compare10817 (p : Pattern) (guard : d1969 p = 1) : d257 p ≤ (0 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1964 p = 1 := by simpa only [d1969, d257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9845 p hg
    simpa only [d1969, d257, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1968 p = 1 := by simpa only [d1969, d257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10816 p hg
    simpa only [d1969, d257, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10818 (p : Pattern) (guard : d1973 p = 1) : d258 p ≤ (0 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1968 p = 1 := by simpa only [d1973, d258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9855 p hg
    simpa only [d1973, d258, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1972 p = 1 := by simpa only [d1973, d258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10750 p hg
    simpa only [d1973, d258, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10819 (p : Pattern) (guard : d1974 p = 1) : d259 p ≤ (0 : Int) + d152 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1969 p = 1 := by simpa only [d1974, d259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10817 p hg
    simpa only [d1974, d259, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1973 p = 1 := by simpa only [d1974, d259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10818 p hg
    simpa only [d1974, d259, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10820 (p : Pattern) (guard : d1975 p = 1) : d260 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1970 p = 1 := by simpa only [d1975, d260, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10815 p hg
    simpa only [d1975, d260, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1974 p = 1 := by simpa only [d1975, d260, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10819 p hg
    simpa only [d1975, d260, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10821 (p : Pattern) (guard : d1957 p = 1) : d143 p ≤ (0 : Int) + d135 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1952 p = 1 := by simpa only [d1957, d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10605 p hg
    simpa only [d1957, d143, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1956 p = 1 := by simpa only [d1957, d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10653 p hg
    simpa only [d1957, d143, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10822 (p : Pattern) (guard : d1962 p = 1) : d144 p ≤ (0 : Int) + d136 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1957 p = 1 := by simpa only [d1962, d144, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10821 p hg
    simpa only [d1962, d144, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1961 p = 1 := by simpa only [d1962, d144, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10091 p hg
    simpa only [d1962, d144, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10823 (p : Pattern) (guard : d1967 p = 1) : d145 p ≤ (0 : Int) + d137 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1962 p = 1 := by simpa only [d1967, d145, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10822 p hg
    simpa only [d1967, d145, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1966 p = 1 := by simpa only [d1967, d145, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9573 p hg
    simpa only [d1967, d145, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10824 (p : Pattern) (guard : d1972 p = 1) : d149 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1967 p = 1 := by simpa only [d1972, d149, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10823 p hg
    simpa only [d1972, d149, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1971 p = 1 := by simpa only [d1972, d149, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10022 p hg
    simpa only [d1972, d149, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10825 (p : Pattern) (guard : d1973 p = 1) : d261 p ≤ (0 : Int) + d141 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1968 p = 1 := by simpa only [d1973, d261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9873 p hg
    simpa only [d1973, d261, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1972 p = 1 := by simpa only [d1973, d261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10824 p hg
    simpa only [d1973, d261, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10826 (p : Pattern) (guard : d1974 p = 1) : d262 p ≤ (0 : Int) + d141 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1969 p = 1 := by simpa only [d1974, d262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10814 p hg
    simpa only [d1974, d262, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1973 p = 1 := by simpa only [d1974, d262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10825 p hg
    simpa only [d1974, d262, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10827 (p : Pattern) (guard : d1973 p = 1) : d257 p ≤ (0 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1968 p = 1 := by simpa only [d1973, d257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9881 p hg
    simpa only [d1973, d257, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1972 p = 1 := by simpa only [d1973, d257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10750 p hg
    simpa only [d1973, d257, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10828 (p : Pattern) (guard : d1977 p = 1) : d263 p ≤ (0 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1972 p = 1 := by simpa only [d1977, d263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9888 p hg
    simpa only [d1977, d263, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1976 p = 1 := by simpa only [d1977, d263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10751 p hg
    simpa only [d1977, d263, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10829 (p : Pattern) (guard : d1978 p = 1) : d264 p ≤ (0 : Int) + d152 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1973 p = 1 := by simpa only [d1978, d264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10827 p hg
    simpa only [d1978, d264, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1977 p = 1 := by simpa only [d1978, d264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10828 p hg
    simpa only [d1978, d264, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10830 (p : Pattern) (guard : d1979 p = 1) : d265 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1974 p = 1 := by simpa only [d1979, d265, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10826 p hg
    simpa only [d1979, d265, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1978 p = 1 := by simpa only [d1979, d265, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10829 p hg
    simpa only [d1979, d265, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10831 (p : Pattern) (guard : d1980 p = 1) : d266 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1975 p = 1 := by simpa only [d1980, d266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10820 p hg
    simpa only [d1980, d266, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1979 p = 1 := by simpa only [d1980, d266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10830 p hg
    simpa only [d1980, d266, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10832 (p : Pattern) (guard : d1973 p = 1) : d267 p ≤ (0 : Int) + d141 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1968 p = 1 := by simpa only [d1973, d267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9899 p hg
    simpa only [d1973, d267, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1972 p = 1 := by simpa only [d1973, d267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10824 p hg
    simpa only [d1973, d267, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10833 (p : Pattern) (guard : d1974 p = 1) : d268 p ≤ (0 : Int) + d141 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1969 p = 1 := by simpa only [d1974, d268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10814 p hg
    simpa only [d1974, d268, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1973 p = 1 := by simpa only [d1974, d268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10832 p hg
    simpa only [d1974, d268, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10834 (p : Pattern) (guard : d1973 p = 1) : d269 p ≤ (0 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1968 p = 1 := by simpa only [d1973, d269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9909 p hg
    simpa only [d1973, d269, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1972 p = 1 := by simpa only [d1973, d269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10750 p hg
    simpa only [d1973, d269, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10835 (p : Pattern) (guard : d1977 p = 1) : d270 p ≤ (0 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1972 p = 1 := by simpa only [d1977, d270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9916 p hg
    simpa only [d1977, d270, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1976 p = 1 := by simpa only [d1977, d270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10751 p hg
    simpa only [d1977, d270, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10836 (p : Pattern) (guard : d1978 p = 1) : d271 p ≤ (0 : Int) + d152 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1973 p = 1 := by simpa only [d1978, d271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10834 p hg
    simpa only [d1978, d271, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1977 p = 1 := by simpa only [d1978, d271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10835 p hg
    simpa only [d1978, d271, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10837 (p : Pattern) (guard : d1979 p = 1) : d272 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1974 p = 1 := by simpa only [d1979, d272, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10833 p hg
    simpa only [d1979, d272, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1978 p = 1 := by simpa only [d1979, d272, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10836 p hg
    simpa only [d1979, d272, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10838 (p : Pattern) (guard : d1961 p = 1) : d157 p ≤ (0 : Int) + d135 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1956 p = 1 := by simpa only [d1961, d157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10653 p hg
    simpa only [d1961, d157, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1961, d157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10703 p hg
    simpa only [d1961, d157, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10839 (p : Pattern) (guard : d1966 p = 1) : d158 p ≤ (0 : Int) + d136 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d158, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10838 p hg
    simpa only [d1966, d158, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d158, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1966, d158, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10840 (p : Pattern) (guard : d1971 p = 1) : d159 p ≤ (0 : Int) + d137 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d159, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10839 p hg
    simpa only [d1971, d159, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d159, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1971, d159, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10841 (p : Pattern) (guard : d1976 p = 1) : d160 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1971 p = 1 := by simpa only [d1976, d160, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10840 p hg
    simpa only [d1976, d160, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1976, d160, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10046 p hg
    simpa only [d1976, d160, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10842 (p : Pattern) (guard : d1977 p = 1) : d273 p ≤ (0 : Int) + d141 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1972 p = 1 := by simpa only [d1977, d273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9926 p hg
    simpa only [d1977, d273, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1976 p = 1 := by simpa only [d1977, d273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10841 p hg
    simpa only [d1977, d273, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10843 (p : Pattern) (guard : d1978 p = 1) : d274 p ≤ (0 : Int) + d141 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1973 p = 1 := by simpa only [d1978, d274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10825 p hg
    simpa only [d1978, d274, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1977 p = 1 := by simpa only [d1978, d274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10842 p hg
    simpa only [d1978, d274, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10844 (p : Pattern) (guard : d1981 p = 1) : d275 p ≤ (0 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1976 p = 1 := by simpa only [d1981, d275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9935 p hg
    simpa only [d1981, d275, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1981, d275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9780 p hg
    simpa only [d1981, d275, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10845 (p : Pattern) (guard : d1982 p = 1) : d276 p ≤ (0 : Int) + d152 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1977 p = 1 := by simpa only [d1982, d276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10835 p hg
    simpa only [d1982, d276, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1981 p = 1 := by simpa only [d1982, d276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10844 p hg
    simpa only [d1982, d276, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10846 (p : Pattern) (guard : d1983 p = 1) : d277 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1978 p = 1 := by simpa only [d1983, d277, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10843 p hg
    simpa only [d1983, d277, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1982 p = 1 := by simpa only [d1983, d277, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10845 p hg
    simpa only [d1983, d277, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10847 (p : Pattern) (guard : d1984 p = 1) : d278 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1979 p = 1 := by simpa only [d1984, d278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10837 p hg
    simpa only [d1984, d278, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1983 p = 1 := by simpa only [d1984, d278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10846 p hg
    simpa only [d1984, d278, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10848 (p : Pattern) (guard : d1985 p = 1) : d279 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1980 p = 1 := by simpa only [d1985, d279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10831 p hg
    simpa only [d1985, d279, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1984 p = 1 := by simpa only [d1985, d279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10847 p hg
    simpa only [d1985, d279, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10849 (p : Pattern) (guard : d1977 p = 1) : d280 p ≤ (0 : Int) + d141 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1972 p = 1 := by simpa only [d1977, d280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9961 p hg
    simpa only [d1977, d280, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1976 p = 1 := by simpa only [d1977, d280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10841 p hg
    simpa only [d1977, d280, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10850 (p : Pattern) (guard : d1978 p = 1) : d281 p ≤ (0 : Int) + d141 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1973 p = 1 := by simpa only [d1978, d281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10825 p hg
    simpa only [d1978, d281, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1977 p = 1 := by simpa only [d1978, d281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10849 p hg
    simpa only [d1978, d281, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10851 (p : Pattern) (guard : d1977 p = 1) : d282 p ≤ (0 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1972 p = 1 := by simpa only [d1977, d282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9968 p hg
    simpa only [d1977, d282, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1976 p = 1 := by simpa only [d1977, d282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10751 p hg
    simpa only [d1977, d282, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10852 (p : Pattern) (guard : d1981 p = 1) : d283 p ≤ (0 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1976 p = 1 := by simpa only [d1981, d283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9973 p hg
    simpa only [d1981, d283, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1981, d283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9780 p hg
    simpa only [d1981, d283, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10853 (p : Pattern) (guard : d1982 p = 1) : d284 p ≤ (0 : Int) + d152 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1977 p = 1 := by simpa only [d1982, d284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10851 p hg
    simpa only [d1982, d284, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1981 p = 1 := by simpa only [d1982, d284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10852 p hg
    simpa only [d1982, d284, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10854 (p : Pattern) (guard : d1983 p = 1) : d285 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1978 p = 1 := by simpa only [d1983, d285, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10850 p hg
    simpa only [d1983, d285, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1982 p = 1 := by simpa only [d1983, d285, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10853 p hg
    simpa only [d1983, d285, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10855 (p : Pattern) (guard : d1984 p = 1) : d286 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1979 p = 1 := by simpa only [d1984, d286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10830 p hg
    simpa only [d1984, d286, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1983 p = 1 := by simpa only [d1984, d286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10854 p hg
    simpa only [d1984, d286, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10856 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d141 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10857 (p : Pattern) (guard : d1981 p = 1) : d283 p ≤ (0 : Int) + d141 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1976 p = 1 := by simpa only [d1981, d283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9990 p hg
    simpa only [d1981, d283, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1981, d283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10856 p hg
    simpa only [d1981, d283, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10858 (p : Pattern) (guard : d1982 p = 1) : d287 p ≤ (0 : Int) + d141 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1977 p = 1 := by simpa only [d1982, d287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10849 p hg
    simpa only [d1982, d287, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1981 p = 1 := by simpa only [d1982, d287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10857 p hg
    simpa only [d1982, d287, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10859 (p : Pattern) (guard : d1986 p = 1) : d288 p ≤ (0 : Int) + d152 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1981 p = 1 := by simpa only [d1986, d288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10844 p hg
    simpa only [d1986, d288, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1986, d288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9780 p hg
    simpa only [d1986, d288, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10860 (p : Pattern) (guard : d1987 p = 1) : d289 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1982 p = 1 := by simpa only [d1987, d289, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10858 p hg
    simpa only [d1987, d289, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1986 p = 1 := by simpa only [d1987, d289, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10859 p hg
    simpa only [d1987, d289, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10861 (p : Pattern) (guard : d1988 p = 1) : d290 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1983 p = 1 := by simpa only [d1988, d290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10846 p hg
    simpa only [d1988, d290, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1987 p = 1 := by simpa only [d1988, d290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10860 p hg
    simpa only [d1988, d290, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10862 (p : Pattern) (guard : d1989 p = 1) : d291 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1984 p = 1 := by simpa only [d1989, d291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10855 p hg
    simpa only [d1989, d291, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1988 p = 1 := by simpa only [d1989, d291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10861 p hg
    simpa only [d1989, d291, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10863 (p : Pattern) (guard : d1990 p = 1) : d292 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 80 with
  | false =>
    have hg : d1985 p = 1 := by simpa only [d1990, d292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10848 p hg
    simpa only [d1990, d292, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1989 p = 1 := by simpa only [d1990, d292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10862 p hg
    simpa only [d1990, d292, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10864 (p : Pattern) (guard : d1 p = 1) : d5 p ≤ (0 : Int) + d17 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare691 p hg
    simpa only [d5, d17, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d5, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare201 p hg
    simpa only [d5, d17, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10865 (p : Pattern) (guard : d1 p = 1) : d5 p ≤ (0 : Int) + d19 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10864 p hg
    simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare661 p hg
    simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10866 (p : Pattern) (guard : d1 p = 1) : d5 p ≤ (0 : Int) + d21 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9373 p hg
    simpa only [d5, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d5, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare201 p hg
    simpa only [d5, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10867 (p : Pattern) (guard : d1 p = 1) : d37 p ≤ (0 : Int) + d23 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d37, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10866 p hg
    simpa only [d37, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d37, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare201 p hg
    simpa only [d37, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10868 (p : Pattern) (guard : d1 p = 1) : d697 p ≤ (0 : Int) + d135 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d697, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10865 p hg
    simpa only [d697, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d697, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10867 p hg
    simpa only [d697, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10869 (p : Pattern) (guard : d1944 p = 1) : d37 p ≤ (0 : Int) + d23 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1944, d37, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10866 p hg
    simpa only [d1944, d37, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1943 p = 1 := by simpa only [d1944, d37, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9486 p hg
    simpa only [d1944, d37, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10870 (p : Pattern) (guard : d1945 p = 1) : d697 p ≤ (0 : Int) + d135 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1945, d697, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10865 p hg
    simpa only [d1945, d697, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1944 p = 1 := by simpa only [d1945, d697, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10869 p hg
    simpa only [d1945, d697, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10871 (p : Pattern) (guard : d1946 p = 1) : d697 p ≤ (0 : Int) + d135 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10868 p hg
    simpa only [d1946, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1945 p = 1 := by simpa only [d1946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10870 p hg
    simpa only [d1946, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10872 (p : Pattern) (guard : d1944 p = 1) : d37 p ≤ (0 : Int) + d2 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1944, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare661 p hg
    simpa only [d1944, d37, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1943 p = 1 := by simpa only [d1944, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9486 p hg
    simpa only [d1944, d37, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10873 (p : Pattern) (guard : d1945 p = 1) : d697 p ≤ (0 : Int) + d2 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1945, d697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare661 p hg
    simpa only [d1945, d697, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1944 p = 1 := by simpa only [d1945, d697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10872 p hg
    simpa only [d1945, d697, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10874 (p : Pattern) (guard : d1944 p = 1) : d11 p ≤ (0 : Int) + d2 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare666 p hg
    simpa only [d1944, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1943 p = 1 := by simpa only [d1944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9494 p hg
    simpa only [d1944, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10875 (p : Pattern) (guard : d1947 p = 1) : d39 p ≤ (0 : Int) + d2 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1943 p = 1 := by simpa only [d1947, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9494 p hg
    simpa only [d1947, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d1947, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4473 p hg
    simpa only [d1947, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10876 (p : Pattern) (guard : d1948 p = 1) : d698 p ≤ (0 : Int) + d2 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1944 p = 1 := by simpa only [d1948, d698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10874 p hg
    simpa only [d1948, d698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1947 p = 1 := by simpa only [d1948, d698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10875 p hg
    simpa only [d1948, d698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10877 (p : Pattern) (guard : d1949 p = 1) : d699 p ≤ (0 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1945 p = 1 := by simpa only [d1949, d699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10873 p hg
    simpa only [d1949, d699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1948 p = 1 := by simpa only [d1949, d699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10876 p hg
    simpa only [d1949, d699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10878 (p : Pattern) (guard : d1950 p = 1) : d700 p ≤ (0 : Int) + d136 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1946 p = 1 := by simpa only [d1950, d700, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10871 p hg
    simpa only [d1950, d700, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1949 p = 1 := by simpa only [d1950, d700, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10877 p hg
    simpa only [d1950, d700, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10879 (p : Pattern) (guard : d1944 p = 1) : d5 p ≤ (0 : Int) + d2 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare661 p hg
    simpa only [d1944, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1943 p = 1 := by simpa only [d1944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9505 p hg
    simpa only [d1944, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10880 (p : Pattern) (guard : d1948 p = 1) : d697 p ≤ (0 : Int) + d2 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1944 p = 1 := by simpa only [d1948, d697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10879 p hg
    simpa only [d1948, d697, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1947 p = 1 := by simpa only [d1948, d697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9531 p hg
    simpa only [d1948, d697, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10881 (p : Pattern) (guard : d1949 p = 1) : d697 p ≤ (0 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1945 p = 1 := by simpa only [d1949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10873 p hg
    simpa only [d1949, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1948 p = 1 := by simpa only [d1949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10880 p hg
    simpa only [d1949, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10882 (p : Pattern) (guard : d1947 p = 1) : d11 p ≤ (0 : Int) + d2 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1943 p = 1 := by simpa only [d1947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9494 p hg
    simpa only [d1947, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d1947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9514 p hg
    simpa only [d1947, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10883 (p : Pattern) (guard : d1952 p = 1) : d698 p ≤ (0 : Int) + d2 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1947 p = 1 := by simpa only [d1952, d698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10882 p hg
    simpa only [d1952, d698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1951 p = 1 := by simpa only [d1952, d698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9617 p hg
    simpa only [d1952, d698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10884 (p : Pattern) (guard : d1953 p = 1) : d699 p ≤ (0 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1948 p = 1 := by simpa only [d1953, d699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10880 p hg
    simpa only [d1953, d699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1952 p = 1 := by simpa only [d1953, d699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10883 p hg
    simpa only [d1953, d699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10885 (p : Pattern) (guard : d1954 p = 1) : d700 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1949 p = 1 := by simpa only [d1954, d700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10881 p hg
    simpa only [d1954, d700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1953 p = 1 := by simpa only [d1954, d700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10884 p hg
    simpa only [d1954, d700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10886 (p : Pattern) (guard : d1955 p = 1) : d700 p ≤ (0 : Int) + d137 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1950 p = 1 := by simpa only [d1955, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10878 p hg
    simpa only [d1955, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1954 p = 1 := by simpa only [d1955, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10885 p hg
    simpa only [d1955, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10887 (p : Pattern) (guard : d1 p = 1) : d5 p ≤ (0 : Int) + d23 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10866 p hg
    simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare661 p hg
    simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10888 (p : Pattern) (guard : d1945 p = 1) : d697 p ≤ (0 : Int) + d138 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1945, d697, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10887 p hg
    simpa only [d1945, d697, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1944 p = 1 := by simpa only [d1945, d697, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10872 p hg
    simpa only [d1945, d697, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10889 (p : Pattern) (guard : d1944 p = 1) : d5 p ≤ (0 : Int) + d23 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1944, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10866 p hg
    simpa only [d1944, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1943 p = 1 := by simpa only [d1944, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9505 p hg
    simpa only [d1944, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10890 (p : Pattern) (guard : d1948 p = 1) : d697 p ≤ (0 : Int) + d138 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1944 p = 1 := by simpa only [d1948, d697, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10889 p hg
    simpa only [d1948, d697, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1947 p = 1 := by simpa only [d1948, d697, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9531 p hg
    simpa only [d1948, d697, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10891 (p : Pattern) (guard : d1949 p = 1) : d697 p ≤ (0 : Int) + d138 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1945 p = 1 := by simpa only [d1949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10888 p hg
    simpa only [d1949, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1948 p = 1 := by simpa only [d1949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10890 p hg
    simpa only [d1949, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10892 (p : Pattern) (guard : d1954 p = 1) : d700 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1949 p = 1 := by simpa only [d1954, d700, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10891 p hg
    simpa only [d1954, d700, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1953 p = 1 := by simpa only [d1954, d700, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10884 p hg
    simpa only [d1954, d700, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10893 (p : Pattern) (guard : d1947 p = 1) : d5 p ≤ (0 : Int) + d2 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1943 p = 1 := by simpa only [d1947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9505 p hg
    simpa only [d1947, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d1947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9533 p hg
    simpa only [d1947, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10894 (p : Pattern) (guard : d1952 p = 1) : d697 p ≤ (0 : Int) + d2 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1947 p = 1 := by simpa only [d1952, d697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10893 p hg
    simpa only [d1952, d697, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1951 p = 1 := by simpa only [d1952, d697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9535 p hg
    simpa only [d1952, d697, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10895 (p : Pattern) (guard : d1953 p = 1) : d697 p ≤ (0 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1948 p = 1 := by simpa only [d1953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10880 p hg
    simpa only [d1953, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1952 p = 1 := by simpa only [d1953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10894 p hg
    simpa only [d1953, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10896 (p : Pattern) (guard : d1951 p = 1) : d11 p ≤ (0 : Int) + d2 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d1951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9514 p hg
    simpa only [d1951, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2790 p hg
    simpa only [d1951, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10897 (p : Pattern) (guard : d1956 p = 1) : d698 p ≤ (0 : Int) + d2 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1951 p = 1 := by simpa only [d1956, d698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10896 p hg
    simpa only [d1956, d698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1956, d698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2377 p hg
    simpa only [d1956, d698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10898 (p : Pattern) (guard : d1957 p = 1) : d699 p ≤ (0 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1952 p = 1 := by simpa only [d1957, d699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10894 p hg
    simpa only [d1957, d699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1956 p = 1 := by simpa only [d1957, d699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10897 p hg
    simpa only [d1957, d699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10899 (p : Pattern) (guard : d1958 p = 1) : d700 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1953 p = 1 := by simpa only [d1958, d700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10895 p hg
    simpa only [d1958, d700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1957 p = 1 := by simpa only [d1958, d700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10898 p hg
    simpa only [d1958, d700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10900 (p : Pattern) (guard : d1959 p = 1) : d700 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1954 p = 1 := by simpa only [d1959, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10892 p hg
    simpa only [d1959, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1958 p = 1 := by simpa only [d1959, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10899 p hg
    simpa only [d1959, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10901 (p : Pattern) (guard : d1960 p = 1) : d700 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1955 p = 1 := by simpa only [d1960, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10886 p hg
    simpa only [d1960, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1959 p = 1 := by simpa only [d1960, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10900 p hg
    simpa only [d1960, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10902 (p : Pattern) (guard : d1944 p = 1) : d5 p ≤ (0 : Int) + d19 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1944, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10864 p hg
    simpa only [d1944, d19, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1943 p = 1 := by simpa only [d1944, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9505 p hg
    simpa only [d1944, d19, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10903 (p : Pattern) (guard : d1943 p = 1) : d5 p ≤ (0 : Int) + d21 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1943, d5, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9373 p hg
    simpa only [d1943, d5, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d1943, d5, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1218 p hg
    simpa only [d1943, d5, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10904 (p : Pattern) (guard : d1947 p = 1) : d37 p ≤ (0 : Int) + d23 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1943 p = 1 := by simpa only [d1947, d37, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10903 p hg
    simpa only [d1947, d37, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d1947, d37, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4473 p hg
    simpa only [d1947, d37, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10905 (p : Pattern) (guard : d1948 p = 1) : d697 p ≤ (0 : Int) + d135 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1944 p = 1 := by simpa only [d1948, d697, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10902 p hg
    simpa only [d1948, d697, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1947 p = 1 := by simpa only [d1948, d697, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10904 p hg
    simpa only [d1948, d697, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10906 (p : Pattern) (guard : d1949 p = 1) : d697 p ≤ (0 : Int) + d135 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1945 p = 1 := by simpa only [d1949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10870 p hg
    simpa only [d1949, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1948 p = 1 := by simpa only [d1949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10905 p hg
    simpa only [d1949, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10907 (p : Pattern) (guard : d1954 p = 1) : d700 p ≤ (0 : Int) + d136 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1949 p = 1 := by simpa only [d1954, d700, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10906 p hg
    simpa only [d1954, d700, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1953 p = 1 := by simpa only [d1954, d700, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10884 p hg
    simpa only [d1954, d700, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10908 (p : Pattern) (guard : d1959 p = 1) : d700 p ≤ (0 : Int) + d137 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1954 p = 1 := by simpa only [d1959, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10907 p hg
    simpa only [d1959, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1958 p = 1 := by simpa only [d1959, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10899 p hg
    simpa only [d1959, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10909 (p : Pattern) (guard : d1947 p = 1) : d5 p ≤ (0 : Int) + d23 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1943 p = 1 := by simpa only [d1947, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10903 p hg
    simpa only [d1947, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d1947, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9533 p hg
    simpa only [d1947, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10910 (p : Pattern) (guard : d1952 p = 1) : d697 p ≤ (0 : Int) + d138 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1947 p = 1 := by simpa only [d1952, d697, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10909 p hg
    simpa only [d1952, d697, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1951 p = 1 := by simpa only [d1952, d697, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9535 p hg
    simpa only [d1952, d697, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10911 (p : Pattern) (guard : d1953 p = 1) : d697 p ≤ (0 : Int) + d138 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1948 p = 1 := by simpa only [d1953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10890 p hg
    simpa only [d1953, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1952 p = 1 := by simpa only [d1953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10910 p hg
    simpa only [d1953, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10912 (p : Pattern) (guard : d1958 p = 1) : d700 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1953 p = 1 := by simpa only [d1958, d700, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10911 p hg
    simpa only [d1958, d700, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1957 p = 1 := by simpa only [d1958, d700, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10898 p hg
    simpa only [d1958, d700, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10913 (p : Pattern) (guard : d1951 p = 1) : d5 p ≤ (0 : Int) + d2 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d1951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9533 p hg
    simpa only [d1951, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2786 p hg
    simpa only [d1951, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10914 (p : Pattern) (guard : d1956 p = 1) : d697 p ≤ (0 : Int) + d2 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1951 p = 1 := by simpa only [d1956, d697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10913 p hg
    simpa only [d1956, d697, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1956, d697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2375 p hg
    simpa only [d1956, d697, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10915 (p : Pattern) (guard : d1957 p = 1) : d697 p ≤ (0 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1952 p = 1 := by simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10894 p hg
    simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1956 p = 1 := by simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10914 p hg
    simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10916 (p : Pattern) (guard : d0 p = 1) : d698 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10917 (p : Pattern) (guard : d1961 p = 1) : d699 p ≤ (0 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1956 p = 1 := by simpa only [d1961, d699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10914 p hg
    simpa only [d1961, d699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1961, d699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10916 p hg
    simpa only [d1961, d699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10918 (p : Pattern) (guard : d1962 p = 1) : d700 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1957 p = 1 := by simpa only [d1962, d700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10915 p hg
    simpa only [d1962, d700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1961 p = 1 := by simpa only [d1962, d700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10917 p hg
    simpa only [d1962, d700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10919 (p : Pattern) (guard : d1963 p = 1) : d700 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1958 p = 1 := by simpa only [d1963, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10912 p hg
    simpa only [d1963, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1962 p = 1 := by simpa only [d1963, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10918 p hg
    simpa only [d1963, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban32Refined
