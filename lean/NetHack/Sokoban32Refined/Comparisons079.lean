/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Comparisons078
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare11060 (p : Pattern) (guard : d0 p = 1) : d727 p ≤ (0 : Int) + d152 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11061 (p : Pattern) (guard : d1981 p = 1) : d728 p ≤ (0 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1976 p = 1 := by simpa only [d1981, d728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11059 p hg
    simpa only [d1981, d728, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1981, d728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11060 p hg
    simpa only [d1981, d728, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11062 (p : Pattern) (guard : d1982 p = 1) : d729 p ≤ (0 : Int) + d152 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1977 p = 1 := by simpa only [d1982, d729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11058 p hg
    simpa only [d1982, d729, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1981 p = 1 := by simpa only [d1982, d729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11061 p hg
    simpa only [d1982, d729, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11063 (p : Pattern) (guard : d1983 p = 1) : d730 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1978 p = 1 := by simpa only [d1983, d730, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11056 p hg
    simpa only [d1983, d730, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1982 p = 1 := by simpa only [d1983, d730, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11062 p hg
    simpa only [d1983, d730, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11064 (p : Pattern) (guard : d1984 p = 1) : d731 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1979 p = 1 := by simpa only [d1984, d731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11048 p hg
    simpa only [d1984, d731, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1983 p = 1 := by simpa only [d1984, d731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11063 p hg
    simpa only [d1984, d731, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11065 (p : Pattern) (guard : d1985 p = 1) : d732 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1980 p = 1 := by simpa only [d1985, d732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11014 p hg
    simpa only [d1985, d732, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1984 p = 1 := by simpa only [d1985, d732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11064 p hg
    simpa only [d1985, d732, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11066 (p : Pattern) (guard : d1966 p = 1) : d700 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d700, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11025 p hg
    simpa only [d1966, d700, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d700, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7704 p hg
    simpa only [d1966, d700, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11067 (p : Pattern) (guard : d1971 p = 1) : d700 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11066 p hg
    simpa only [d1971, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7695 p hg
    simpa only [d1971, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11068 (p : Pattern) (guard : d1972 p = 1) : d700 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1967 p = 1 := by simpa only [d1972, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10993 p hg
    simpa only [d1972, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1971 p = 1 := by simpa only [d1972, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11067 p hg
    simpa only [d1972, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11069 (p : Pattern) (guard : d1973 p = 1) : d700 p ≤ (0 : Int) + d141 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1968 p = 1 := by simpa only [d1973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10938 p hg
    simpa only [d1973, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1972 p = 1 := by simpa only [d1973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11068 p hg
    simpa only [d1973, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11070 (p : Pattern) (guard : d1974 p = 1) : d700 p ≤ (0 : Int) + d141 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1969 p = 1 := by simpa only [d1974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10939 p hg
    simpa only [d1974, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1973 p = 1 := by simpa only [d1974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d1974, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11071 (p : Pattern) (guard : d1971 p = 1) : d699 p ≤ (0 : Int) + d2 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10957 p hg
    simpa only [d1971, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7704 p hg
    simpa only [d1971, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11072 (p : Pattern) (guard : d1972 p = 1) : d699 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1967 p = 1 := by simpa only [d1972, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11001 p hg
    simpa only [d1972, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1971 p = 1 := by simpa only [d1972, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11071 p hg
    simpa only [d1972, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11073 (p : Pattern) (guard : d1973 p = 1) : d699 p ≤ (0 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1968 p = 1 := by simpa only [d1973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10959 p hg
    simpa only [d1973, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1972 p = 1 := by simpa only [d1973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11072 p hg
    simpa only [d1973, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11074 (p : Pattern) (guard : d1976 p = 1) : d702 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1971 p = 1 := by simpa only [d1976, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11009 p hg
    simpa only [d1976, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1976, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7711 p hg
    simpa only [d1976, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11075 (p : Pattern) (guard : d1977 p = 1) : d702 p ≤ (0 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1972 p = 1 := by simpa only [d1977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10976 p hg
    simpa only [d1977, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1976 p = 1 := by simpa only [d1977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11074 p hg
    simpa only [d1977, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11076 (p : Pattern) (guard : d1978 p = 1) : d703 p ≤ (0 : Int) + d152 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1973 p = 1 := by simpa only [d1978, d703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11073 p hg
    simpa only [d1978, d703, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1977 p = 1 := by simpa only [d1978, d703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11075 p hg
    simpa only [d1978, d703, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11077 (p : Pattern) (guard : d1979 p = 1) : d704 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1974 p = 1 := by simpa only [d1979, d704, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11070 p hg
    simpa only [d1979, d704, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1978 p = 1 := by simpa only [d1979, d704, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11076 p hg
    simpa only [d1979, d704, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11078 (p : Pattern) (guard : d1966 p = 1) : d700 p ≤ (0 : Int) + d136 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d700, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11050 p hg
    simpa only [d1966, d700, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d700, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7704 p hg
    simpa only [d1966, d700, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11079 (p : Pattern) (guard : d1971 p = 1) : d700 p ≤ (0 : Int) + d137 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11078 p hg
    simpa only [d1971, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7695 p hg
    simpa only [d1971, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11080 (p : Pattern) (guard : d1976 p = 1) : d709 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1971 p = 1 := by simpa only [d1976, d709, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11079 p hg
    simpa only [d1976, d709, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1976, d709, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11053 p hg
    simpa only [d1976, d709, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11081 (p : Pattern) (guard : d1977 p = 1) : d710 p ≤ (0 : Int) + d141 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1972 p = 1 := by simpa only [d1977, d710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11068 p hg
    simpa only [d1977, d710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1976 p = 1 := by simpa only [d1977, d710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11080 p hg
    simpa only [d1977, d710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11082 (p : Pattern) (guard : d1978 p = 1) : d710 p ≤ (0 : Int) + d141 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1973 p = 1 := by simpa only [d1978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10998 p hg
    simpa only [d1978, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1977 p = 1 := by simpa only [d1978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11081 p hg
    simpa only [d1978, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11083 (p : Pattern) (guard : d1966 p = 1) : d699 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11007 p hg
    simpa only [d1966, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7704 p hg
    simpa only [d1966, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11084 (p : Pattern) (guard : d1971 p = 1) : d699 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11083 p hg
    simpa only [d1971, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7704 p hg
    simpa only [d1971, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11085 (p : Pattern) (guard : d1976 p = 1) : d712 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1971 p = 1 := by simpa only [d1976, d712, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11084 p hg
    simpa only [d1976, d712, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1976, d712, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7726 p hg
    simpa only [d1976, d712, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11086 (p : Pattern) (guard : d1977 p = 1) : d713 p ≤ (0 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1972 p = 1 := by simpa only [d1977, d713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11072 p hg
    simpa only [d1977, d713, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1976 p = 1 := by simpa only [d1977, d713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11085 p hg
    simpa only [d1977, d713, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11087 (p : Pattern) (guard : d0 p = 1) : d714 p ≤ (0 : Int) + d152 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11088 (p : Pattern) (guard : d1981 p = 1) : d715 p ≤ (0 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1976 p = 1 := by simpa only [d1981, d715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11074 p hg
    simpa only [d1981, d715, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1981, d715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11087 p hg
    simpa only [d1981, d715, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11089 (p : Pattern) (guard : d1982 p = 1) : d716 p ≤ (0 : Int) + d152 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1977 p = 1 := by simpa only [d1982, d716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11086 p hg
    simpa only [d1982, d716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1981 p = 1 := by simpa only [d1982, d716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11088 p hg
    simpa only [d1982, d716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11090 (p : Pattern) (guard : d1983 p = 1) : d733 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1978 p = 1 := by simpa only [d1983, d733, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11082 p hg
    simpa only [d1983, d733, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1982 p = 1 := by simpa only [d1983, d733, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11089 p hg
    simpa only [d1983, d733, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11091 (p : Pattern) (guard : d1984 p = 1) : d734 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1979 p = 1 := by simpa only [d1984, d734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11077 p hg
    simpa only [d1984, d734, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1983 p = 1 := by simpa only [d1984, d734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11090 p hg
    simpa only [d1984, d734, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11092 (p : Pattern) (guard : d1976 p = 1) : d719 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1971 p = 1 := by simpa only [d1976, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11052 p hg
    simpa only [d1976, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1976, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8321 p hg
    simpa only [d1976, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11093 (p : Pattern) (guard : d1977 p = 1) : d719 p ≤ (0 : Int) + d141 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1972 p = 1 := by simpa only [d1977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11028 p hg
    simpa only [d1977, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1976 p = 1 := by simpa only [d1977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11092 p hg
    simpa only [d1977, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11094 (p : Pattern) (guard : d1978 p = 1) : d720 p ≤ (0 : Int) + d141 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1973 p = 1 := by simpa only [d1978, d720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d1978, d720, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1977 p = 1 := by simpa only [d1978, d720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11093 p hg
    simpa only [d1978, d720, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11095 (p : Pattern) (guard : d0 p = 1) : d705 p ≤ (0 : Int) + d152 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11096 (p : Pattern) (guard : d1981 p = 1) : d705 p ≤ (0 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1976 p = 1 := by simpa only [d1981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11059 p hg
    simpa only [d1981, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11095 p hg
    simpa only [d1981, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11097 (p : Pattern) (guard : d1982 p = 1) : d735 p ≤ (0 : Int) + d152 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1977 p = 1 := by simpa only [d1982, d735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11046 p hg
    simpa only [d1982, d735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1981 p = 1 := by simpa only [d1982, d735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11096 p hg
    simpa only [d1982, d735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11098 (p : Pattern) (guard : d1983 p = 1) : d736 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1978 p = 1 := by simpa only [d1983, d736, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11094 p hg
    simpa only [d1983, d736, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1982 p = 1 := by simpa only [d1983, d736, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11097 p hg
    simpa only [d1983, d736, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11099 (p : Pattern) (guard : d0 p = 1) : d698 p ≤ (0 : Int) + d135 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11100 (p : Pattern) (guard : d1961 p = 1) : d699 p ≤ (0 : Int) + d135 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1956 p = 1 := by simpa only [d1961, d699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10990 p hg
    simpa only [d1961, d699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1961, d699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11099 p hg
    simpa only [d1961, d699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11101 (p : Pattern) (guard : d1966 p = 1) : d702 p ≤ (0 : Int) + d136 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d702, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11100 p hg
    simpa only [d1966, d702, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d702, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10966 p hg
    simpa only [d1966, d702, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11102 (p : Pattern) (guard : d1971 p = 1) : d702 p ≤ (0 : Int) + d137 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11101 p hg
    simpa only [d1971, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7711 p hg
    simpa only [d1971, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11103 (p : Pattern) (guard : d0 p = 1) : d702 p ≤ (0 : Int) + d140 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11104 (p : Pattern) (guard : d1976 p = 1) : d702 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1971 p = 1 := by simpa only [d1976, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11102 p hg
    simpa only [d1976, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1976, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11103 p hg
    simpa only [d1976, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11105 (p : Pattern) (guard : d0 p = 1) : d714 p ≤ (0 : Int) + d141 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11106 (p : Pattern) (guard : d1981 p = 1) : d715 p ≤ (0 : Int) + d141 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1976 p = 1 := by simpa only [d1981, d715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11104 p hg
    simpa only [d1981, d715, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1981, d715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11105 p hg
    simpa only [d1981, d715, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11107 (p : Pattern) (guard : d1982 p = 1) : d737 p ≤ (0 : Int) + d141 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1977 p = 1 := by simpa only [d1982, d737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11081 p hg
    simpa only [d1982, d737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1981 p = 1 := by simpa only [d1982, d737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11106 p hg
    simpa only [d1982, d737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11108 (p : Pattern) (guard : d1986 p = 1) : d738 p ≤ (0 : Int) + d152 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1981 p = 1 := by simpa only [d1986, d738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11061 p hg
    simpa only [d1986, d738, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1986, d738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9780 p hg
    simpa only [d1986, d738, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11109 (p : Pattern) (guard : d1987 p = 1) : d739 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1982 p = 1 := by simpa only [d1987, d739, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11107 p hg
    simpa only [d1987, d739, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1986 p = 1 := by simpa only [d1987, d739, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11108 p hg
    simpa only [d1987, d739, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11110 (p : Pattern) (guard : d1988 p = 1) : d740 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1983 p = 1 := by simpa only [d1988, d740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11098 p hg
    simpa only [d1988, d740, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1987 p = 1 := by simpa only [d1988, d740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11109 p hg
    simpa only [d1988, d740, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11111 (p : Pattern) (guard : d1989 p = 1) : d741 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1984 p = 1 := by simpa only [d1989, d741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11091 p hg
    simpa only [d1989, d741, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1988 p = 1 := by simpa only [d1989, d741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11110 p hg
    simpa only [d1989, d741, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11112 (p : Pattern) (guard : d1990 p = 1) : d742 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 80 with
  | false =>
    have hg : d1985 p = 1 := by simpa only [d1990, d742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11065 p hg
    simpa only [d1990, d742, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1989 p = 1 := by simpa only [d1990, d742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11111 p hg
    simpa only [d1990, d742, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11113 (p : Pattern) (guard : d1969 p = 1) : d141 p ≤ (0 : Int) + d141 p := by
  omega
theorem compare11114 (p : Pattern) (guard : d1973 p = 1) : d150 p ≤ (0 : Int) + d141 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1968 p = 1 := by simpa only [d1973, d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10813 p hg
    simpa only [d1973, d150, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1972 p = 1 := by simpa only [d1973, d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10824 p hg
    simpa only [d1973, d150, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11115 (p : Pattern) (guard : d1974 p = 1) : d151 p ≤ (0 : Int) + d141 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1969 p = 1 := by simpa only [d1974, d151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11113 p hg
    simpa only [d1974, d151, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1973 p = 1 := by simpa only [d1974, d151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11114 p hg
    simpa only [d1974, d151, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11116 (p : Pattern) (guard : d1979 p = 1) : d156 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1974 p = 1 := by simpa only [d1979, d156, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11115 p hg
    simpa only [d1979, d156, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1978 p = 1 := by simpa only [d1979, d156, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10753 p hg
    simpa only [d1979, d156, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11117 (p : Pattern) (guard : d1977 p = 1) : d161 p ≤ (0 : Int) + d141 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1972 p = 1 := by simpa only [d1977, d161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10824 p hg
    simpa only [d1977, d161, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1976 p = 1 := by simpa only [d1977, d161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10841 p hg
    simpa only [d1977, d161, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11118 (p : Pattern) (guard : d1978 p = 1) : d162 p ≤ (0 : Int) + d141 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1973 p = 1 := by simpa only [d1978, d162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11114 p hg
    simpa only [d1978, d162, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1977 p = 1 := by simpa only [d1978, d162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11117 p hg
    simpa only [d1978, d162, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11119 (p : Pattern) (guard : d1983 p = 1) : d165 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1978 p = 1 := by simpa only [d1983, d165, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11118 p hg
    simpa only [d1983, d165, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1982 p = 1 := by simpa only [d1983, d165, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10784 p hg
    simpa only [d1983, d165, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11120 (p : Pattern) (guard : d1984 p = 1) : d166 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1979 p = 1 := by simpa only [d1984, d166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11116 p hg
    simpa only [d1984, d166, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1983 p = 1 := by simpa only [d1984, d166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11119 p hg
    simpa only [d1984, d166, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11121 (p : Pattern) (guard : d1981 p = 1) : d167 p ≤ (0 : Int) + d141 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1976 p = 1 := by simpa only [d1981, d167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10841 p hg
    simpa only [d1981, d167, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1981, d167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10856 p hg
    simpa only [d1981, d167, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11122 (p : Pattern) (guard : d1982 p = 1) : d168 p ≤ (0 : Int) + d141 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1977 p = 1 := by simpa only [d1982, d168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11117 p hg
    simpa only [d1982, d168, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1981 p = 1 := by simpa only [d1982, d168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11121 p hg
    simpa only [d1982, d168, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11123 (p : Pattern) (guard : d1987 p = 1) : d170 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1982 p = 1 := by simpa only [d1987, d170, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11122 p hg
    simpa only [d1987, d170, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1986 p = 1 := by simpa only [d1987, d170, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10806 p hg
    simpa only [d1987, d170, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11124 (p : Pattern) (guard : d1988 p = 1) : d171 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1983 p = 1 := by simpa only [d1988, d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11119 p hg
    simpa only [d1988, d171, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1987 p = 1 := by simpa only [d1988, d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11123 p hg
    simpa only [d1988, d171, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11125 (p : Pattern) (guard : d1989 p = 1) : d172 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1984 p = 1 := by simpa only [d1989, d172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11120 p hg
    simpa only [d1989, d172, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1988 p = 1 := by simpa only [d1989, d172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11124 p hg
    simpa only [d1989, d172, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11126 (p : Pattern) (guard : d1990 p = 1) : d173 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 80 with
  | false =>
    have hg : d1985 p = 1 := by simpa only [d1990, d173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9941 p hg
    simpa only [d1990, d173, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1989 p = 1 := by simpa only [d1990, d173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11125 p hg
    simpa only [d1990, d173, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11127 (p : Pattern) (guard : d1985 p = 1) : d174 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1980 p = 1 := by simpa only [d1985, d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9894 p hg
    simpa only [d1985, d174, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1984 p = 1 := by simpa only [d1985, d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11120 p hg
    simpa only [d1985, d174, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11128 (p : Pattern) (guard : d1989 p = 1) : d175 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1984 p = 1 := by simpa only [d1989, d175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9978 p hg
    simpa only [d1989, d175, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1988 p = 1 := by simpa only [d1989, d175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11124 p hg
    simpa only [d1989, d175, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11129 (p : Pattern) (guard : d1990 p = 1) : d176 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 80 with
  | false =>
    have hg : d1985 p = 1 := by simpa only [d1990, d176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11127 p hg
    simpa only [d1990, d176, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1989 p = 1 := by simpa only [d1990, d176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11128 p hg
    simpa only [d1990, d176, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11130 (p : Pattern) (guard : d1980 p = 1) : d177 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1975 p = 1 := by simpa only [d1980, d177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9862 p hg
    simpa only [d1980, d177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1979 p = 1 := by simpa only [d1980, d177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11116 p hg
    simpa only [d1980, d177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11131 (p : Pattern) (guard : d1984 p = 1) : d178 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1979 p = 1 := by simpa only [d1984, d178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9921 p hg
    simpa only [d1984, d178, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1983 p = 1 := by simpa only [d1984, d178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11119 p hg
    simpa only [d1984, d178, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11132 (p : Pattern) (guard : d1985 p = 1) : d179 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1980 p = 1 := by simpa only [d1985, d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11130 p hg
    simpa only [d1985, d179, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1984 p = 1 := by simpa only [d1985, d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11131 p hg
    simpa only [d1985, d179, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11133 (p : Pattern) (guard : d1984 p = 1) : d180 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1979 p = 1 := by simpa only [d1984, d180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9957 p hg
    simpa only [d1984, d180, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1983 p = 1 := by simpa only [d1984, d180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11119 p hg
    simpa only [d1984, d180, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11134 (p : Pattern) (guard : d1988 p = 1) : d181 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1983 p = 1 := by simpa only [d1988, d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9987 p hg
    simpa only [d1988, d181, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1987 p = 1 := by simpa only [d1988, d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11123 p hg
    simpa only [d1988, d181, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11135 (p : Pattern) (guard : d1989 p = 1) : d182 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1984 p = 1 := by simpa only [d1989, d182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11133 p hg
    simpa only [d1989, d182, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1988 p = 1 := by simpa only [d1989, d182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11134 p hg
    simpa only [d1989, d182, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11136 (p : Pattern) (guard : d1990 p = 1) : d183 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 80 with
  | false =>
    have hg : d1985 p = 1 := by simpa only [d1990, d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11132 p hg
    simpa only [d1990, d183, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1989 p = 1 := by simpa only [d1990, d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11135 p hg
    simpa only [d1990, d183, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11137 (p : Pattern) (guard : d1 p = 1) : d7 p ≤ (0 : Int) + d19 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d7, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare693 p hg
    simpa only [d7, d19, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d7, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare201 p hg
    simpa only [d7, d19, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11138 (p : Pattern) (guard : d1 p = 1) : d7 p ≤ (0 : Int) + d135 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11137 p hg
    simpa only [d135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9484 p hg
    simpa only [d135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11139 (p : Pattern) (guard : d1945 p = 1) : d7 p ≤ (0 : Int) + d135 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1945, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11137 p hg
    simpa only [d1945, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1944 p = 1 := by simpa only [d1945, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9487 p hg
    simpa only [d1945, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11140 (p : Pattern) (guard : d1946 p = 1) : d7 p ≤ (0 : Int) + d135 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11138 p hg
    simpa only [d1946, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1945 p = 1 := by simpa only [d1946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11139 p hg
    simpa only [d1946, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11141 (p : Pattern) (guard : d1 p = 1) : d7 p ≤ (0 : Int) + d2 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9490 p hg
    simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare201 p hg
    simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11142 (p : Pattern) (guard : d1945 p = 1) : d7 p ≤ (0 : Int) + d2 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11141 p hg
    simpa only [d1945, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1944 p = 1 := by simpa only [d1945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9492 p hg
    simpa only [d1945, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11143 (p : Pattern) (guard : d1944 p = 1) : d13 p ≤ (0 : Int) + d2 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1944, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2164 p hg
    simpa only [d1944, d13, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1943 p = 1 := by simpa only [d1944, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9486 p hg
    simpa only [d1944, d13, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11144 (p : Pattern) (guard : d1948 p = 1) : d13 p ≤ (0 : Int) + d2 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1944 p = 1 := by simpa only [d1948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11143 p hg
    simpa only [d1948, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1947 p = 1 := by simpa only [d1948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9497 p hg
    simpa only [d1948, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11145 (p : Pattern) (guard : d1949 p = 1) : d653 p ≤ (0 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1945 p = 1 := by simpa only [d1949, d653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11142 p hg
    simpa only [d1949, d653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1948 p = 1 := by simpa only [d1949, d653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11144 p hg
    simpa only [d1949, d653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11146 (p : Pattern) (guard : d1950 p = 1) : d654 p ≤ (0 : Int) + d136 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1946 p = 1 := by simpa only [d1950, d654, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11140 p hg
    simpa only [d1950, d654, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1949 p = 1 := by simpa only [d1950, d654, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11145 p hg
    simpa only [d1950, d654, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11147 (p : Pattern) (guard : d1948 p = 1) : d7 p ≤ (0 : Int) + d2 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1944 p = 1 := by simpa only [d1948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9492 p hg
    simpa only [d1948, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1947 p = 1 := by simpa only [d1948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9508 p hg
    simpa only [d1948, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11148 (p : Pattern) (guard : d1949 p = 1) : d7 p ≤ (0 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1945 p = 1 := by simpa only [d1949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11142 p hg
    simpa only [d1949, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1948 p = 1 := by simpa only [d1949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11147 p hg
    simpa only [d1949, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11149 (p : Pattern) (guard : d1952 p = 1) : d13 p ≤ (0 : Int) + d2 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1947 p = 1 := by simpa only [d1952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9497 p hg
    simpa only [d1952, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1951 p = 1 := by simpa only [d1952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9517 p hg
    simpa only [d1952, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11150 (p : Pattern) (guard : d1953 p = 1) : d653 p ≤ (0 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1948 p = 1 := by simpa only [d1953, d653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11147 p hg
    simpa only [d1953, d653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1952 p = 1 := by simpa only [d1953, d653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11149 p hg
    simpa only [d1953, d653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11151 (p : Pattern) (guard : d1954 p = 1) : d654 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1949 p = 1 := by simpa only [d1954, d654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11148 p hg
    simpa only [d1954, d654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1953 p = 1 := by simpa only [d1954, d654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11150 p hg
    simpa only [d1954, d654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11152 (p : Pattern) (guard : d1955 p = 1) : d654 p ≤ (0 : Int) + d137 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1950 p = 1 := by simpa only [d1955, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11146 p hg
    simpa only [d1955, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1954 p = 1 := by simpa only [d1955, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11151 p hg
    simpa only [d1955, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11153 (p : Pattern) (guard : d1945 p = 1) : d7 p ≤ (0 : Int) + d138 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1945, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9484 p hg
    simpa only [d1945, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1944 p = 1 := by simpa only [d1945, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9492 p hg
    simpa only [d1945, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11154 (p : Pattern) (guard : d1948 p = 1) : d7 p ≤ (0 : Int) + d138 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1944 p = 1 := by simpa only [d1948, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9487 p hg
    simpa only [d1948, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1947 p = 1 := by simpa only [d1948, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9508 p hg
    simpa only [d1948, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11155 (p : Pattern) (guard : d1949 p = 1) : d7 p ≤ (0 : Int) + d138 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1945 p = 1 := by simpa only [d1949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11153 p hg
    simpa only [d1949, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1948 p = 1 := by simpa only [d1949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11154 p hg
    simpa only [d1949, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11156 (p : Pattern) (guard : d1954 p = 1) : d654 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1949 p = 1 := by simpa only [d1954, d654, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11155 p hg
    simpa only [d1954, d654, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1953 p = 1 := by simpa only [d1954, d654, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11150 p hg
    simpa only [d1954, d654, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11157 (p : Pattern) (guard : d1952 p = 1) : d7 p ≤ (0 : Int) + d2 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1947 p = 1 := by simpa only [d1952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9508 p hg
    simpa only [d1952, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1951 p = 1 := by simpa only [d1952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9549 p hg
    simpa only [d1952, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11158 (p : Pattern) (guard : d1953 p = 1) : d7 p ≤ (0 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1948 p = 1 := by simpa only [d1953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11147 p hg
    simpa only [d1953, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1952 p = 1 := by simpa only [d1953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11157 p hg
    simpa only [d1953, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11159 (p : Pattern) (guard : d1956 p = 1) : d13 p ≤ (0 : Int) + d2 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1951 p = 1 := by simpa only [d1956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9517 p hg
    simpa only [d1956, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2353 p hg
    simpa only [d1956, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11160 (p : Pattern) (guard : d1957 p = 1) : d653 p ≤ (0 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1952 p = 1 := by simpa only [d1957, d653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11157 p hg
    simpa only [d1957, d653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1956 p = 1 := by simpa only [d1957, d653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11159 p hg
    simpa only [d1957, d653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11161 (p : Pattern) (guard : d1958 p = 1) : d654 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1953 p = 1 := by simpa only [d1958, d654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11158 p hg
    simpa only [d1958, d654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1957 p = 1 := by simpa only [d1958, d654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11160 p hg
    simpa only [d1958, d654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11162 (p : Pattern) (guard : d1959 p = 1) : d654 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1954 p = 1 := by simpa only [d1959, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11156 p hg
    simpa only [d1959, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1958 p = 1 := by simpa only [d1959, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11161 p hg
    simpa only [d1959, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11163 (p : Pattern) (guard : d1960 p = 1) : d654 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1955 p = 1 := by simpa only [d1960, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11152 p hg
    simpa only [d1960, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1959 p = 1 := by simpa only [d1960, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11162 p hg
    simpa only [d1960, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11164 (p : Pattern) (guard : d1944 p = 1) : d7 p ≤ (0 : Int) + d19 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1944, d7, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare693 p hg
    simpa only [d1944, d7, d19, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1943 p = 1 := by simpa only [d1944, d7, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9486 p hg
    simpa only [d1944, d7, d19, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11165 (p : Pattern) (guard : d1948 p = 1) : d7 p ≤ (0 : Int) + d135 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1944 p = 1 := by simpa only [d1948, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11164 p hg
    simpa only [d1948, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1947 p = 1 := by simpa only [d1948, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9526 p hg
    simpa only [d1948, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11166 (p : Pattern) (guard : d1949 p = 1) : d7 p ≤ (0 : Int) + d135 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1945 p = 1 := by simpa only [d1949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11139 p hg
    simpa only [d1949, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1948 p = 1 := by simpa only [d1949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11165 p hg
    simpa only [d1949, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11167 (p : Pattern) (guard : d1954 p = 1) : d654 p ≤ (0 : Int) + d136 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1949 p = 1 := by simpa only [d1954, d654, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11166 p hg
    simpa only [d1954, d654, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1953 p = 1 := by simpa only [d1954, d654, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11150 p hg
    simpa only [d1954, d654, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11168 (p : Pattern) (guard : d1959 p = 1) : d654 p ≤ (0 : Int) + d137 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1954 p = 1 := by simpa only [d1959, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11167 p hg
    simpa only [d1959, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1958 p = 1 := by simpa only [d1959, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11161 p hg
    simpa only [d1959, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11169 (p : Pattern) (guard : d1952 p = 1) : d7 p ≤ (0 : Int) + d138 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1947 p = 1 := by simpa only [d1952, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9526 p hg
    simpa only [d1952, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1951 p = 1 := by simpa only [d1952, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9549 p hg
    simpa only [d1952, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11170 (p : Pattern) (guard : d1953 p = 1) : d7 p ≤ (0 : Int) + d138 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1948 p = 1 := by simpa only [d1953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11154 p hg
    simpa only [d1953, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1952 p = 1 := by simpa only [d1953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11169 p hg
    simpa only [d1953, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11171 (p : Pattern) (guard : d1958 p = 1) : d654 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1953 p = 1 := by simpa only [d1958, d654, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11170 p hg
    simpa only [d1958, d654, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1957 p = 1 := by simpa only [d1958, d654, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11160 p hg
    simpa only [d1958, d654, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11172 (p : Pattern) (guard : d1956 p = 1) : d7 p ≤ (0 : Int) + d2 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1951 p = 1 := by simpa only [d1956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9549 p hg
    simpa only [d1956, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2350 p hg
    simpa only [d1956, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11173 (p : Pattern) (guard : d1957 p = 1) : d7 p ≤ (0 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1952 p = 1 := by simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11157 p hg
    simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1956 p = 1 := by simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11172 p hg
    simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11174 (p : Pattern) (guard : d1961 p = 1) : d653 p ≤ (0 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1956 p = 1 := by simpa only [d1961, d653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11172 p hg
    simpa only [d1961, d653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1961, d653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2353 p hg
    simpa only [d1961, d653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11175 (p : Pattern) (guard : d1962 p = 1) : d654 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1957 p = 1 := by simpa only [d1962, d654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11173 p hg
    simpa only [d1962, d654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1961 p = 1 := by simpa only [d1962, d654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11174 p hg
    simpa only [d1962, d654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11176 (p : Pattern) (guard : d1963 p = 1) : d654 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1958 p = 1 := by simpa only [d1963, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11171 p hg
    simpa only [d1963, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1962 p = 1 := by simpa only [d1963, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11175 p hg
    simpa only [d1963, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11177 (p : Pattern) (guard : d1964 p = 1) : d654 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1959 p = 1 := by simpa only [d1964, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11168 p hg
    simpa only [d1964, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1963 p = 1 := by simpa only [d1964, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11176 p hg
    simpa only [d1964, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11178 (p : Pattern) (guard : d1965 p = 1) : d654 p ≤ (0 : Int) + d141 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1960 p = 1 := by simpa only [d1965, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11163 p hg
    simpa only [d1965, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1964 p = 1 := by simpa only [d1965, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11177 p hg
    simpa only [d1965, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11179 (p : Pattern) (guard : d1947 p = 1) : d7 p ≤ (0 : Int) + d19 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1943 p = 1 := by simpa only [d1947, d7, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9558 p hg
    simpa only [d1947, d7, d19, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d1947, d7, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4473 p hg
    simpa only [d1947, d7, d19, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11180 (p : Pattern) (guard : d1952 p = 1) : d7 p ≤ (0 : Int) + d135 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1947 p = 1 := by simpa only [d1952, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11179 p hg
    simpa only [d1952, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1951 p = 1 := by simpa only [d1952, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9561 p hg
    simpa only [d1952, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11181 (p : Pattern) (guard : d1953 p = 1) : d7 p ≤ (0 : Int) + d135 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1948 p = 1 := by simpa only [d1953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11165 p hg
    simpa only [d1953, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1952 p = 1 := by simpa only [d1953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11180 p hg
    simpa only [d1953, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11182 (p : Pattern) (guard : d1958 p = 1) : d654 p ≤ (0 : Int) + d136 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1953 p = 1 := by simpa only [d1958, d654, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11181 p hg
    simpa only [d1958, d654, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1957 p = 1 := by simpa only [d1958, d654, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11160 p hg
    simpa only [d1958, d654, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11183 (p : Pattern) (guard : d1963 p = 1) : d654 p ≤ (0 : Int) + d137 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1958 p = 1 := by simpa only [d1963, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11182 p hg
    simpa only [d1963, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1962 p = 1 := by simpa only [d1963, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11175 p hg
    simpa only [d1963, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11184 (p : Pattern) (guard : d1956 p = 1) : d7 p ≤ (0 : Int) + d138 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1951 p = 1 := by simpa only [d1956, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9561 p hg
    simpa only [d1956, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1956, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2350 p hg
    simpa only [d1956, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11185 (p : Pattern) (guard : d1957 p = 1) : d7 p ≤ (0 : Int) + d138 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1952 p = 1 := by simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11169 p hg
    simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1956 p = 1 := by simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11184 p hg
    simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11186 (p : Pattern) (guard : d1962 p = 1) : d654 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1957 p = 1 := by simpa only [d1962, d654, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11185 p hg
    simpa only [d1962, d654, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1961 p = 1 := by simpa only [d1962, d654, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11174 p hg
    simpa only [d1962, d654, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11187 (p : Pattern) (guard : d1961 p = 1) : d7 p ≤ (0 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1956 p = 1 := by simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11172 p hg
    simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2350 p hg
    simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11188 (p : Pattern) (guard : d1966 p = 1) : d654 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11187 p hg
    simpa only [d1966, d654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7094 p hg
    simpa only [d1966, d654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11189 (p : Pattern) (guard : d1967 p = 1) : d654 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1962 p = 1 := by simpa only [d1967, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11186 p hg
    simpa only [d1967, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1966 p = 1 := by simpa only [d1967, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11188 p hg
    simpa only [d1967, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11190 (p : Pattern) (guard : d1968 p = 1) : d654 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1963 p = 1 := by simpa only [d1968, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11183 p hg
    simpa only [d1968, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1967 p = 1 := by simpa only [d1968, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11189 p hg
    simpa only [d1968, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11191 (p : Pattern) (guard : d1969 p = 1) : d654 p ≤ (0 : Int) + d141 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1964 p = 1 := by simpa only [d1969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11177 p hg
    simpa only [d1969, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1968 p = 1 := by simpa only [d1969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11190 p hg
    simpa only [d1969, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11192 (p : Pattern) (guard : d1970 p = 1) : d654 p ≤ (0 : Int) + d141 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1965 p = 1 := by simpa only [d1970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11178 p hg
    simpa only [d1970, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1969 p = 1 := by simpa only [d1970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11191 p hg
    simpa only [d1970, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11193 (p : Pattern) (guard : d1944 p = 1) : d13 p ≤ (0 : Int) + d23 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1944, d13, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare700 p hg
    simpa only [d1944, d13, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1943 p = 1 := by simpa only [d1944, d13, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9486 p hg
    simpa only [d1944, d13, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11194 (p : Pattern) (guard : d1948 p = 1) : d13 p ≤ (0 : Int) + d138 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1944 p = 1 := by simpa only [d1948, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11193 p hg
    simpa only [d1948, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1947 p = 1 := by simpa only [d1948, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9497 p hg
    simpa only [d1948, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11195 (p : Pattern) (guard : d1949 p = 1) : d653 p ≤ (0 : Int) + d138 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1945 p = 1 := by simpa only [d1949, d653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11153 p hg
    simpa only [d1949, d653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1948 p = 1 := by simpa only [d1949, d653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11194 p hg
    simpa only [d1949, d653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11196 (p : Pattern) (guard : d1954 p = 1) : d653 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1949 p = 1 := by simpa only [d1954, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11195 p hg
    simpa only [d1954, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1953 p = 1 := by simpa only [d1954, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11150 p hg
    simpa only [d1954, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11197 (p : Pattern) (guard : d1958 p = 1) : d653 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1953 p = 1 := by simpa only [d1958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11150 p hg
    simpa only [d1958, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1957 p = 1 := by simpa only [d1958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11160 p hg
    simpa only [d1958, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11198 (p : Pattern) (guard : d1959 p = 1) : d653 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1954 p = 1 := by simpa only [d1959, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11196 p hg
    simpa only [d1959, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1958 p = 1 := by simpa only [d1959, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11197 p hg
    simpa only [d1959, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11199 (p : Pattern) (guard : d1962 p = 1) : d653 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1957 p = 1 := by simpa only [d1962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11160 p hg
    simpa only [d1962, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1961 p = 1 := by simpa only [d1962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11174 p hg
    simpa only [d1962, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban32Refined
