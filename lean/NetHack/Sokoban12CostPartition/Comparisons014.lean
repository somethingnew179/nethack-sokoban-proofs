/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban12CostPartition.Comparisons013
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare1960 (p : Pattern) (guard : d798 p = 1) : d349 p ≤ (0 : Int) + d249 p := by
  cases selected : p 158 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d798, d349, d249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1789 p hg
    simpa only [d798, d349, d249, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d798, d349, d249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare732 p hg
    simpa only [d798, d349, d249, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1961 (p : Pattern) (guard : d798 p = 1) : d350 p ≤ (0 : Int) + d250 p := by
  cases selected : p 141 with
  | false =>
    have hg : d798 p = 1 := by simpa only [d350, d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1959 p hg
    simpa only [d350, d250, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d798 p = 1 := by simpa only [d350, d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1960 p hg
    simpa only [d350, d250, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1962 (p : Pattern) (guard : d798 p = 1) : d351 p ≤ (0 : Int) + d251 p := by
  cases selected : p 134 with
  | false =>
    have hg : d798 p = 1 := by simpa only [d351, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1961 p hg
    simpa only [d351, d251, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d798 p = 1 := by simpa only [d351, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare511 p hg
    simpa only [d351, d251, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1963 (p : Pattern) (guard : d798 p = 1) : d352 p ≤ (0 : Int) + d317 p := by
  cases selected : p 133 with
  | false =>
    have hg : d798 p = 1 := by simpa only [d352, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1958 p hg
    simpa only [d352, d317, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d798 p = 1 := by simpa only [d352, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1962 p hg
    simpa only [d352, d317, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1964 (p : Pattern) (guard : d798 p = 1) : d338 p ≤ (0 : Int) + d191 p := by
  cases selected : p 158 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d798, d338, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1781 p hg
    simpa only [d798, d338, d191, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d798, d338, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare728 p hg
    simpa only [d798, d338, d191, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1965 (p : Pattern) (guard : d798 p = 1) : d339 p ≤ (0 : Int) + d253 p := by
  cases selected : p 158 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d798, d339, d253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1783 p hg
    simpa only [d798, d339, d253, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d798, d339, d253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare732 p hg
    simpa only [d798, d339, d253, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1966 (p : Pattern) (guard : d798 p = 1) : d340 p ≤ (0 : Int) + d254 p := by
  cases selected : p 141 with
  | false =>
    have hg : d798 p = 1 := by simpa only [d340, d254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1964 p hg
    simpa only [d340, d254, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d798 p = 1 := by simpa only [d340, d254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1965 p hg
    simpa only [d340, d254, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1967 (p : Pattern) (guard : d798 p = 1) : d353 p ≤ (0 : Int) + d255 p := by
  cases selected : p 134 with
  | false =>
    have hg : d798 p = 1 := by simpa only [d353, d255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1966 p hg
    simpa only [d353, d255, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d798 p = 1 := by simpa only [d353, d255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare511 p hg
    simpa only [d353, d255, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1968 (p : Pattern) (guard : d798 p = 1) : d354 p ≤ (0 : Int) + d256 p := by
  cases selected : p 133 with
  | false =>
    have hg : d798 p = 1 := by simpa only [d354, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1967 p hg
    simpa only [d354, d256, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d798 p = 1 := by simpa only [d354, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare511 p hg
    simpa only [d354, d256, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1969 (p : Pattern) (guard : d798 p = 1) : d355 p ≤ (0 : Int) + d318 p := by
  cases selected : p 132 with
  | false =>
    have hg : d798 p = 1 := by simpa only [d355, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1963 p hg
    simpa only [d355, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d798 p = 1 := by simpa only [d355, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1968 p hg
    simpa only [d355, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1970 (p : Pattern) (guard : d798 p = 1) : d356 p ≤ (0 : Int) + d319 p := by
  cases selected : p 108 with
  | false =>
    have hg : d798 p = 1 := by simpa only [d356, d319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1957 p hg
    simpa only [d356, d319, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d798 p = 1 := by simpa only [d356, d319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1969 p hg
    simpa only [d356, d319, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1971 (p : Pattern) (guard : d0 p = 1) : d114 p ≤ (11 : Int) + d57 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1972 (p : Pattern) (guard : d1 p = 1) : d57 p ≤ (11 : Int) + d57 p := by
  omega
theorem compare1973 (p : Pattern) (guard : d0 p = 1) : d55 p ≤ (11 : Int) + d57 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1974 (p : Pattern) (guard : d794 p = 1) : d114 p ≤ (11 : Int) + d57 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d794, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1972 p hg
    simpa only [d794, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d794, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1973 p hg
    simpa only [d794, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1975 (p : Pattern) (guard : d987 p = 1) : d114 p ≤ (11 : Int) + d57 p := by
  cases selected : p 158 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d987, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1971 p hg
    simpa only [d987, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d987, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1974 p hg
    simpa only [d987, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1976 (p : Pattern) (guard : d0 p = 1) : d116 p ≤ (11 : Int) + d63 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1977 (p : Pattern) (guard : d1 p = 1) : d63 p ≤ (11 : Int) + d63 p := by
  omega
theorem compare1978 (p : Pattern) (guard : d0 p = 1) : d65 p ≤ (11 : Int) + d63 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1979 (p : Pattern) (guard : d794 p = 1) : d116 p ≤ (11 : Int) + d63 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d794, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1977 p hg
    simpa only [d794, d116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d794, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1978 p hg
    simpa only [d794, d116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1980 (p : Pattern) (guard : d987 p = 1) : d116 p ≤ (11 : Int) + d63 p := by
  cases selected : p 158 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d987, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1976 p hg
    simpa only [d987, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d987, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1979 p hg
    simpa only [d987, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1981 (p : Pattern) (guard : d987 p = 1) : d335 p ≤ (11 : Int) + d64 p := by
  cases selected : p 141 with
  | false =>
    have hg : d987 p = 1 := by simpa only [d335, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1975 p hg
    simpa only [d335, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d987 p = 1 := by simpa only [d335, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1980 p hg
    simpa only [d335, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1982 (p : Pattern) (guard : d0 p = 1) : d107 p ≤ (11 : Int) + d106 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1983 (p : Pattern) (guard : d1 p = 1) : d106 p ≤ (11 : Int) + d106 p := by
  omega
theorem compare1984 (p : Pattern) (guard : d0 p = 1) : d55 p ≤ (11 : Int) + d106 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1985 (p : Pattern) (guard : d794 p = 1) : d107 p ≤ (11 : Int) + d106 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d794, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1983 p hg
    simpa only [d794, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d794, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1984 p hg
    simpa only [d794, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1986 (p : Pattern) (guard : d987 p = 1) : d107 p ≤ (11 : Int) + d106 p := by
  cases selected : p 158 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d987, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1982 p hg
    simpa only [d987, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d987, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1985 p hg
    simpa only [d987, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1987 (p : Pattern) (guard : d0 p = 1) : d110 p ≤ (11 : Int) + d109 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1988 (p : Pattern) (guard : d1 p = 1) : d109 p ≤ (11 : Int) + d109 p := by
  omega
theorem compare1989 (p : Pattern) (guard : d0 p = 1) : d65 p ≤ (11 : Int) + d109 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1990 (p : Pattern) (guard : d794 p = 1) : d110 p ≤ (11 : Int) + d109 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d794, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1988 p hg
    simpa only [d794, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d794, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1989 p hg
    simpa only [d794, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1991 (p : Pattern) (guard : d987 p = 1) : d110 p ≤ (11 : Int) + d109 p := by
  cases selected : p 158 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d987, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1987 p hg
    simpa only [d987, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d987, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1990 p hg
    simpa only [d987, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1992 (p : Pattern) (guard : d987 p = 1) : d336 p ≤ (11 : Int) + d227 p := by
  cases selected : p 141 with
  | false =>
    have hg : d987 p = 1 := by simpa only [d336, d227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1986 p hg
    simpa only [d336, d227, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d987 p = 1 := by simpa only [d336, d227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1991 p hg
    simpa only [d336, d227, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1993 (p : Pattern) (guard : d987 p = 1) : d337 p ≤ (11 : Int) + d228 p := by
  cases selected : p 134 with
  | false =>
    have hg : d987 p = 1 := by simpa only [d337, d228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1981 p hg
    simpa only [d337, d228, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d987 p = 1 := by simpa only [d337, d228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1992 p hg
    simpa only [d337, d228, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1994 (p : Pattern) (guard : d1 p = 1) : d2 p ≤ (11 : Int) + d0 p := by
  change (2 : Int) ≤ (11 : Int) + 0
  decide
theorem compare1995 (p : Pattern) (guard : d1 p = 1) : d4 p ≤ (11 : Int) + d2 p := by
  change (4 : Int) ≤ (11 : Int) + 2
  decide
theorem compare1996 (p : Pattern) (guard : d1 p = 1) : d54 p ≤ (11 : Int) + d6 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d54, d6, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1994 p hg
    simpa only [d54, d6, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d54, d6, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1995 p hg
    simpa only [d54, d6, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1997 (p : Pattern) (guard : d1 p = 1) : d55 p ≤ (11 : Int) + d7 p := by
  cases selected : p 192 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d55, d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1994 p hg
    simpa only [d55, d7, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d55, d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1996 p hg
    simpa only [d55, d7, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1998 (p : Pattern) (guard : d1 p = 1) : d55 p ≤ (11 : Int) + d55 p := by
  omega
theorem compare1999 (p : Pattern) (guard : d1 p = 1) : d55 p ≤ (11 : Int) + d56 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1997 p hg
    simpa only [d56, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1998 p hg
    simpa only [d56, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2000 (p : Pattern) (guard : d1 p = 1) : d55 p ≤ (11 : Int) + d57 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1997 p hg
    simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1999 p hg
    simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2001 (p : Pattern) (guard : d794 p = 1) : d55 p ≤ (11 : Int) + d57 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2000 p hg
    simpa only [d794, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1973 p hg
    simpa only [d794, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2002 (p : Pattern) (guard : d987 p = 1) : d338 p ≤ (11 : Int) + d57 p := by
  cases selected : p 158 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d987, d338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1971 p hg
    simpa only [d987, d338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d987, d338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2001 p hg
    simpa only [d987, d338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2003 (p : Pattern) (guard : d1 p = 1) : d3 p ≤ (11 : Int) + d1 p := by
  change (3 : Int) ≤ (11 : Int) + 1
  decide
theorem compare2004 (p : Pattern) (guard : d1 p = 1) : d9 p ≤ (11 : Int) + d8 p := by
  cases selected : p 271 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d9, d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1994 p hg
    simpa only [d9, d8, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d9, d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2003 p hg
    simpa only [d9, d8, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2005 (p : Pattern) (guard : d1 p = 1) : d5 p ≤ (11 : Int) + d3 p := by
  change (5 : Int) ≤ (11 : Int) + 3
  decide
theorem compare2006 (p : Pattern) (guard : d1 p = 1) : d58 p ≤ (11 : Int) + d9 p := by
  cases selected : p 271 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d58, d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1995 p hg
    simpa only [d58, d9, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d58, d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2005 p hg
    simpa only [d58, d9, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2007 (p : Pattern) (guard : d1 p = 1) : d59 p ≤ (11 : Int) + d10 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d59, d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2004 p hg
    simpa only [d59, d10, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d59, d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2006 p hg
    simpa only [d59, d10, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2008 (p : Pattern) (guard : d1 p = 1) : d60 p ≤ (11 : Int) + d11 p := by
  cases selected : p 192 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d60, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2004 p hg
    simpa only [d60, d11, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d60, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2007 p hg
    simpa only [d60, d11, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2009 (p : Pattern) (guard : d1 p = 1) : d65 p ≤ (11 : Int) + d12 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d65, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1997 p hg
    simpa only [d65, d12, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d65, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2008 p hg
    simpa only [d65, d12, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2010 (p : Pattern) (guard : d1 p = 1) : d60 p ≤ (11 : Int) + d60 p := by
  omega
theorem compare2011 (p : Pattern) (guard : d1 p = 1) : d60 p ≤ (11 : Int) + d61 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2008 p hg
    simpa only [d61, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2010 p hg
    simpa only [d61, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2012 (p : Pattern) (guard : d1 p = 1) : d65 p ≤ (11 : Int) + d62 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d65, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1999 p hg
    simpa only [d65, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d65, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2011 p hg
    simpa only [d65, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2013 (p : Pattern) (guard : d1 p = 1) : d65 p ≤ (11 : Int) + d63 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2009 p hg
    simpa only [d63, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2012 p hg
    simpa only [d63, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2014 (p : Pattern) (guard : d794 p = 1) : d65 p ≤ (11 : Int) + d63 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2013 p hg
    simpa only [d794, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1978 p hg
    simpa only [d794, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2015 (p : Pattern) (guard : d987 p = 1) : d339 p ≤ (11 : Int) + d63 p := by
  cases selected : p 158 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d987, d339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1976 p hg
    simpa only [d987, d339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d987, d339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2014 p hg
    simpa only [d987, d339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2016 (p : Pattern) (guard : d987 p = 1) : d340 p ≤ (11 : Int) + d64 p := by
  cases selected : p 141 with
  | false =>
    have hg : d987 p = 1 := by simpa only [d340, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2002 p hg
    simpa only [d340, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d987 p = 1 := by simpa only [d340, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2015 p hg
    simpa only [d340, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2017 (p : Pattern) (guard : d0 p = 1) : d107 p ≤ (11 : Int) + d122 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2018 (p : Pattern) (guard : d1 p = 1) : d55 p ≤ (11 : Int) + d106 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1997 p hg
    simpa only [d106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1998 p hg
    simpa only [d106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2019 (p : Pattern) (guard : d0 p = 1) : d55 p ≤ (11 : Int) + d121 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2020 (p : Pattern) (guard : d794 p = 1) : d55 p ≤ (11 : Int) + d122 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d794, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2018 p hg
    simpa only [d794, d122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d794, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2019 p hg
    simpa only [d794, d122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2021 (p : Pattern) (guard : d987 p = 1) : d211 p ≤ (11 : Int) + d122 p := by
  cases selected : p 158 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d987, d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2017 p hg
    simpa only [d987, d211, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d987, d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2020 p hg
    simpa only [d987, d211, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2022 (p : Pattern) (guard : d0 p = 1) : d110 p ≤ (11 : Int) + d129 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2023 (p : Pattern) (guard : d1 p = 1) : d65 p ≤ (11 : Int) + d65 p := by
  omega
theorem compare2024 (p : Pattern) (guard : d1 p = 1) : d65 p ≤ (11 : Int) + d109 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2009 p hg
    simpa only [d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2023 p hg
    simpa only [d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2025 (p : Pattern) (guard : d0 p = 1) : d65 p ≤ (11 : Int) + d128 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2026 (p : Pattern) (guard : d794 p = 1) : d65 p ≤ (11 : Int) + d129 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d794, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2024 p hg
    simpa only [d794, d129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d794, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2025 p hg
    simpa only [d794, d129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2027 (p : Pattern) (guard : d987 p = 1) : d212 p ≤ (11 : Int) + d129 p := by
  cases selected : p 158 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d987, d212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2022 p hg
    simpa only [d987, d212, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d987, d212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2026 p hg
    simpa only [d987, d212, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2028 (p : Pattern) (guard : d987 p = 1) : d213 p ≤ (11 : Int) + d775 p := by
  cases selected : p 141 with
  | false =>
    have hg : d987 p = 1 := by simpa only [d213, d775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2021 p hg
    simpa only [d213, d775, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d987 p = 1 := by simpa only [d213, d775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2027 p hg
    simpa only [d213, d775, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2029 (p : Pattern) (guard : d987 p = 1) : d341 p ≤ (11 : Int) + d776 p := by
  cases selected : p 134 with
  | false =>
    have hg : d987 p = 1 := by simpa only [d341, d776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2016 p hg
    simpa only [d341, d776, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d987 p = 1 := by simpa only [d341, d776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2028 p hg
    simpa only [d341, d776, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2030 (p : Pattern) (guard : d987 p = 1) : d342 p ≤ (11 : Int) + d777 p := by
  cases selected : p 133 with
  | false =>
    have hg : d987 p = 1 := by simpa only [d342, d777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1993 p hg
    simpa only [d342, d777, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d987 p = 1 := by simpa only [d342, d777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2029 p hg
    simpa only [d342, d777, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2031 (p : Pattern) (guard : d987 p = 1) : d66 p ≤ (11 : Int) + d66 p := by
  omega
theorem compare2032 (p : Pattern) (guard : d987 p = 1) : d343 p ≤ (11 : Int) + d778 p := by
  cases selected : p 133 with
  | false =>
    have hg : d987 p = 1 := by simpa only [d343, d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2029 p hg
    simpa only [d343, d778, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d987 p = 1 := by simpa only [d343, d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2031 p hg
    simpa only [d343, d778, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2033 (p : Pattern) (guard : d987 p = 1) : d344 p ≤ (11 : Int) + d779 p := by
  cases selected : p 132 with
  | false =>
    have hg : d987 p = 1 := by simpa only [d344, d779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2030 p hg
    simpa only [d344, d779, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d987 p = 1 := by simpa only [d344, d779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2032 p hg
    simpa only [d344, d779, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2034 (p : Pattern) (guard : d987 p = 1) : d345 p ≤ (11 : Int) + d67 p := by
  cases selected : p 134 with
  | false =>
    have hg : d987 p = 1 := by simpa only [d345, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1981 p hg
    simpa only [d345, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d987 p = 1 := by simpa only [d345, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2031 p hg
    simpa only [d345, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2035 (p : Pattern) (guard : d0 p = 1) : d346 p ≤ (11 : Int) + d140 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2036 (p : Pattern) (guard : d1 p = 1) : d55 p ≤ (11 : Int) + d119 p := by
  cases selected : p 187 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1997 p hg
    simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1998 p hg
    simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2037 (p : Pattern) (guard : d1 p = 1) : d55 p ≤ (11 : Int) + d137 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2036 p hg
    simpa only [d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1998 p hg
    simpa only [d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2038 (p : Pattern) (guard : d1 p = 1) : d55 p ≤ (11 : Int) + d138 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1997 p hg
    simpa only [d138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2037 p hg
    simpa only [d138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2039 (p : Pattern) (guard : d0 p = 1) : d55 p ≤ (11 : Int) + d139 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2040 (p : Pattern) (guard : d794 p = 1) : d55 p ≤ (11 : Int) + d140 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d794, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2038 p hg
    simpa only [d794, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d794, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2039 p hg
    simpa only [d794, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2041 (p : Pattern) (guard : d987 p = 1) : d347 p ≤ (11 : Int) + d140 p := by
  cases selected : p 158 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d987, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2035 p hg
    simpa only [d987, d347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d987, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2040 p hg
    simpa only [d987, d347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2042 (p : Pattern) (guard : d0 p = 1) : d348 p ≤ (11 : Int) + d147 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2043 (p : Pattern) (guard : d1 p = 1) : d60 p ≤ (11 : Int) + d125 p := by
  cases selected : p 187 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2008 p hg
    simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2010 p hg
    simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2044 (p : Pattern) (guard : d1 p = 1) : d60 p ≤ (11 : Int) + d143 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2043 p hg
    simpa only [d143, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2010 p hg
    simpa only [d143, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2045 (p : Pattern) (guard : d1 p = 1) : d65 p ≤ (11 : Int) + d144 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d65, d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2037 p hg
    simpa only [d65, d144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d65, d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2044 p hg
    simpa only [d65, d144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2046 (p : Pattern) (guard : d1 p = 1) : d65 p ≤ (11 : Int) + d145 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2009 p hg
    simpa only [d145, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2045 p hg
    simpa only [d145, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2047 (p : Pattern) (guard : d0 p = 1) : d65 p ≤ (11 : Int) + d146 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2048 (p : Pattern) (guard : d794 p = 1) : d65 p ≤ (11 : Int) + d147 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d794, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2046 p hg
    simpa only [d794, d147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d794, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2047 p hg
    simpa only [d794, d147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2049 (p : Pattern) (guard : d987 p = 1) : d349 p ≤ (11 : Int) + d147 p := by
  cases selected : p 158 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d987, d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2042 p hg
    simpa only [d987, d349, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d987, d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2048 p hg
    simpa only [d987, d349, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2050 (p : Pattern) (guard : d987 p = 1) : d350 p ≤ (11 : Int) + d780 p := by
  cases selected : p 141 with
  | false =>
    have hg : d987 p = 1 := by simpa only [d350, d780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2041 p hg
    simpa only [d350, d780, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d987 p = 1 := by simpa only [d350, d780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2049 p hg
    simpa only [d350, d780, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2051 (p : Pattern) (guard : d987 p = 1) : d351 p ≤ (11 : Int) + d781 p := by
  cases selected : p 134 with
  | false =>
    have hg : d987 p = 1 := by simpa only [d351, d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2050 p hg
    simpa only [d351, d781, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d987 p = 1 := by simpa only [d351, d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2031 p hg
    simpa only [d351, d781, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2052 (p : Pattern) (guard : d987 p = 1) : d352 p ≤ (11 : Int) + d782 p := by
  cases selected : p 133 with
  | false =>
    have hg : d987 p = 1 := by simpa only [d352, d782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2034 p hg
    simpa only [d352, d782, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d987 p = 1 := by simpa only [d352, d782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2051 p hg
    simpa only [d352, d782, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2053 (p : Pattern) (guard : d0 p = 1) : d114 p ≤ (11 : Int) + d153 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2054 (p : Pattern) (guard : d794 p = 1) : d55 p ≤ (11 : Int) + d153 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d794, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2000 p hg
    simpa only [d794, d153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d794, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2039 p hg
    simpa only [d794, d153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2055 (p : Pattern) (guard : d987 p = 1) : d338 p ≤ (11 : Int) + d153 p := by
  cases selected : p 158 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d987, d338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2053 p hg
    simpa only [d987, d338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d987, d338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2054 p hg
    simpa only [d987, d338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2056 (p : Pattern) (guard : d0 p = 1) : d116 p ≤ (11 : Int) + d155 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2057 (p : Pattern) (guard : d794 p = 1) : d65 p ≤ (11 : Int) + d155 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d794, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2013 p hg
    simpa only [d794, d155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d794, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2047 p hg
    simpa only [d794, d155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2058 (p : Pattern) (guard : d987 p = 1) : d339 p ≤ (11 : Int) + d155 p := by
  cases selected : p 158 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d987, d339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2056 p hg
    simpa only [d987, d339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d987, d339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2057 p hg
    simpa only [d987, d339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2059 (p : Pattern) (guard : d987 p = 1) : d340 p ≤ (11 : Int) + d783 p := by
  cases selected : p 141 with
  | false =>
    have hg : d987 p = 1 := by simpa only [d340, d783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2055 p hg
    simpa only [d340, d783, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d987 p = 1 := by simpa only [d340, d783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2058 p hg
    simpa only [d340, d783, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2060 (p : Pattern) (guard : d987 p = 1) : d353 p ≤ (11 : Int) + d784 p := by
  cases selected : p 134 with
  | false =>
    have hg : d987 p = 1 := by simpa only [d353, d784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2059 p hg
    simpa only [d353, d784, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d987 p = 1 := by simpa only [d353, d784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2031 p hg
    simpa only [d353, d784, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2061 (p : Pattern) (guard : d987 p = 1) : d354 p ≤ (11 : Int) + d785 p := by
  cases selected : p 133 with
  | false =>
    have hg : d987 p = 1 := by simpa only [d354, d785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d354, d785, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d987 p = 1 := by simpa only [d354, d785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2031 p hg
    simpa only [d354, d785, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2062 (p : Pattern) (guard : d987 p = 1) : d355 p ≤ (11 : Int) + d786 p := by
  cases selected : p 132 with
  | false =>
    have hg : d987 p = 1 := by simpa only [d355, d786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2052 p hg
    simpa only [d355, d786, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d987 p = 1 := by simpa only [d355, d786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2061 p hg
    simpa only [d355, d786, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2063 (p : Pattern) (guard : d987 p = 1) : d356 p ≤ (11 : Int) + d787 p := by
  cases selected : p 108 with
  | false =>
    have hg : d987 p = 1 := by simpa only [d356, d787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2033 p hg
    simpa only [d356, d787, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d987 p = 1 := by simpa only [d356, d787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2062 p hg
    simpa only [d356, d787, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2064 (p : Pattern) (guard : d0 p = 1) : d336 p ≤ (0 : Int) + d66 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2065 (p : Pattern) (guard : d845 p = 1) : d337 p ≤ (0 : Int) + d67 p := by
  cases selected : p 134 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d845, d337, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1750 p hg
    simpa only [d845, d337, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d845, d337, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2064 p hg
    simpa only [d845, d337, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2066 (p : Pattern) (guard : d818 p = 1) : d114 p ≤ (0 : Int) + d57 p := by
  cases selected : p 159 with
  | false =>
    have hg : d758 p = 1 := by simpa only [d818, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare814 p hg
    simpa only [d818, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d818, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1401 p hg
    simpa only [d818, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2067 (p : Pattern) (guard : d818 p = 1) : d338 p ≤ (0 : Int) + d68 p := by
  cases selected : p 158 with
  | false =>
    have hg : d818 p = 1 := by simpa only [d338, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2066 p hg
    simpa only [d338, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d818 p = 1 := by simpa only [d338, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare707 p hg
    simpa only [d338, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2068 (p : Pattern) (guard : d818 p = 1) : d116 p ≤ (0 : Int) + d63 p := by
  cases selected : p 159 with
  | false =>
    have hg : d758 p = 1 := by simpa only [d818, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare817 p hg
    simpa only [d818, d116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d818, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1405 p hg
    simpa only [d818, d116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2069 (p : Pattern) (guard : d818 p = 1) : d339 p ≤ (0 : Int) + d69 p := by
  cases selected : p 158 with
  | false =>
    have hg : d818 p = 1 := by simpa only [d339, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2068 p hg
    simpa only [d339, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d818 p = 1 := by simpa only [d339, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare709 p hg
    simpa only [d339, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2070 (p : Pattern) (guard : d818 p = 1) : d340 p ≤ (0 : Int) + d70 p := by
  cases selected : p 141 with
  | false =>
    have hg : d818 p = 1 := by simpa only [d340, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2067 p hg
    simpa only [d340, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d818 p = 1 := by simpa only [d340, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2069 p hg
    simpa only [d340, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2071 (p : Pattern) (guard : d848 p = 1) : d341 p ≤ (0 : Int) + d71 p := by
  cases selected : p 134 with
  | false =>
    have hg : d818 p = 1 := by simpa only [d848, d341, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2070 p hg
    simpa only [d848, d341, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d848, d341, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare564 p hg
    simpa only [d848, d341, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2072 (p : Pattern) (guard : d849 p = 1) : d342 p ≤ (0 : Int) + d72 p := by
  cases selected : p 133 with
  | false =>
    have hg : d845 p = 1 := by simpa only [d849, d342, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2065 p hg
    simpa only [d849, d342, d72, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d848 p = 1 := by simpa only [d849, d342, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2071 p hg
    simpa only [d849, d342, d72, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2073 (p : Pattern) (guard : d845 p = 1) : d341 p ≤ (0 : Int) + d71 p := by
  cases selected : p 134 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d845, d341, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1759 p hg
    simpa only [d845, d341, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d845, d341, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare564 p hg
    simpa only [d845, d341, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2074 (p : Pattern) (guard : d849 p = 1) : d343 p ≤ (0 : Int) + d73 p := by
  cases selected : p 133 with
  | false =>
    have hg : d845 p = 1 := by simpa only [d849, d343, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2073 p hg
    simpa only [d849, d343, d73, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d848 p = 1 := by simpa only [d849, d343, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare824 p hg
    simpa only [d849, d343, d73, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2075 (p : Pattern) (guard : d849 p = 1) : d344 p ≤ (0 : Int) + d74 p := by
  cases selected : p 132 with
  | false =>
    have hg : d849 p = 1 := by simpa only [d344, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2072 p hg
    simpa only [d344, d74, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d849 p = 1 := by simpa only [d344, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2074 p hg
    simpa only [d344, d74, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2076 (p : Pattern) (guard : d845 p = 1) : d345 p ≤ (0 : Int) + d67 p := by
  cases selected : p 134 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d845, d345, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1750 p hg
    simpa only [d845, d345, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d845, d345, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare203 p hg
    simpa only [d845, d345, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2077 (p : Pattern) (guard : d758 p = 1) : d138 p ≤ (0 : Int) + d57 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d758, d138, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare282 p hg
    simpa only [d758, d138, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d758, d138, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1708 p hg
    simpa only [d758, d138, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2078 (p : Pattern) (guard : d818 p = 1) : d346 p ≤ (0 : Int) + d57 p := by
  cases selected : p 159 with
  | false =>
    have hg : d758 p = 1 := by simpa only [d818, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2077 p hg
    simpa only [d818, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d818, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1401 p hg
    simpa only [d818, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2079 (p : Pattern) (guard : d818 p = 1) : d347 p ≤ (0 : Int) + d68 p := by
  cases selected : p 158 with
  | false =>
    have hg : d818 p = 1 := by simpa only [d347, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2078 p hg
    simpa only [d347, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d818 p = 1 := by simpa only [d347, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare707 p hg
    simpa only [d347, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2080 (p : Pattern) (guard : d758 p = 1) : d145 p ≤ (0 : Int) + d63 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d758, d145, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare294 p hg
    simpa only [d758, d145, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d758, d145, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1714 p hg
    simpa only [d758, d145, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2081 (p : Pattern) (guard : d818 p = 1) : d348 p ≤ (0 : Int) + d63 p := by
  cases selected : p 159 with
  | false =>
    have hg : d758 p = 1 := by simpa only [d818, d348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2080 p hg
    simpa only [d818, d348, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d818, d348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1405 p hg
    simpa only [d818, d348, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2082 (p : Pattern) (guard : d818 p = 1) : d349 p ≤ (0 : Int) + d69 p := by
  cases selected : p 158 with
  | false =>
    have hg : d818 p = 1 := by simpa only [d349, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2081 p hg
    simpa only [d349, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d818 p = 1 := by simpa only [d349, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare709 p hg
    simpa only [d349, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2083 (p : Pattern) (guard : d818 p = 1) : d350 p ≤ (0 : Int) + d70 p := by
  cases selected : p 141 with
  | false =>
    have hg : d818 p = 1 := by simpa only [d350, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2079 p hg
    simpa only [d350, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d818 p = 1 := by simpa only [d350, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2082 p hg
    simpa only [d350, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2084 (p : Pattern) (guard : d848 p = 1) : d351 p ≤ (0 : Int) + d71 p := by
  cases selected : p 134 with
  | false =>
    have hg : d818 p = 1 := by simpa only [d848, d351, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2083 p hg
    simpa only [d848, d351, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d848, d351, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare203 p hg
    simpa only [d848, d351, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2085 (p : Pattern) (guard : d849 p = 1) : d352 p ≤ (0 : Int) + d72 p := by
  cases selected : p 133 with
  | false =>
    have hg : d845 p = 1 := by simpa only [d849, d352, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2076 p hg
    simpa only [d849, d352, d72, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d848 p = 1 := by simpa only [d849, d352, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2084 p hg
    simpa only [d849, d352, d72, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2086 (p : Pattern) (guard : d845 p = 1) : d353 p ≤ (0 : Int) + d71 p := by
  cases selected : p 134 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d845, d353, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1759 p hg
    simpa only [d845, d353, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d845, d353, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare203 p hg
    simpa only [d845, d353, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2087 (p : Pattern) (guard : d849 p = 1) : d354 p ≤ (0 : Int) + d73 p := by
  cases selected : p 133 with
  | false =>
    have hg : d845 p = 1 := by simpa only [d849, d354, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2086 p hg
    simpa only [d849, d354, d73, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d848 p = 1 := by simpa only [d849, d354, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare824 p hg
    simpa only [d849, d354, d73, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2088 (p : Pattern) (guard : d849 p = 1) : d355 p ≤ (0 : Int) + d74 p := by
  cases selected : p 132 with
  | false =>
    have hg : d849 p = 1 := by simpa only [d355, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2085 p hg
    simpa only [d355, d74, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d849 p = 1 := by simpa only [d355, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2087 p hg
    simpa only [d355, d74, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2089 (p : Pattern) (guard : d849 p = 1) : d356 p ≤ (0 : Int) + d74 p := by
  cases selected : p 108 with
  | false =>
    have hg : d849 p = 1 := by simpa only [d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2075 p hg
    simpa only [d356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d849 p = 1 := by simpa only [d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2088 p hg
    simpa only [d356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2090 (p : Pattern) (guard : d798 p = 1) : d338 p ≤ (0 : Int) + d115 p := by
  cases selected : p 158 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d798, d338, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1402 p hg
    simpa only [d798, d338, d115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d798, d338, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1471 p hg
    simpa only [d798, d338, d115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2091 (p : Pattern) (guard : d798 p = 1) : d339 p ≤ (0 : Int) + d117 p := by
  cases selected : p 158 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d798, d339, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1406 p hg
    simpa only [d798, d339, d117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d798, d339, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1473 p hg
    simpa only [d798, d339, d117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2092 (p : Pattern) (guard : d798 p = 1) : d340 p ≤ (0 : Int) + d118 p := by
  cases selected : p 141 with
  | false =>
    have hg : d798 p = 1 := by simpa only [d340, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2090 p hg
    simpa only [d340, d118, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d798 p = 1 := by simpa only [d340, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2091 p hg
    simpa only [d340, d118, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2093 (p : Pattern) (guard : d798 p = 1) : d211 p ≤ (0 : Int) + d124 p := by
  cases selected : p 158 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d798, d211, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare727 p hg
    simpa only [d798, d211, d124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d798, d211, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1476 p hg
    simpa only [d798, d211, d124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2094 (p : Pattern) (guard : d798 p = 1) : d212 p ≤ (0 : Int) + d131 p := by
  cases selected : p 158 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d798, d212, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare731 p hg
    simpa only [d798, d212, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d798, d212, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1478 p hg
    simpa only [d798, d212, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2095 (p : Pattern) (guard : d798 p = 1) : d213 p ≤ (0 : Int) + d132 p := by
  cases selected : p 141 with
  | false =>
    have hg : d798 p = 1 := by simpa only [d213, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2093 p hg
    simpa only [d213, d132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d798 p = 1 := by simpa only [d213, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2094 p hg
    simpa only [d213, d132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2096 (p : Pattern) (guard : d798 p = 1) : d341 p ≤ (0 : Int) + d133 p := by
  cases selected : p 134 with
  | false =>
    have hg : d798 p = 1 := by simpa only [d341, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2092 p hg
    simpa only [d341, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d798 p = 1 := by simpa only [d341, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2095 p hg
    simpa only [d341, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2097 (p : Pattern) (guard : d799 p = 1) : d342 p ≤ (0 : Int) + d134 p := by
  cases selected : p 133 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d799, d342, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1754 p hg
    simpa only [d799, d342, d134, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d798 p = 1 := by simpa only [d799, d342, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2096 p hg
    simpa only [d799, d342, d134, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2098 (p : Pattern) (guard : d0 p = 1) : d343 p ≤ (0 : Int) + d66 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2099 (p : Pattern) (guard : d800 p = 1) : d344 p ≤ (0 : Int) + d199 p := by
  cases selected : p 132 with
  | false =>
    have hg : d799 p = 1 := by simpa only [d800, d344, d199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2097 p hg
    simpa only [d800, d344, d199, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d800, d344, d199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2098 p hg
    simpa only [d800, d344, d199, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban12CostPartition
