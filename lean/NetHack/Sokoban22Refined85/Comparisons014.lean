/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons013
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare1960 (p : Pattern) (guard : d0 p = 1) : d87 p ≤ (0 : Int) + d422 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1961 (p : Pattern) (guard : d4068 p = 1) : d88 p ≤ (0 : Int) + d546 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4068, d88, d546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1896 p hg
    simpa only [d4068, d88, d546, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4068, d88, d546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1960 p hg
    simpa only [d4068, d88, d546, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1962 (p : Pattern) (guard : d0 p = 1) : d425 p ≤ (0 : Int) + d547 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1963 (p : Pattern) (guard : d4113 p = 1) : d500 p ≤ (0 : Int) + d548 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4068 p = 1 := by simpa only [d4113, d500, d548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1961 p hg
    simpa only [d4113, d500, d548, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4113, d500, d548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1962 p hg
    simpa only [d4113, d500, d548, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1964 (p : Pattern) (guard : d4113 p = 1) : d501 p ≤ (0 : Int) + d549 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4113 p = 1 := by simpa only [d501, d549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1959 p hg
    simpa only [d501, d549, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4113 p = 1 := by simpa only [d501, d549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1963 p hg
    simpa only [d501, d549, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1965 (p : Pattern) (guard : d0 p = 1) : d442 p ≤ (0 : Int) + d551 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1966 (p : Pattern) (guard : d4113 p = 1) : d502 p ≤ (0 : Int) + d552 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4068 p = 1 := by simpa only [d4113, d502, d552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1904 p hg
    simpa only [d4113, d502, d552, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4113, d502, d552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1965 p hg
    simpa only [d4113, d502, d552, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1967 (p : Pattern) (guard : d0 p = 1) : d87 p ≤ (0 : Int) + d412 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1968 (p : Pattern) (guard : d4068 p = 1) : d88 p ≤ (0 : Int) + d553 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4068, d88, d553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1896 p hg
    simpa only [d4068, d88, d553, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4068, d88, d553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1967 p hg
    simpa only [d4068, d88, d553, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1969 (p : Pattern) (guard : d0 p = 1) : d444 p ≤ (0 : Int) + d547 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1970 (p : Pattern) (guard : d4113 p = 1) : d503 p ≤ (0 : Int) + d554 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4068 p = 1 := by simpa only [d4113, d503, d554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1968 p hg
    simpa only [d4113, d503, d554, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4113, d503, d554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1969 p hg
    simpa only [d4113, d503, d554, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1971 (p : Pattern) (guard : d4113 p = 1) : d504 p ≤ (0 : Int) + d555 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4113 p = 1 := by simpa only [d504, d555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1966 p hg
    simpa only [d504, d555, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4113 p = 1 := by simpa only [d504, d555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1970 p hg
    simpa only [d504, d555, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1972 (p : Pattern) (guard : d4113 p = 1) : d505 p ≤ (0 : Int) + d556 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4113 p = 1 := by simpa only [d505, d556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1964 p hg
    simpa only [d505, d556, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4113 p = 1 := by simpa only [d505, d556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1971 p hg
    simpa only [d505, d556, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1973 (p : Pattern) (guard : d0 p = 1) : d442 p ≤ (0 : Int) + d580 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1974 (p : Pattern) (guard : d4113 p = 1) : d506 p ≤ (0 : Int) + d581 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4068 p = 1 := by simpa only [d4113, d506, d581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1912 p hg
    simpa only [d4113, d506, d581, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4113, d506, d581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1973 p hg
    simpa only [d4113, d506, d581, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1975 (p : Pattern) (guard : d0 p = 1) : d157 p ≤ (0 : Int) + d412 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1976 (p : Pattern) (guard : d4068 p = 1) : d158 p ≤ (0 : Int) + d582 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4068, d158, d582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1910 p hg
    simpa only [d4068, d158, d582, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4068, d158, d582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1975 p hg
    simpa only [d4068, d158, d582, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1977 (p : Pattern) (guard : d0 p = 1) : d444 p ≤ (0 : Int) + d583 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1978 (p : Pattern) (guard : d4113 p = 1) : d507 p ≤ (0 : Int) + d584 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4068 p = 1 := by simpa only [d4113, d507, d584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1976 p hg
    simpa only [d4113, d507, d584, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4113, d507, d584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1977 p hg
    simpa only [d4113, d507, d584, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1979 (p : Pattern) (guard : d4113 p = 1) : d508 p ≤ (0 : Int) + d585 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4113 p = 1 := by simpa only [d508, d585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1974 p hg
    simpa only [d508, d585, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4113 p = 1 := by simpa only [d508, d585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1978 p hg
    simpa only [d508, d585, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1980 (p : Pattern) (guard : d4113 p = 1) : d509 p ≤ (0 : Int) + d586 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4113 p = 1 := by simpa only [d509, d586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1964 p hg
    simpa only [d509, d586, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4113 p = 1 := by simpa only [d509, d586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1979 p hg
    simpa only [d509, d586, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1981 (p : Pattern) (guard : d4113 p = 1) : d510 p ≤ (0 : Int) + d587 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4113 p = 1 := by simpa only [d510, d587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1972 p hg
    simpa only [d510, d587, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4113 p = 1 := by simpa only [d510, d587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1980 p hg
    simpa only [d510, d587, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1982 (p : Pattern) (guard : d0 p = 1) : d444 p ≤ (0 : Int) + d606 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1983 (p : Pattern) (guard : d4113 p = 1) : d503 p ≤ (0 : Int) + d607 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4068 p = 1 := by simpa only [d4113, d503, d607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1968 p hg
    simpa only [d4113, d503, d607, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4113, d503, d607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1982 p hg
    simpa only [d4113, d503, d607, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1984 (p : Pattern) (guard : d4113 p = 1) : d504 p ≤ (0 : Int) + d608 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4113 p = 1 := by simpa only [d504, d608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1966 p hg
    simpa only [d504, d608, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4113 p = 1 := by simpa only [d504, d608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1983 p hg
    simpa only [d504, d608, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1985 (p : Pattern) (guard : d4113 p = 1) : d505 p ≤ (0 : Int) + d609 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4113 p = 1 := by simpa only [d505, d609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1964 p hg
    simpa only [d505, d609, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4113 p = 1 := by simpa only [d505, d609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1984 p hg
    simpa only [d505, d609, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1986 (p : Pattern) (guard : d0 p = 1) : d463 p ≤ (0 : Int) + d617 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1987 (p : Pattern) (guard : d4113 p = 1) : d511 p ≤ (0 : Int) + d618 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4068 p = 1 := by simpa only [d4113, d511, d618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1924 p hg
    simpa only [d4113, d511, d618, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4113, d511, d618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1986 p hg
    simpa only [d4113, d511, d618, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1988 (p : Pattern) (guard : d1 p = 1) : d290 p ≤ (0 : Int) + d290 p := by
  omega
theorem compare1989 (p : Pattern) (guard : d0 p = 1) : d305 p ≤ (0 : Int) + d473 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1990 (p : Pattern) (guard : d4068 p = 1) : d306 p ≤ (0 : Int) + d619 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4068, d306, d619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1988 p hg
    simpa only [d4068, d306, d619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4068, d306, d619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1989 p hg
    simpa only [d4068, d306, d619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1991 (p : Pattern) (guard : d0 p = 1) : d476 p ≤ (0 : Int) + d647 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1992 (p : Pattern) (guard : d4113 p = 1) : d512 p ≤ (0 : Int) + d648 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4068 p = 1 := by simpa only [d4113, d512, d648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1990 p hg
    simpa only [d4113, d512, d648, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4113, d512, d648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1991 p hg
    simpa only [d4113, d512, d648, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1993 (p : Pattern) (guard : d4113 p = 1) : d513 p ≤ (0 : Int) + d649 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4113 p = 1 := by simpa only [d513, d649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1987 p hg
    simpa only [d513, d649, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4113 p = 1 := by simpa only [d513, d649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1992 p hg
    simpa only [d513, d649, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1994 (p : Pattern) (guard : d4113 p = 1) : d514 p ≤ (0 : Int) + d650 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4113 p = 1 := by simpa only [d514, d650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1964 p hg
    simpa only [d514, d650, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4113 p = 1 := by simpa only [d514, d650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1993 p hg
    simpa only [d514, d650, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1995 (p : Pattern) (guard : d4113 p = 1) : d515 p ≤ (0 : Int) + d651 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4113 p = 1 := by simpa only [d515, d651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1985 p hg
    simpa only [d515, d651, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4113 p = 1 := by simpa only [d515, d651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1994 p hg
    simpa only [d515, d651, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1996 (p : Pattern) (guard : d4113 p = 1) : d516 p ≤ (0 : Int) + d652 p := by
  cases selected : p 48 with
  | false =>
    have hg : d4113 p = 1 := by simpa only [d516, d652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1981 p hg
    simpa only [d516, d652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4113 p = 1 := by simpa only [d516, d652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1995 p hg
    simpa only [d516, d652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1997 (p : Pattern) (guard : d0 p = 1) : d77 p ≤ (0 : Int) + d4120 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1998 (p : Pattern) (guard : d1 p = 1) : d16 p ≤ (0 : Int) + d33 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d16, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1207 p hg
    simpa only [d16, d33, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d16, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare823 p hg
    simpa only [d16, d33, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1999 (p : Pattern) (guard : d1 p = 1) : d15 p ≤ (0 : Int) + d36 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d15, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1489 p hg
    simpa only [d15, d36, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d15, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d15, d36, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2000 (p : Pattern) (guard : d1 p = 1) : d16 p ≤ (0 : Int) + d37 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d16, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1207 p hg
    simpa only [d16, d37, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d16, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1999 p hg
    simpa only [d16, d37, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2001 (p : Pattern) (guard : d1 p = 1) : d16 p ≤ (0 : Int) + d38 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1998 p hg
    simpa only [d38, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2000 p hg
    simpa only [d38, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2002 (p : Pattern) (guard : d1 p = 1) : d16 p ≤ (0 : Int) + d42 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d16, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1207 p hg
    simpa only [d16, d42, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d16, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1523 p hg
    simpa only [d16, d42, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2003 (p : Pattern) (guard : d1 p = 1) : d18 p ≤ (0 : Int) + d18 p := by
  omega
theorem compare2004 (p : Pattern) (guard : d1 p = 1) : d20 p ≤ (0 : Int) + d43 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d20, d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2003 p hg
    simpa only [d20, d43, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d20, d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1526 p hg
    simpa only [d20, d43, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2005 (p : Pattern) (guard : d1 p = 1) : d21 p ≤ (0 : Int) + d44 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d21, d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2002 p hg
    simpa only [d21, d44, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d21, d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2004 p hg
    simpa only [d21, d44, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2006 (p : Pattern) (guard : d1 p = 1) : d22 p ≤ (0 : Int) + d45 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d22, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2001 p hg
    simpa only [d22, d45, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d22, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2005 p hg
    simpa only [d22, d45, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2007 (p : Pattern) (guard : d1 p = 1) : d15 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1500 p hg
    simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2008 (p : Pattern) (guard : d1 p = 1) : d16 p ≤ (0 : Int) + d46 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d16, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1207 p hg
    simpa only [d16, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d16, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2007 p hg
    simpa only [d16, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2009 (p : Pattern) (guard : d1 p = 1) : d21 p ≤ (0 : Int) + d47 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d21, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2008 p hg
    simpa only [d21, d47, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d21, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2004 p hg
    simpa only [d21, d47, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2010 (p : Pattern) (guard : d1 p = 1) : d24 p ≤ (0 : Int) + d24 p := by
  omega
theorem compare2011 (p : Pattern) (guard : d1 p = 1) : d26 p ≤ (0 : Int) + d48 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d26, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2010 p hg
    simpa only [d26, d48, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d26, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare869 p hg
    simpa only [d26, d48, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2012 (p : Pattern) (guard : d1 p = 1) : d27 p ≤ (0 : Int) + d49 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d27, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2011 p hg
    simpa only [d27, d49, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d27, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d27, d49, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2013 (p : Pattern) (guard : d1 p = 1) : d28 p ≤ (0 : Int) + d50 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d28, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2009 p hg
    simpa only [d28, d50, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d28, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2012 p hg
    simpa only [d28, d50, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2014 (p : Pattern) (guard : d1 p = 1) : d29 p ≤ (0 : Int) + d51 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d29, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2006 p hg
    simpa only [d29, d51, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d29, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2013 p hg
    simpa only [d29, d51, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2015 (p : Pattern) (guard : d0 p = 1) : d81 p ≤ (0 : Int) + d51 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2016 (p : Pattern) (guard : d4117 p = 1) : d82 p ≤ (0 : Int) + d51 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2014 p hg
    simpa only [d4117, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2015 p hg
    simpa only [d4117, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2017 (p : Pattern) (guard : d1 p = 1) : d31 p ≤ (0 : Int) + d31 p := by
  omega
theorem compare2018 (p : Pattern) (guard : d1 p = 1) : d53 p ≤ (0 : Int) + d66 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d53, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2017 p hg
    simpa only [d53, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d53, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1541 p hg
    simpa only [d53, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2019 (p : Pattern) (guard : d1 p = 1) : d54 p ≤ (0 : Int) + d67 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d54, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2000 p hg
    simpa only [d54, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d54, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2018 p hg
    simpa only [d54, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2020 (p : Pattern) (guard : d1 p = 1) : d55 p ≤ (0 : Int) + d68 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d55, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2004 p hg
    simpa only [d55, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d55, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2011 p hg
    simpa only [d55, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2021 (p : Pattern) (guard : d1 p = 1) : d56 p ≤ (0 : Int) + d69 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d56, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2019 p hg
    simpa only [d56, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d56, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2020 p hg
    simpa only [d56, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2022 (p : Pattern) (guard : d1 p = 1) : d58 p ≤ (0 : Int) + d58 p := by
  omega
theorem compare2023 (p : Pattern) (guard : d1 p = 1) : d60 p ≤ (0 : Int) + d70 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d60, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2022 p hg
    simpa only [d60, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d60, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare850 p hg
    simpa only [d60, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2024 (p : Pattern) (guard : d1 p = 1) : d61 p ≤ (0 : Int) + d71 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d61, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2004 p hg
    simpa only [d61, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d61, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2023 p hg
    simpa only [d61, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2025 (p : Pattern) (guard : d1 p = 1) : d40 p ≤ (0 : Int) + d40 p := by
  omega
theorem compare2026 (p : Pattern) (guard : d1 p = 1) : d62 p ≤ (0 : Int) + d72 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d62, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2025 p hg
    simpa only [d62, d72, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d62, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare712 p hg
    simpa only [d62, d72, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2027 (p : Pattern) (guard : d1 p = 1) : d63 p ≤ (0 : Int) + d73 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d63, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2026 p hg
    simpa only [d63, d73, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d63, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d63, d73, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2028 (p : Pattern) (guard : d1 p = 1) : d64 p ≤ (0 : Int) + d74 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d64, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2024 p hg
    simpa only [d64, d74, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d64, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2027 p hg
    simpa only [d64, d74, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2029 (p : Pattern) (guard : d1 p = 1) : d65 p ≤ (0 : Int) + d75 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d65, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2021 p hg
    simpa only [d65, d75, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d65, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2028 p hg
    simpa only [d65, d75, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2030 (p : Pattern) (guard : d0 p = 1) : d85 p ≤ (0 : Int) + d75 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2031 (p : Pattern) (guard : d4117 p = 1) : d86 p ≤ (0 : Int) + d75 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2029 p hg
    simpa only [d4117, d86, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2030 p hg
    simpa only [d4117, d86, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2032 (p : Pattern) (guard : d4117 p = 1) : d87 p ≤ (0 : Int) + d4120 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d87, d4120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2016 p hg
    simpa only [d87, d4120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d87, d4120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2031 p hg
    simpa only [d87, d4120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2033 (p : Pattern) (guard : d4118 p = 1) : d88 p ≤ (0 : Int) + d4120 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4118, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1997 p hg
    simpa only [d4118, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d4118, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2032 p hg
    simpa only [d4118, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2034 (p : Pattern) (guard : d0 p = 1) : d413 p ≤ (0 : Int) + d4121 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2035 (p : Pattern) (guard : d4119 p = 1) : d499 p ≤ (0 : Int) + d4122 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4118 p = 1 := by simpa only [d4119, d499, d4122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2033 p hg
    simpa only [d4119, d499, d4122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4119, d499, d4122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2034 p hg
    simpa only [d4119, d499, d4122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2036 (p : Pattern) (guard : d0 p = 1) : d425 p ≤ (0 : Int) + d4121 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2037 (p : Pattern) (guard : d4119 p = 1) : d500 p ≤ (0 : Int) + d4122 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4118 p = 1 := by simpa only [d4119, d500, d4122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2033 p hg
    simpa only [d4119, d500, d4122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4119, d500, d4122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2036 p hg
    simpa only [d4119, d500, d4122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2038 (p : Pattern) (guard : d4119 p = 1) : d501 p ≤ (0 : Int) + d4122 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4119 p = 1 := by simpa only [d501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2035 p hg
    simpa only [d501, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4119 p = 1 := by simpa only [d501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2037 p hg
    simpa only [d501, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2039 (p : Pattern) (guard : d0 p = 1) : d442 p ≤ (0 : Int) + d4121 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2040 (p : Pattern) (guard : d4119 p = 1) : d502 p ≤ (0 : Int) + d4122 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4118 p = 1 := by simpa only [d4119, d502, d4122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2033 p hg
    simpa only [d4119, d502, d4122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4119, d502, d4122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2039 p hg
    simpa only [d4119, d502, d4122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2041 (p : Pattern) (guard : d0 p = 1) : d444 p ≤ (0 : Int) + d4121 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2042 (p : Pattern) (guard : d4119 p = 1) : d503 p ≤ (0 : Int) + d4122 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4118 p = 1 := by simpa only [d4119, d503, d4122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2033 p hg
    simpa only [d4119, d503, d4122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4119, d503, d4122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2041 p hg
    simpa only [d4119, d503, d4122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2043 (p : Pattern) (guard : d4119 p = 1) : d504 p ≤ (0 : Int) + d4122 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4119 p = 1 := by simpa only [d504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2040 p hg
    simpa only [d504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4119 p = 1 := by simpa only [d504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2042 p hg
    simpa only [d504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2044 (p : Pattern) (guard : d4119 p = 1) : d505 p ≤ (0 : Int) + d4122 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4119 p = 1 := by simpa only [d505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2038 p hg
    simpa only [d505, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4119 p = 1 := by simpa only [d505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2043 p hg
    simpa only [d505, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2045 (p : Pattern) (guard : d0 p = 1) : d147 p ≤ (0 : Int) + d4123 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2046 (p : Pattern) (guard : d1 p = 1) : d105 p ≤ (0 : Int) + d118 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d105, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1274 p hg
    simpa only [d105, d118, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d105, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1250 p hg
    simpa only [d105, d118, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2047 (p : Pattern) (guard : d1 p = 1) : d104 p ≤ (0 : Int) + d121 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d104, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1405 p hg
    simpa only [d104, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d104, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d104, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2048 (p : Pattern) (guard : d1 p = 1) : d105 p ≤ (0 : Int) + d122 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d105, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1274 p hg
    simpa only [d105, d122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d105, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2047 p hg
    simpa only [d105, d122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2049 (p : Pattern) (guard : d1 p = 1) : d105 p ≤ (0 : Int) + d123 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2046 p hg
    simpa only [d123, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2048 p hg
    simpa only [d123, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2050 (p : Pattern) (guard : d1 p = 1) : d105 p ≤ (0 : Int) + d124 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d105, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1274 p hg
    simpa only [d105, d124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d105, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1588 p hg
    simpa only [d105, d124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2051 (p : Pattern) (guard : d1 p = 1) : d107 p ≤ (0 : Int) + d107 p := by
  omega
theorem compare2052 (p : Pattern) (guard : d1 p = 1) : d109 p ≤ (0 : Int) + d125 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d109, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2051 p hg
    simpa only [d109, d125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d109, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1322 p hg
    simpa only [d109, d125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2053 (p : Pattern) (guard : d1 p = 1) : d110 p ≤ (0 : Int) + d126 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d110, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2050 p hg
    simpa only [d110, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d110, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2052 p hg
    simpa only [d110, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2054 (p : Pattern) (guard : d1 p = 1) : d111 p ≤ (0 : Int) + d127 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d111, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2049 p hg
    simpa only [d111, d127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d111, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2053 p hg
    simpa only [d111, d127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2055 (p : Pattern) (guard : d1 p = 1) : d112 p ≤ (0 : Int) + d128 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d112, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2023 p hg
    simpa only [d112, d128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d112, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d112, d128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2056 (p : Pattern) (guard : d1 p = 1) : d113 p ≤ (0 : Int) + d129 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d113, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2053 p hg
    simpa only [d113, d129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d113, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2055 p hg
    simpa only [d113, d129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2057 (p : Pattern) (guard : d1 p = 1) : d114 p ≤ (0 : Int) + d130 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d114, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2054 p hg
    simpa only [d114, d130, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d114, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2056 p hg
    simpa only [d114, d130, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2058 (p : Pattern) (guard : d0 p = 1) : d151 p ≤ (0 : Int) + d130 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2059 (p : Pattern) (guard : d4117 p = 1) : d152 p ≤ (0 : Int) + d130 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2057 p hg
    simpa only [d4117, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2058 p hg
    simpa only [d4117, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2060 (p : Pattern) (guard : d1 p = 1) : d116 p ≤ (0 : Int) + d116 p := by
  omega
theorem compare2061 (p : Pattern) (guard : d1 p = 1) : d132 p ≤ (0 : Int) + d139 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d132, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d132, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d132, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1595 p hg
    simpa only [d132, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2062 (p : Pattern) (guard : d1 p = 1) : d133 p ≤ (0 : Int) + d140 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d133, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2048 p hg
    simpa only [d133, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d133, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2061 p hg
    simpa only [d133, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2063 (p : Pattern) (guard : d1 p = 1) : d134 p ≤ (0 : Int) + d141 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d134, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2052 p hg
    simpa only [d134, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d134, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2023 p hg
    simpa only [d134, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2064 (p : Pattern) (guard : d1 p = 1) : d135 p ≤ (0 : Int) + d142 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d135, d142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2062 p hg
    simpa only [d135, d142, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d135, d142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2063 p hg
    simpa only [d135, d142, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2065 (p : Pattern) (guard : d1 p = 1) : d136 p ≤ (0 : Int) + d143 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d136, d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2052 p hg
    simpa only [d136, d143, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d136, d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2026 p hg
    simpa only [d136, d143, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2066 (p : Pattern) (guard : d1 p = 1) : d137 p ≤ (0 : Int) + d144 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d137, d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2065 p hg
    simpa only [d137, d144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d137, d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d137, d144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2067 (p : Pattern) (guard : d1 p = 1) : d138 p ≤ (0 : Int) + d145 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d138, d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2064 p hg
    simpa only [d138, d145, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d138, d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2066 p hg
    simpa only [d138, d145, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2068 (p : Pattern) (guard : d0 p = 1) : d155 p ≤ (0 : Int) + d145 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2069 (p : Pattern) (guard : d4117 p = 1) : d156 p ≤ (0 : Int) + d145 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2067 p hg
    simpa only [d4117, d156, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2068 p hg
    simpa only [d4117, d156, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2070 (p : Pattern) (guard : d4117 p = 1) : d157 p ≤ (0 : Int) + d4123 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d157, d4123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2059 p hg
    simpa only [d157, d4123, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d157, d4123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2069 p hg
    simpa only [d157, d4123, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2071 (p : Pattern) (guard : d4118 p = 1) : d158 p ≤ (0 : Int) + d4123 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4118, d158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2045 p hg
    simpa only [d4118, d158, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d4118, d158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2070 p hg
    simpa only [d4118, d158, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2072 (p : Pattern) (guard : d0 p = 1) : d442 p ≤ (0 : Int) + d4124 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2073 (p : Pattern) (guard : d4119 p = 1) : d506 p ≤ (0 : Int) + d4125 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4118 p = 1 := by simpa only [d4119, d506, d4125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2071 p hg
    simpa only [d4119, d506, d4125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4119, d506, d4125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2072 p hg
    simpa only [d4119, d506, d4125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2074 (p : Pattern) (guard : d0 p = 1) : d444 p ≤ (0 : Int) + d4124 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2075 (p : Pattern) (guard : d4119 p = 1) : d507 p ≤ (0 : Int) + d4125 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4118 p = 1 := by simpa only [d4119, d507, d4125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2071 p hg
    simpa only [d4119, d507, d4125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4119, d507, d4125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2074 p hg
    simpa only [d4119, d507, d4125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2076 (p : Pattern) (guard : d4119 p = 1) : d508 p ≤ (0 : Int) + d4125 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4119 p = 1 := by simpa only [d508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2073 p hg
    simpa only [d508, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4119 p = 1 := by simpa only [d508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2075 p hg
    simpa only [d508, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2077 (p : Pattern) (guard : d4119 p = 1) : d509 p ≤ (0 : Int) + d4126 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4119 p = 1 := by simpa only [d509, d4126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2038 p hg
    simpa only [d509, d4126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4119 p = 1 := by simpa only [d509, d4126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2076 p hg
    simpa only [d509, d4126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2078 (p : Pattern) (guard : d4119 p = 1) : d510 p ≤ (0 : Int) + d4127 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4119 p = 1 := by simpa only [d510, d4127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2044 p hg
    simpa only [d510, d4127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4119 p = 1 := by simpa only [d510, d4127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2077 p hg
    simpa only [d510, d4127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2079 (p : Pattern) (guard : d0 p = 1) : d444 p ≤ (0 : Int) + d4128 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2080 (p : Pattern) (guard : d4119 p = 1) : d503 p ≤ (0 : Int) + d4129 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4118 p = 1 := by simpa only [d4119, d503, d4129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2033 p hg
    simpa only [d4119, d503, d4129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4119, d503, d4129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2079 p hg
    simpa only [d4119, d503, d4129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2081 (p : Pattern) (guard : d4119 p = 1) : d504 p ≤ (0 : Int) + d4130 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4119 p = 1 := by simpa only [d504, d4130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2040 p hg
    simpa only [d504, d4130, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4119 p = 1 := by simpa only [d504, d4130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2080 p hg
    simpa only [d504, d4130, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2082 (p : Pattern) (guard : d4119 p = 1) : d505 p ≤ (0 : Int) + d4131 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4119 p = 1 := by simpa only [d505, d4131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2038 p hg
    simpa only [d505, d4131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4119 p = 1 := by simpa only [d505, d4131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2081 p hg
    simpa only [d505, d4131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2083 (p : Pattern) (guard : d0 p = 1) : d220 p ≤ (0 : Int) + d4132 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2084 (p : Pattern) (guard : d1 p = 1) : d211 p ≤ (0 : Int) + d215 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d211, d215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2052 p hg
    simpa only [d211, d215, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d211, d215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d211, d215, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2085 (p : Pattern) (guard : d1 p = 1) : d212 p ≤ (0 : Int) + d216 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d212, d216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2062 p hg
    simpa only [d212, d216, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d212, d216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2084 p hg
    simpa only [d212, d216, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2086 (p : Pattern) (guard : d1 p = 1) : d213 p ≤ (0 : Int) + d217 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d213, d217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2084 p hg
    simpa only [d213, d217, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d213, d217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d213, d217, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2087 (p : Pattern) (guard : d1 p = 1) : d214 p ≤ (0 : Int) + d218 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d214, d218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2085 p hg
    simpa only [d214, d218, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d214, d218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2086 p hg
    simpa only [d214, d218, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2088 (p : Pattern) (guard : d0 p = 1) : d155 p ≤ (0 : Int) + d218 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2089 (p : Pattern) (guard : d4117 p = 1) : d221 p ≤ (0 : Int) + d218 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2087 p hg
    simpa only [d4117, d221, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2088 p hg
    simpa only [d4117, d221, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2090 (p : Pattern) (guard : d4117 p = 1) : d222 p ≤ (0 : Int) + d4132 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d222, d4132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2059 p hg
    simpa only [d222, d4132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d222, d4132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2089 p hg
    simpa only [d222, d4132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2091 (p : Pattern) (guard : d4118 p = 1) : d223 p ≤ (0 : Int) + d4132 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4118, d223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2083 p hg
    simpa only [d4118, d223, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d4118, d223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2090 p hg
    simpa only [d4118, d223, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2092 (p : Pattern) (guard : d0 p = 1) : d463 p ≤ (0 : Int) + d4133 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2093 (p : Pattern) (guard : d4119 p = 1) : d511 p ≤ (0 : Int) + d4134 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4118 p = 1 := by simpa only [d4119, d511, d4134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2091 p hg
    simpa only [d4119, d511, d4134, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4119, d511, d4134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2092 p hg
    simpa only [d4119, d511, d4134, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2094 (p : Pattern) (guard : d0 p = 1) : d290 p ≤ (0 : Int) + d4135 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2095 (p : Pattern) (guard : d1 p = 1) : d291 p ≤ (0 : Int) + d271 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d291, d271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1364 p hg
    simpa only [d291, d271, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d291, d271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1343 p hg
    simpa only [d291, d271, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2096 (p : Pattern) (guard : d1 p = 1) : d269 p ≤ (0 : Int) + d272 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d269, d272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1342 p hg
    simpa only [d269, d272, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d269, d272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1595 p hg
    simpa only [d269, d272, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2097 (p : Pattern) (guard : d1 p = 1) : d273 p ≤ (0 : Int) + d273 p := by
  omega
theorem compare2098 (p : Pattern) (guard : d1 p = 1) : d292 p ≤ (0 : Int) + d274 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d292, d274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2097 p hg
    simpa only [d292, d274, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d292, d274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1283 p hg
    simpa only [d292, d274, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2099 (p : Pattern) (guard : d1 p = 1) : d293 p ≤ (0 : Int) + d275 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d293, d275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2096 p hg
    simpa only [d293, d275, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d293, d275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2098 p hg
    simpa only [d293, d275, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
