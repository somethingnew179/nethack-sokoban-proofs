/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Comparisons013
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare1960 (p : Pattern) (guard : d1087 p = 1) : d110 p ≤ (1 : Int) + d1108 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1087 p = 1 := by simpa only [d110, d1108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1924 p hg
    simpa only [d110, d1108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1087 p = 1 := by simpa only [d110, d1108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1959 p hg
    simpa only [d110, d1108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1961 (p : Pattern) (guard : d1087 p = 1) : d111 p ≤ (1 : Int) + d1112 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1087 p = 1 := by simpa only [d111, d1112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1959 p hg
    simpa only [d111, d1112, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1087 p = 1 := by simpa only [d111, d1112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1937 p hg
    simpa only [d111, d1112, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1962 (p : Pattern) (guard : d1087 p = 1) : d112 p ≤ (1 : Int) + d1113 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1087 p = 1 := by simpa only [d112, d1113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1960 p hg
    simpa only [d112, d1113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1087 p = 1 := by simpa only [d112, d1113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1961 p hg
    simpa only [d112, d1113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1963 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (1 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1964 (p : Pattern) (guard : d1096 p = 1) : d130 p ≤ (1 : Int) + d1117 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1087 p = 1 := by simpa only [d1096, d130, d1117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1962 p hg
    simpa only [d1096, d130, d1117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1096, d130, d1117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1963 p hg
    simpa only [d1096, d130, d1117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1965 (p : Pattern) (guard : d1096 p = 1) : d252 p ≤ (1 : Int) + d1118 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1096 p = 1 := by simpa only [d252, d1118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1958 p hg
    simpa only [d252, d1118, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1096 p = 1 := by simpa only [d252, d1118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1964 p hg
    simpa only [d252, d1118, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1966 (p : Pattern) (guard : d1096 p = 1) : d253 p ≤ (1 : Int) + d1119 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1096 p = 1 := by simpa only [d253, d1119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1956 p hg
    simpa only [d253, d1119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1096 p = 1 := by simpa only [d253, d1119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1965 p hg
    simpa only [d253, d1119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1967 (p : Pattern) (guard : d1096 p = 1) : d254 p ≤ (1 : Int) + d1120 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1096 p = 1 := by simpa only [d254, d1120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1951 p hg
    simpa only [d254, d1120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1096 p = 1 := by simpa only [d254, d1120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1966 p hg
    simpa only [d254, d1120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1968 (p : Pattern) (guard : d1096 p = 1) : d255 p ≤ (1 : Int) + d1121 p := by
  cases selected : p 80 with
  | false =>
    have hg : d1096 p = 1 := by simpa only [d255, d1121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1944 p hg
    simpa only [d255, d1121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1096 p = 1 := by simpa only [d255, d1121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1967 p hg
    simpa only [d255, d1121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1969 (p : Pattern) (guard : d0 p = 1) : d141 p ≤ (0 : Int) + d45 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1970 (p : Pattern) (guard : d866 p = 1) : d228 p ≤ (0 : Int) + d45 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d866, d228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare418 p hg
    simpa only [d866, d228, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d866, d228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1969 p hg
    simpa only [d866, d228, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1971 (p : Pattern) (guard : d0 p = 1) : d152 p ≤ (0 : Int) + d65 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1972 (p : Pattern) (guard : d866 p = 1) : d229 p ≤ (0 : Int) + d66 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d866, d229, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare494 p hg
    simpa only [d866, d229, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d866, d229, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1971 p hg
    simpa only [d866, d229, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1973 (p : Pattern) (guard : d866 p = 1) : d230 p ≤ (0 : Int) + d67 p := by
  cases selected : p 112 with
  | false =>
    have hg : d866 p = 1 := by simpa only [d230, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1970 p hg
    simpa only [d230, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d866 p = 1 := by simpa only [d230, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1972 p hg
    simpa only [d230, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1974 (p : Pattern) (guard : d0 p = 1) : d150 p ≤ (0 : Int) + d77 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1975 (p : Pattern) (guard : d866 p = 1) : d231 p ≤ (0 : Int) + d78 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d866, d231, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare474 p hg
    simpa only [d866, d231, d78, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d866, d231, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1974 p hg
    simpa only [d866, d231, d78, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1976 (p : Pattern) (guard : d0 p = 1) : d154 p ≤ (0 : Int) + d82 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1977 (p : Pattern) (guard : d866 p = 1) : d232 p ≤ (0 : Int) + d83 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d866, d232, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare498 p hg
    simpa only [d866, d232, d83, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d866, d232, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1976 p hg
    simpa only [d866, d232, d83, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1978 (p : Pattern) (guard : d866 p = 1) : d233 p ≤ (0 : Int) + d84 p := by
  cases selected : p 112 with
  | false =>
    have hg : d866 p = 1 := by simpa only [d233, d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1975 p hg
    simpa only [d233, d84, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d866 p = 1 := by simpa only [d233, d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1977 p hg
    simpa only [d233, d84, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1979 (p : Pattern) (guard : d866 p = 1) : d234 p ≤ (0 : Int) + d85 p := by
  cases selected : p 106 with
  | false =>
    have hg : d866 p = 1 := by simpa only [d234, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1973 p hg
    simpa only [d234, d85, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d866 p = 1 := by simpa only [d234, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1978 p hg
    simpa only [d234, d85, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1980 (p : Pattern) (guard : d0 p = 1) : d150 p ≤ (0 : Int) + d95 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1981 (p : Pattern) (guard : d866 p = 1) : d235 p ≤ (0 : Int) + d96 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d866, d235, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare418 p hg
    simpa only [d866, d235, d96, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d866, d235, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1980 p hg
    simpa only [d866, d235, d96, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1982 (p : Pattern) (guard : d0 p = 1) : d154 p ≤ (0 : Int) + d102 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1983 (p : Pattern) (guard : d866 p = 1) : d236 p ≤ (0 : Int) + d102 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d866, d236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare505 p hg
    simpa only [d866, d236, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d866, d236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1982 p hg
    simpa only [d866, d236, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1984 (p : Pattern) (guard : d866 p = 1) : d237 p ≤ (0 : Int) + d103 p := by
  cases selected : p 112 with
  | false =>
    have hg : d866 p = 1 := by simpa only [d237, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1981 p hg
    simpa only [d237, d103, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d866 p = 1 := by simpa only [d237, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1983 p hg
    simpa only [d237, d103, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1985 (p : Pattern) (guard : d0 p = 1) : d161 p ≤ (0 : Int) + d105 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1986 (p : Pattern) (guard : d866 p = 1) : d238 p ≤ (0 : Int) + d106 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d866, d238, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare429 p hg
    simpa only [d866, d238, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d866, d238, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1985 p hg
    simpa only [d866, d238, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1987 (p : Pattern) (guard : d866 p = 1) : d239 p ≤ (0 : Int) + d113 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d866, d239, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare511 p hg
    simpa only [d866, d239, d113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d866, d239, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1839 p hg
    simpa only [d866, d239, d113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1988 (p : Pattern) (guard : d866 p = 1) : d240 p ≤ (0 : Int) + d114 p := by
  cases selected : p 112 with
  | false =>
    have hg : d866 p = 1 := by simpa only [d240, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1986 p hg
    simpa only [d240, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d866 p = 1 := by simpa only [d240, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1987 p hg
    simpa only [d240, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1989 (p : Pattern) (guard : d866 p = 1) : d241 p ≤ (0 : Int) + d115 p := by
  cases selected : p 106 with
  | false =>
    have hg : d866 p = 1 := by simpa only [d241, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1984 p hg
    simpa only [d241, d115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d866 p = 1 := by simpa only [d241, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1988 p hg
    simpa only [d241, d115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1990 (p : Pattern) (guard : d866 p = 1) : d242 p ≤ (0 : Int) + d116 p := by
  cases selected : p 86 with
  | false =>
    have hg : d866 p = 1 := by simpa only [d242, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1979 p hg
    simpa only [d242, d116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d866 p = 1 := by simpa only [d242, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1989 p hg
    simpa only [d242, d116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1991 (p : Pattern) (guard : d0 p = 1) : d150 p ≤ (0 : Int) + d45 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1992 (p : Pattern) (guard : d866 p = 1) : d235 p ≤ (0 : Int) + d45 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d866, d235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare418 p hg
    simpa only [d866, d235, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d866, d235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1991 p hg
    simpa only [d866, d235, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1993 (p : Pattern) (guard : d0 p = 1) : d154 p ≤ (0 : Int) + d65 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1994 (p : Pattern) (guard : d866 p = 1) : d243 p ≤ (0 : Int) + d66 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d866, d243, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare494 p hg
    simpa only [d866, d243, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d866, d243, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1993 p hg
    simpa only [d866, d243, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1995 (p : Pattern) (guard : d866 p = 1) : d244 p ≤ (0 : Int) + d67 p := by
  cases selected : p 112 with
  | false =>
    have hg : d866 p = 1 := by simpa only [d244, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1992 p hg
    simpa only [d244, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d866 p = 1 := by simpa only [d244, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1994 p hg
    simpa only [d244, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1996 (p : Pattern) (guard : d0 p = 1) : d161 p ≤ (0 : Int) + d77 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1997 (p : Pattern) (guard : d866 p = 1) : d238 p ≤ (0 : Int) + d77 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d866, d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare429 p hg
    simpa only [d866, d238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d866, d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1996 p hg
    simpa only [d866, d238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1998 (p : Pattern) (guard : d0 p = 1) : d163 p ≤ (0 : Int) + d82 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1999 (p : Pattern) (guard : d866 p = 1) : d245 p ≤ (0 : Int) + d83 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d866, d245, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare498 p hg
    simpa only [d866, d245, d83, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d866, d245, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1998 p hg
    simpa only [d866, d245, d83, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2000 (p : Pattern) (guard : d866 p = 1) : d246 p ≤ (0 : Int) + d117 p := by
  cases selected : p 112 with
  | false =>
    have hg : d866 p = 1 := by simpa only [d246, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1997 p hg
    simpa only [d246, d117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d866 p = 1 := by simpa only [d246, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1999 p hg
    simpa only [d246, d117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2001 (p : Pattern) (guard : d866 p = 1) : d247 p ≤ (0 : Int) + d118 p := by
  cases selected : p 106 with
  | false =>
    have hg : d866 p = 1 := by simpa only [d247, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1995 p hg
    simpa only [d247, d118, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d866 p = 1 := by simpa only [d247, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2000 p hg
    simpa only [d247, d118, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2002 (p : Pattern) (guard : d0 p = 1) : d161 p ≤ (0 : Int) + d123 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2003 (p : Pattern) (guard : d866 p = 1) : d248 p ≤ (0 : Int) + d124 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d866, d248, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare418 p hg
    simpa only [d866, d248, d124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d866, d248, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2002 p hg
    simpa only [d866, d248, d124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2004 (p : Pattern) (guard : d866 p = 1) : d249 p ≤ (0 : Int) + d127 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d866, d249, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare505 p hg
    simpa only [d866, d249, d127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d866, d249, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1857 p hg
    simpa only [d866, d249, d127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2005 (p : Pattern) (guard : d866 p = 1) : d250 p ≤ (0 : Int) + d128 p := by
  cases selected : p 112 with
  | false =>
    have hg : d866 p = 1 := by simpa only [d250, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2003 p hg
    simpa only [d250, d128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d866 p = 1 := by simpa only [d250, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2004 p hg
    simpa only [d250, d128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2006 (p : Pattern) (guard : d0 p = 1) : d167 p ≤ (0 : Int) + d82 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2007 (p : Pattern) (guard : d866 p = 1) : d251 p ≤ (0 : Int) + d129 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d866, d251, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare429 p hg
    simpa only [d866, d251, d129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d866, d251, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2006 p hg
    simpa only [d866, d251, d129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2008 (p : Pattern) (guard : d866 p = 1) : d252 p ≤ (0 : Int) + d131 p := by
  cases selected : p 112 with
  | false =>
    have hg : d866 p = 1 := by simpa only [d252, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2007 p hg
    simpa only [d252, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d866 p = 1 := by simpa only [d252, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare531 p hg
    simpa only [d252, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2009 (p : Pattern) (guard : d866 p = 1) : d253 p ≤ (0 : Int) + d132 p := by
  cases selected : p 106 with
  | false =>
    have hg : d866 p = 1 := by simpa only [d253, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2005 p hg
    simpa only [d253, d132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d866 p = 1 := by simpa only [d253, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2008 p hg
    simpa only [d253, d132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2010 (p : Pattern) (guard : d866 p = 1) : d254 p ≤ (0 : Int) + d133 p := by
  cases selected : p 86 with
  | false =>
    have hg : d866 p = 1 := by simpa only [d254, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2001 p hg
    simpa only [d254, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d866 p = 1 := by simpa only [d254, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2009 p hg
    simpa only [d254, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2011 (p : Pattern) (guard : d866 p = 1) : d255 p ≤ (0 : Int) + d134 p := by
  cases selected : p 80 with
  | false =>
    have hg : d866 p = 1 := by simpa only [d255, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1990 p hg
    simpa only [d255, d134, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d866 p = 1 := by simpa only [d255, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2010 p hg
    simpa only [d255, d134, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2012 (p : Pattern) (guard : d0 p = 1) : d229 p ≤ (0 : Int) + d152 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2013 (p : Pattern) (guard : d868 p = 1) : d230 p ≤ (0 : Int) + d184 p := by
  cases selected : p 112 with
  | false =>
    have hg : d866 p = 1 := by simpa only [d868, d230, d184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1970 p hg
    simpa only [d868, d230, d184, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d868, d230, d184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2012 p hg
    simpa only [d868, d230, d184, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2014 (p : Pattern) (guard : d0 p = 1) : d232 p ≤ (0 : Int) + d155 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2015 (p : Pattern) (guard : d868 p = 1) : d233 p ≤ (0 : Int) + d185 p := by
  cases selected : p 112 with
  | false =>
    have hg : d866 p = 1 := by simpa only [d868, d233, d185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1975 p hg
    simpa only [d868, d233, d185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d868, d233, d185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2014 p hg
    simpa only [d868, d233, d185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2016 (p : Pattern) (guard : d868 p = 1) : d234 p ≤ (0 : Int) + d186 p := by
  cases selected : p 106 with
  | false =>
    have hg : d868 p = 1 := by simpa only [d234, d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2013 p hg
    simpa only [d234, d186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d868 p = 1 := by simpa only [d234, d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2015 p hg
    simpa only [d234, d186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2017 (p : Pattern) (guard : d0 p = 1) : d150 p ≤ (0 : Int) + d196 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2018 (p : Pattern) (guard : d866 p = 1) : d235 p ≤ (0 : Int) + d197 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d866, d235, d197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare418 p hg
    simpa only [d866, d235, d197, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d866, d235, d197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2017 p hg
    simpa only [d866, d235, d197, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2019 (p : Pattern) (guard : d0 p = 1) : d236 p ≤ (0 : Int) + d155 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2020 (p : Pattern) (guard : d868 p = 1) : d237 p ≤ (0 : Int) + d198 p := by
  cases selected : p 112 with
  | false =>
    have hg : d866 p = 1 := by simpa only [d868, d237, d198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2018 p hg
    simpa only [d868, d237, d198, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d868, d237, d198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2019 p hg
    simpa only [d868, d237, d198, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2021 (p : Pattern) (guard : d0 p = 1) : d161 p ≤ (0 : Int) + d203 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2022 (p : Pattern) (guard : d866 p = 1) : d238 p ≤ (0 : Int) + d204 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d866, d238, d204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare429 p hg
    simpa only [d866, d238, d204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d866, d238, d204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2021 p hg
    simpa only [d866, d238, d204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2023 (p : Pattern) (guard : d0 p = 1) : d239 p ≤ (0 : Int) + d164 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2024 (p : Pattern) (guard : d868 p = 1) : d240 p ≤ (0 : Int) + d205 p := by
  cases selected : p 112 with
  | false =>
    have hg : d866 p = 1 := by simpa only [d868, d240, d205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2022 p hg
    simpa only [d868, d240, d205, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d868, d240, d205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2023 p hg
    simpa only [d868, d240, d205, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2025 (p : Pattern) (guard : d868 p = 1) : d241 p ≤ (0 : Int) + d206 p := by
  cases selected : p 106 with
  | false =>
    have hg : d868 p = 1 := by simpa only [d241, d206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2020 p hg
    simpa only [d241, d206, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d868 p = 1 := by simpa only [d241, d206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2024 p hg
    simpa only [d241, d206, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2026 (p : Pattern) (guard : d868 p = 1) : d242 p ≤ (0 : Int) + d207 p := by
  cases selected : p 86 with
  | false =>
    have hg : d868 p = 1 := by simpa only [d242, d207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2016 p hg
    simpa only [d242, d207, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d868 p = 1 := by simpa only [d242, d207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2025 p hg
    simpa only [d242, d207, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2027 (p : Pattern) (guard : d0 p = 1) : d243 p ≤ (0 : Int) + d155 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2028 (p : Pattern) (guard : d868 p = 1) : d244 p ≤ (0 : Int) + d208 p := by
  cases selected : p 112 with
  | false =>
    have hg : d866 p = 1 := by simpa only [d868, d244, d208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1992 p hg
    simpa only [d868, d244, d208, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d868, d244, d208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2027 p hg
    simpa only [d868, d244, d208, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2029 (p : Pattern) (guard : d0 p = 1) : d245 p ≤ (0 : Int) + d164 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2030 (p : Pattern) (guard : d868 p = 1) : d246 p ≤ (0 : Int) + d209 p := by
  cases selected : p 112 with
  | false =>
    have hg : d866 p = 1 := by simpa only [d868, d246, d209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1997 p hg
    simpa only [d868, d246, d209, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d868, d246, d209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2029 p hg
    simpa only [d868, d246, d209, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2031 (p : Pattern) (guard : d868 p = 1) : d247 p ≤ (0 : Int) + d210 p := by
  cases selected : p 106 with
  | false =>
    have hg : d868 p = 1 := by simpa only [d247, d210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2028 p hg
    simpa only [d247, d210, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d868 p = 1 := by simpa only [d247, d210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2030 p hg
    simpa only [d247, d210, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2032 (p : Pattern) (guard : d0 p = 1) : d161 p ≤ (0 : Int) + d214 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2033 (p : Pattern) (guard : d866 p = 1) : d248 p ≤ (0 : Int) + d215 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d866, d248, d215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare418 p hg
    simpa only [d866, d248, d215, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d866, d248, d215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2032 p hg
    simpa only [d866, d248, d215, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2034 (p : Pattern) (guard : d0 p = 1) : d249 p ≤ (0 : Int) + d164 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2035 (p : Pattern) (guard : d868 p = 1) : d250 p ≤ (0 : Int) + d216 p := by
  cases selected : p 112 with
  | false =>
    have hg : d866 p = 1 := by simpa only [d868, d250, d216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2033 p hg
    simpa only [d868, d250, d216, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d868, d250, d216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2034 p hg
    simpa only [d868, d250, d216, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2036 (p : Pattern) (guard : d0 p = 1) : d167 p ≤ (0 : Int) + d222 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2037 (p : Pattern) (guard : d866 p = 1) : d251 p ≤ (0 : Int) + d223 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d866, d251, d223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare429 p hg
    simpa only [d866, d251, d223, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d866, d251, d223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2036 p hg
    simpa only [d866, d251, d223, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2038 (p : Pattern) (guard : d0 p = 1) : d130 p ≤ (0 : Int) + d169 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2039 (p : Pattern) (guard : d868 p = 1) : d252 p ≤ (0 : Int) + d224 p := by
  cases selected : p 112 with
  | false =>
    have hg : d866 p = 1 := by simpa only [d868, d252, d224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2037 p hg
    simpa only [d868, d252, d224, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d868, d252, d224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2038 p hg
    simpa only [d868, d252, d224, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2040 (p : Pattern) (guard : d868 p = 1) : d253 p ≤ (0 : Int) + d225 p := by
  cases selected : p 106 with
  | false =>
    have hg : d868 p = 1 := by simpa only [d253, d225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2035 p hg
    simpa only [d253, d225, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d868 p = 1 := by simpa only [d253, d225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2039 p hg
    simpa only [d253, d225, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2041 (p : Pattern) (guard : d868 p = 1) : d254 p ≤ (0 : Int) + d226 p := by
  cases selected : p 86 with
  | false =>
    have hg : d868 p = 1 := by simpa only [d254, d226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2031 p hg
    simpa only [d254, d226, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d868 p = 1 := by simpa only [d254, d226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2040 p hg
    simpa only [d254, d226, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2042 (p : Pattern) (guard : d868 p = 1) : d255 p ≤ (0 : Int) + d227 p := by
  cases selected : p 80 with
  | false =>
    have hg : d868 p = 1 := by simpa only [d255, d227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2026 p hg
    simpa only [d255, d227, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d868 p = 1 := by simpa only [d255, d227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2041 p hg
    simpa only [d255, d227, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2043 (p : Pattern) (guard : d0 p = 1) : d229 p ≤ (0 : Int) + d66 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2044 (p : Pattern) (guard : d868 p = 1) : d230 p ≤ (0 : Int) + d67 p := by
  cases selected : p 112 with
  | false =>
    have hg : d866 p = 1 := by simpa only [d868, d230, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1970 p hg
    simpa only [d868, d230, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d868, d230, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2043 p hg
    simpa only [d868, d230, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2045 (p : Pattern) (guard : d0 p = 1) : d232 p ≤ (0 : Int) + d83 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2046 (p : Pattern) (guard : d868 p = 1) : d233 p ≤ (0 : Int) + d84 p := by
  cases selected : p 112 with
  | false =>
    have hg : d866 p = 1 := by simpa only [d868, d233, d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1975 p hg
    simpa only [d868, d233, d84, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d868, d233, d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2045 p hg
    simpa only [d868, d233, d84, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2047 (p : Pattern) (guard : d868 p = 1) : d234 p ≤ (0 : Int) + d85 p := by
  cases selected : p 106 with
  | false =>
    have hg : d868 p = 1 := by simpa only [d234, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2044 p hg
    simpa only [d234, d85, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d868 p = 1 := by simpa only [d234, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2046 p hg
    simpa only [d234, d85, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2048 (p : Pattern) (guard : d0 p = 1) : d241 p ≤ (0 : Int) + d166 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2049 (p : Pattern) (guard : d869 p = 1) : d242 p ≤ (0 : Int) + d174 p := by
  cases selected : p 86 with
  | false =>
    have hg : d868 p = 1 := by simpa only [d869, d242, d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2047 p hg
    simpa only [d869, d242, d174, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d869, d242, d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2048 p hg
    simpa only [d869, d242, d174, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2050 (p : Pattern) (guard : d0 p = 1) : d243 p ≤ (0 : Int) + d66 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2051 (p : Pattern) (guard : d868 p = 1) : d244 p ≤ (0 : Int) + d67 p := by
  cases selected : p 112 with
  | false =>
    have hg : d866 p = 1 := by simpa only [d868, d244, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1992 p hg
    simpa only [d868, d244, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d868, d244, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2050 p hg
    simpa only [d868, d244, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2052 (p : Pattern) (guard : d0 p = 1) : d245 p ≤ (0 : Int) + d83 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2053 (p : Pattern) (guard : d868 p = 1) : d246 p ≤ (0 : Int) + d117 p := by
  cases selected : p 112 with
  | false =>
    have hg : d866 p = 1 := by simpa only [d868, d246, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1997 p hg
    simpa only [d868, d246, d117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d868, d246, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2052 p hg
    simpa only [d868, d246, d117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2054 (p : Pattern) (guard : d868 p = 1) : d247 p ≤ (0 : Int) + d118 p := by
  cases selected : p 106 with
  | false =>
    have hg : d868 p = 1 := by simpa only [d247, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2051 p hg
    simpa only [d247, d118, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d868 p = 1 := by simpa only [d247, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2053 p hg
    simpa only [d247, d118, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2055 (p : Pattern) (guard : d0 p = 1) : d253 p ≤ (0 : Int) + d171 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2056 (p : Pattern) (guard : d869 p = 1) : d254 p ≤ (0 : Int) + d175 p := by
  cases selected : p 86 with
  | false =>
    have hg : d868 p = 1 := by simpa only [d869, d254, d175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2054 p hg
    simpa only [d869, d254, d175, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d869, d254, d175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2055 p hg
    simpa only [d869, d254, d175, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2057 (p : Pattern) (guard : d869 p = 1) : d255 p ≤ (0 : Int) + d176 p := by
  cases selected : p 80 with
  | false =>
    have hg : d869 p = 1 := by simpa only [d255, d176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2049 p hg
    simpa only [d255, d176, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d869 p = 1 := by simpa only [d255, d176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2056 p hg
    simpa only [d255, d176, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2058 (p : Pattern) (guard : d0 p = 1) : d141 p ≤ (0 : Int) + d398 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2059 (p : Pattern) (guard : d1122 p = 1) : d228 p ≤ (0 : Int) + d398 p := by
  cases selected : p 113 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d1122, d228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1447 p hg
    simpa only [d1122, d228, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1122, d228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2058 p hg
    simpa only [d1122, d228, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2060 (p : Pattern) (guard : d1088 p = 1) : d15 p ≤ (0 : Int) + d15 p := by
  omega
theorem compare2061 (p : Pattern) (guard : d1092 p = 1) : d15 p ≤ (0 : Int) + d399 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1092, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d1092, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare853 p hg
    simpa only [d1092, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2062 (p : Pattern) (guard : d1088 p = 1) : d25 p ≤ (0 : Int) + d25 p := by
  omega
theorem compare2063 (p : Pattern) (guard : d1092 p = 1) : d25 p ≤ (0 : Int) + d400 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1092, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2062 p hg
    simpa only [d1092, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare855 p hg
    simpa only [d1092, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2064 (p : Pattern) (guard : d1092 p = 1) : d46 p ≤ (0 : Int) + d401 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d46, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2061 p hg
    simpa only [d46, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d46, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2063 p hg
    simpa only [d46, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2065 (p : Pattern) (guard : d1092 p = 1) : d47 p ≤ (0 : Int) + d402 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d47, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2061 p hg
    simpa only [d47, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d47, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2064 p hg
    simpa only [d47, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2066 (p : Pattern) (guard : d1088 p = 1) : d34 p ≤ (0 : Int) + d34 p := by
  omega
theorem compare2067 (p : Pattern) (guard : d1092 p = 1) : d34 p ≤ (0 : Int) + d403 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1092, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2066 p hg
    simpa only [d1092, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare858 p hg
    simpa only [d1092, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2068 (p : Pattern) (guard : d1092 p = 1) : d48 p ≤ (0 : Int) + d404 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d48, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2061 p hg
    simpa only [d48, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d48, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2067 p hg
    simpa only [d48, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2069 (p : Pattern) (guard : d1088 p = 1) : d41 p ≤ (0 : Int) + d41 p := by
  omega
theorem compare2070 (p : Pattern) (guard : d1092 p = 1) : d41 p ≤ (0 : Int) + d405 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1092, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2069 p hg
    simpa only [d1092, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1443 p hg
    simpa only [d1092, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2071 (p : Pattern) (guard : d1092 p = 1) : d49 p ≤ (0 : Int) + d406 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d49, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2070 p hg
    simpa only [d49, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d49, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2063 p hg
    simpa only [d49, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2072 (p : Pattern) (guard : d1092 p = 1) : d50 p ≤ (0 : Int) + d407 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d50, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2068 p hg
    simpa only [d50, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d50, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2071 p hg
    simpa only [d50, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2073 (p : Pattern) (guard : d1092 p = 1) : d51 p ≤ (0 : Int) + d408 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d51, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2065 p hg
    simpa only [d51, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d51, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2072 p hg
    simpa only [d51, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2074 (p : Pattern) (guard : d1125 p = 1) : d229 p ≤ (0 : Int) + d408 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d1125, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2073 p hg
    simpa only [d1125, d229, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1125, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1448 p hg
    simpa only [d1125, d229, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2075 (p : Pattern) (guard : d1126 p = 1) : d230 p ≤ (0 : Int) + d409 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1122 p = 1 := by simpa only [d1126, d230, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2059 p hg
    simpa only [d1126, d230, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1125 p = 1 := by simpa only [d1126, d230, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2074 p hg
    simpa only [d1126, d230, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2076 (p : Pattern) (guard : d0 p = 1) : d150 p ≤ (0 : Int) + d416 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2077 (p : Pattern) (guard : d1122 p = 1) : d231 p ≤ (0 : Int) + d417 p := by
  cases selected : p 113 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d1122, d231, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1457 p hg
    simpa only [d1122, d231, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1122, d231, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2076 p hg
    simpa only [d1122, d231, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2078 (p : Pattern) (guard : d1092 p = 1) : d68 p ≤ (0 : Int) + d199 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1092, d199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1633 p hg
    simpa only [d1092, d199, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1451 p hg
    simpa only [d1092, d199, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2079 (p : Pattern) (guard : d1092 p = 1) : d70 p ≤ (0 : Int) + d200 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1092, d200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1636 p hg
    simpa only [d1092, d200, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare882 p hg
    simpa only [d1092, d200, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2080 (p : Pattern) (guard : d1092 p = 1) : d75 p ≤ (0 : Int) + d201 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d75, d201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2078 p hg
    simpa only [d75, d201, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d75, d201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2079 p hg
    simpa only [d75, d201, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2081 (p : Pattern) (guard : d1092 p = 1) : d79 p ≤ (0 : Int) + d418 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d79, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2064 p hg
    simpa only [d79, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d79, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2080 p hg
    simpa only [d79, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2082 (p : Pattern) (guard : d1092 p = 1) : d80 p ≤ (0 : Int) + d419 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d80, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2065 p hg
    simpa only [d80, d419, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d80, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2081 p hg
    simpa only [d80, d419, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2083 (p : Pattern) (guard : d0 p = 1) : d154 p ≤ (0 : Int) + d419 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2084 (p : Pattern) (guard : d1125 p = 1) : d232 p ≤ (0 : Int) + d419 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d1125, d232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2082 p hg
    simpa only [d1125, d232, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1125, d232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2083 p hg
    simpa only [d1125, d232, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2085 (p : Pattern) (guard : d1126 p = 1) : d233 p ≤ (0 : Int) + d420 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1122 p = 1 := by simpa only [d1126, d233, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2077 p hg
    simpa only [d1126, d233, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1125 p = 1 := by simpa only [d1126, d233, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2084 p hg
    simpa only [d1126, d233, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2086 (p : Pattern) (guard : d1126 p = 1) : d234 p ≤ (0 : Int) + d421 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1126 p = 1 := by simpa only [d234, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2075 p hg
    simpa only [d234, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1126 p = 1 := by simpa only [d234, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2085 p hg
    simpa only [d234, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2087 (p : Pattern) (guard : d0 p = 1) : d150 p ≤ (0 : Int) + d398 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2088 (p : Pattern) (guard : d1122 p = 1) : d235 p ≤ (0 : Int) + d398 p := by
  cases selected : p 113 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d1122, d235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1447 p hg
    simpa only [d1122, d235, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1122, d235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2087 p hg
    simpa only [d1122, d235, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2089 (p : Pattern) (guard : d1088 p = 1) : d14 p ≤ (0 : Int) + d14 p := by
  omega
theorem compare2090 (p : Pattern) (guard : d1092 p = 1) : d98 p ≤ (0 : Int) + d422 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1092, d98, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2089 p hg
    simpa only [d1092, d98, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d98, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare919 p hg
    simpa only [d1092, d98, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2091 (p : Pattern) (guard : d1088 p = 1) : d24 p ≤ (0 : Int) + d24 p := by
  omega
theorem compare2092 (p : Pattern) (guard : d1092 p = 1) : d71 p ≤ (0 : Int) + d411 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1092, d71, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2091 p hg
    simpa only [d1092, d71, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d71, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare882 p hg
    simpa only [d1092, d71, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2093 (p : Pattern) (guard : d1092 p = 1) : d99 p ≤ (0 : Int) + d423 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d99, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2090 p hg
    simpa only [d99, d423, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d99, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2092 p hg
    simpa only [d99, d423, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2094 (p : Pattern) (guard : d1092 p = 1) : d100 p ≤ (0 : Int) + d424 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d100, d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2090 p hg
    simpa only [d100, d424, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d100, d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2093 p hg
    simpa only [d100, d424, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2095 (p : Pattern) (guard : d1088 p = 1) : d40 p ≤ (0 : Int) + d40 p := by
  omega
theorem compare2096 (p : Pattern) (guard : d1092 p = 1) : d69 p ≤ (0 : Int) + d410 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1092, d69, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2095 p hg
    simpa only [d1092, d69, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d69, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1451 p hg
    simpa only [d1092, d69, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2097 (p : Pattern) (guard : d1092 p = 1) : d72 p ≤ (0 : Int) + d412 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d72, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2096 p hg
    simpa only [d72, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d72, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2092 p hg
    simpa only [d72, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2098 (p : Pattern) (guard : d1092 p = 1) : d101 p ≤ (0 : Int) + d425 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d101, d425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2093 p hg
    simpa only [d101, d425, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d101, d425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2097 p hg
    simpa only [d101, d425, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2099 (p : Pattern) (guard : d1092 p = 1) : d102 p ≤ (0 : Int) + d426 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d102, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2094 p hg
    simpa only [d102, d426, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d102, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2098 p hg
    simpa only [d102, d426, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban32Refined
