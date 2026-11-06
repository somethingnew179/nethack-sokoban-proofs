/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Comparisons072
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare10220 (p : Pattern) (guard : d1971 p = 1) : d430 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10218 p hg
    simpa only [d1971, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10219 p hg
    simpa only [d1971, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10221 (p : Pattern) (guard : d0 p = 1) : d431 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10222 (p : Pattern) (guard : d1976 p = 1) : d432 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1971 p = 1 := by simpa only [d1976, d432, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10220 p hg
    simpa only [d1976, d432, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1976, d432, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10221 p hg
    simpa only [d1976, d432, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10223 (p : Pattern) (guard : d0 p = 1) : d433 p ≤ (0 : Int) + d152 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10224 (p : Pattern) (guard : d1981 p = 1) : d434 p ≤ (0 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1976 p = 1 := by simpa only [d1981, d434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10222 p hg
    simpa only [d1981, d434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1981, d434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10223 p hg
    simpa only [d1981, d434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10225 (p : Pattern) (guard : d1982 p = 1) : d435 p ≤ (0 : Int) + d152 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1977 p = 1 := by simpa only [d1982, d435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10217 p hg
    simpa only [d1982, d435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1981 p = 1 := by simpa only [d1982, d435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10224 p hg
    simpa only [d1982, d435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10226 (p : Pattern) (guard : d1983 p = 1) : d436 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1978 p = 1 := by simpa only [d1983, d436, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10215 p hg
    simpa only [d1983, d436, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1982 p = 1 := by simpa only [d1983, d436, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10225 p hg
    simpa only [d1983, d436, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10227 (p : Pattern) (guard : d1984 p = 1) : d437 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1979 p = 1 := by simpa only [d1984, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10204 p hg
    simpa only [d1984, d437, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1983 p = 1 := by simpa only [d1984, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10226 p hg
    simpa only [d1984, d437, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10228 (p : Pattern) (guard : d1985 p = 1) : d438 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1980 p = 1 := by simpa only [d1985, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10173 p hg
    simpa only [d1985, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1984 p = 1 := by simpa only [d1985, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10227 p hg
    simpa only [d1985, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10229 (p : Pattern) (guard : d0 p = 1) : d403 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10230 (p : Pattern) (guard : d1971 p = 1) : d404 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d404, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10166 p hg
    simpa only [d1971, d404, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d404, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10229 p hg
    simpa only [d1971, d404, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10231 (p : Pattern) (guard : d0 p = 1) : d406 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10232 (p : Pattern) (guard : d1976 p = 1) : d407 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1971 p = 1 := by simpa only [d1976, d407, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10230 p hg
    simpa only [d1976, d407, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1976, d407, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10231 p hg
    simpa only [d1976, d407, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10233 (p : Pattern) (guard : d1977 p = 1) : d408 p ≤ (0 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1972 p = 1 := by simpa only [d1977, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10165 p hg
    simpa only [d1977, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1976 p = 1 := by simpa only [d1977, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10232 p hg
    simpa only [d1977, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10234 (p : Pattern) (guard : d1978 p = 1) : d408 p ≤ (0 : Int) + d152 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1973 p = 1 := by simpa only [d1978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10135 p hg
    simpa only [d1978, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1977 p = 1 := by simpa only [d1978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10233 p hg
    simpa only [d1978, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10235 (p : Pattern) (guard : d1979 p = 1) : d409 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1974 p = 1 := by simpa only [d1979, d409, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10181 p hg
    simpa only [d1979, d409, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1978 p = 1 := by simpa only [d1979, d409, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10234 p hg
    simpa only [d1979, d409, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10236 (p : Pattern) (guard : d0 p = 1) : d399 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10237 (p : Pattern) (guard : d1971 p = 1) : d399 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10166 p hg
    simpa only [d1971, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10236 p hg
    simpa only [d1971, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10238 (p : Pattern) (guard : d0 p = 1) : d401 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10239 (p : Pattern) (guard : d1976 p = 1) : d402 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1971 p = 1 := by simpa only [d1976, d402, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10237 p hg
    simpa only [d1976, d402, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1976, d402, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10238 p hg
    simpa only [d1976, d402, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10240 (p : Pattern) (guard : d0 p = 1) : d418 p ≤ (0 : Int) + d152 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10241 (p : Pattern) (guard : d1981 p = 1) : d419 p ≤ (0 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1976 p = 1 := by simpa only [d1981, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10239 p hg
    simpa only [d1981, d419, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1981, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10240 p hg
    simpa only [d1981, d419, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10242 (p : Pattern) (guard : d1982 p = 1) : d419 p ≤ (0 : Int) + d152 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1977 p = 1 := by simpa only [d1982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10170 p hg
    simpa only [d1982, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1981 p = 1 := by simpa only [d1982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10241 p hg
    simpa only [d1982, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10243 (p : Pattern) (guard : d1983 p = 1) : d439 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1978 p = 1 := by simpa only [d1983, d439, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10215 p hg
    simpa only [d1983, d439, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1982 p = 1 := by simpa only [d1983, d439, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10242 p hg
    simpa only [d1983, d439, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10244 (p : Pattern) (guard : d1984 p = 1) : d440 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1979 p = 1 := by simpa only [d1984, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10235 p hg
    simpa only [d1984, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1983 p = 1 := by simpa only [d1984, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10243 p hg
    simpa only [d1984, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10245 (p : Pattern) (guard : d0 p = 1) : d441 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10246 (p : Pattern) (guard : d1971 p = 1) : d442 p ≤ (0 : Int) + d137 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d442, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10210 p hg
    simpa only [d1971, d442, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d442, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10245 p hg
    simpa only [d1971, d442, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10247 (p : Pattern) (guard : d0 p = 1) : d396 p ≤ (0 : Int) + d140 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10248 (p : Pattern) (guard : d1976 p = 1) : d443 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1971 p = 1 := by simpa only [d1976, d443, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10246 p hg
    simpa only [d1976, d443, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1976, d443, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10247 p hg
    simpa only [d1976, d443, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10249 (p : Pattern) (guard : d1977 p = 1) : d444 p ≤ (0 : Int) + d141 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1972 p = 1 := by simpa only [d1977, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10209 p hg
    simpa only [d1977, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1976 p = 1 := by simpa only [d1977, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10248 p hg
    simpa only [d1977, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10250 (p : Pattern) (guard : d1978 p = 1) : d445 p ≤ (0 : Int) + d141 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1973 p = 1 := by simpa only [d1978, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10180 p hg
    simpa only [d1978, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1977 p = 1 := by simpa only [d1978, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10249 p hg
    simpa only [d1978, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10251 (p : Pattern) (guard : d0 p = 1) : d446 p ≤ (0 : Int) + d152 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10252 (p : Pattern) (guard : d1981 p = 1) : d447 p ≤ (0 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1976 p = 1 := by simpa only [d1981, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10222 p hg
    simpa only [d1981, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1981, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10251 p hg
    simpa only [d1981, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10253 (p : Pattern) (guard : d1982 p = 1) : d448 p ≤ (0 : Int) + d152 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1977 p = 1 := by simpa only [d1982, d448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10202 p hg
    simpa only [d1982, d448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1981 p = 1 := by simpa only [d1982, d448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10252 p hg
    simpa only [d1982, d448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10254 (p : Pattern) (guard : d1983 p = 1) : d449 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1978 p = 1 := by simpa only [d1983, d449, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10250 p hg
    simpa only [d1983, d449, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1982 p = 1 := by simpa only [d1983, d449, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10253 p hg
    simpa only [d1983, d449, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10255 (p : Pattern) (guard : d1966 p = 1) : d399 p ≤ (0 : Int) + d136 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d399, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9772 p hg
    simpa only [d1966, d399, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d399, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1966, d399, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10256 (p : Pattern) (guard : d1971 p = 1) : d399 p ≤ (0 : Int) + d137 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10255 p hg
    simpa only [d1971, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10236 p hg
    simpa only [d1971, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10257 (p : Pattern) (guard : d0 p = 1) : d401 p ≤ (0 : Int) + d140 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10258 (p : Pattern) (guard : d1976 p = 1) : d402 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1971 p = 1 := by simpa only [d1976, d402, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10256 p hg
    simpa only [d1976, d402, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1976, d402, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10257 p hg
    simpa only [d1976, d402, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10259 (p : Pattern) (guard : d0 p = 1) : d418 p ≤ (0 : Int) + d141 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10260 (p : Pattern) (guard : d1981 p = 1) : d419 p ≤ (0 : Int) + d141 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1976 p = 1 := by simpa only [d1981, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10258 p hg
    simpa only [d1981, d419, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1981, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10259 p hg
    simpa only [d1981, d419, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10261 (p : Pattern) (guard : d1982 p = 1) : d450 p ≤ (0 : Int) + d141 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1977 p = 1 := by simpa only [d1982, d450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10214 p hg
    simpa only [d1982, d450, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1981 p = 1 := by simpa only [d1982, d450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10260 p hg
    simpa only [d1982, d450, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10262 (p : Pattern) (guard : d1986 p = 1) : d451 p ≤ (0 : Int) + d152 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1981 p = 1 := by simpa only [d1986, d451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10224 p hg
    simpa only [d1986, d451, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1986, d451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9780 p hg
    simpa only [d1986, d451, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10263 (p : Pattern) (guard : d1987 p = 1) : d452 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1982 p = 1 := by simpa only [d1987, d452, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10261 p hg
    simpa only [d1987, d452, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1986 p = 1 := by simpa only [d1987, d452, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10262 p hg
    simpa only [d1987, d452, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10264 (p : Pattern) (guard : d1988 p = 1) : d453 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1983 p = 1 := by simpa only [d1988, d453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10254 p hg
    simpa only [d1988, d453, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1987 p = 1 := by simpa only [d1988, d453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10263 p hg
    simpa only [d1988, d453, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10265 (p : Pattern) (guard : d1989 p = 1) : d454 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1984 p = 1 := by simpa only [d1989, d454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10244 p hg
    simpa only [d1989, d454, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1988 p = 1 := by simpa only [d1989, d454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10264 p hg
    simpa only [d1989, d454, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10266 (p : Pattern) (guard : d1990 p = 1) : d455 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 80 with
  | false =>
    have hg : d1985 p = 1 := by simpa only [d1990, d455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10228 p hg
    simpa only [d1990, d455, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1989 p = 1 := by simpa only [d1990, d455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10265 p hg
    simpa only [d1990, d455, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10267 (p : Pattern) (guard : d1 p = 1) : d23 p ≤ (0 : Int) + d23 p := by
  omega
theorem compare10268 (p : Pattern) (guard : d1 p = 1) : d538 p ≤ (0 : Int) + d135 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d538, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9482 p hg
    simpa only [d538, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d538, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10267 p hg
    simpa only [d538, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10269 (p : Pattern) (guard : d1944 p = 1) : d23 p ≤ (0 : Int) + d23 p := by
  omega
theorem compare10270 (p : Pattern) (guard : d1945 p = 1) : d538 p ≤ (0 : Int) + d135 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1945, d538, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9482 p hg
    simpa only [d1945, d538, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1944 p = 1 := by simpa only [d1945, d538, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10269 p hg
    simpa only [d1945, d538, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10271 (p : Pattern) (guard : d1946 p = 1) : d538 p ≤ (0 : Int) + d135 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10268 p hg
    simpa only [d1946, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1945 p = 1 := by simpa only [d1946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10270 p hg
    simpa only [d1946, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10272 (p : Pattern) (guard : d1944 p = 1) : d2 p ≤ (0 : Int) + d2 p := by
  omega
theorem compare10273 (p : Pattern) (guard : d1945 p = 1) : d539 p ≤ (0 : Int) + d2 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1945, d539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9491 p hg
    simpa only [d1945, d539, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1944 p = 1 := by simpa only [d1945, d539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10272 p hg
    simpa only [d1945, d539, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10274 (p : Pattern) (guard : d1947 p = 1) : d2 p ≤ (0 : Int) + d2 p := by
  omega
theorem compare10275 (p : Pattern) (guard : d1948 p = 1) : d540 p ≤ (0 : Int) + d2 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1944 p = 1 := by simpa only [d1948, d540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9495 p hg
    simpa only [d1948, d540, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1947 p = 1 := by simpa only [d1948, d540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10274 p hg
    simpa only [d1948, d540, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10276 (p : Pattern) (guard : d1949 p = 1) : d541 p ≤ (0 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1945 p = 1 := by simpa only [d1949, d541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10273 p hg
    simpa only [d1949, d541, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1948 p = 1 := by simpa only [d1949, d541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10275 p hg
    simpa only [d1949, d541, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10277 (p : Pattern) (guard : d1950 p = 1) : d542 p ≤ (0 : Int) + d136 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1946 p = 1 := by simpa only [d1950, d542, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10271 p hg
    simpa only [d1950, d542, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1949 p = 1 := by simpa only [d1950, d542, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10276 p hg
    simpa only [d1950, d542, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10278 (p : Pattern) (guard : d1948 p = 1) : d539 p ≤ (0 : Int) + d2 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1944 p = 1 := by simpa only [d1948, d539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9511 p hg
    simpa only [d1948, d539, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1947 p = 1 := by simpa only [d1948, d539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10274 p hg
    simpa only [d1948, d539, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10279 (p : Pattern) (guard : d1949 p = 1) : d539 p ≤ (0 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1945 p = 1 := by simpa only [d1949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10273 p hg
    simpa only [d1949, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1948 p = 1 := by simpa only [d1949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10278 p hg
    simpa only [d1949, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10280 (p : Pattern) (guard : d1951 p = 1) : d2 p ≤ (0 : Int) + d2 p := by
  omega
theorem compare10281 (p : Pattern) (guard : d1952 p = 1) : d540 p ≤ (0 : Int) + d2 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1947 p = 1 := by simpa only [d1952, d540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9515 p hg
    simpa only [d1952, d540, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1951 p = 1 := by simpa only [d1952, d540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10280 p hg
    simpa only [d1952, d540, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10282 (p : Pattern) (guard : d1953 p = 1) : d541 p ≤ (0 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1948 p = 1 := by simpa only [d1953, d541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10278 p hg
    simpa only [d1953, d541, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1952 p = 1 := by simpa only [d1953, d541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10281 p hg
    simpa only [d1953, d541, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10283 (p : Pattern) (guard : d1954 p = 1) : d543 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1949 p = 1 := by simpa only [d1954, d543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10279 p hg
    simpa only [d1954, d543, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1953 p = 1 := by simpa only [d1954, d543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10282 p hg
    simpa only [d1954, d543, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10284 (p : Pattern) (guard : d1955 p = 1) : d544 p ≤ (0 : Int) + d137 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1950 p = 1 := by simpa only [d1955, d544, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10277 p hg
    simpa only [d1955, d544, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1954 p = 1 := by simpa only [d1955, d544, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10283 p hg
    simpa only [d1955, d544, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10285 (p : Pattern) (guard : d1945 p = 1) : d539 p ≤ (0 : Int) + d138 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1945, d539, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9503 p hg
    simpa only [d1945, d539, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1944 p = 1 := by simpa only [d1945, d539, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10272 p hg
    simpa only [d1945, d539, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10286 (p : Pattern) (guard : d1948 p = 1) : d539 p ≤ (0 : Int) + d138 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1944 p = 1 := by simpa only [d1948, d539, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9506 p hg
    simpa only [d1948, d539, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1947 p = 1 := by simpa only [d1948, d539, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10274 p hg
    simpa only [d1948, d539, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10287 (p : Pattern) (guard : d1949 p = 1) : d539 p ≤ (0 : Int) + d138 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1945 p = 1 := by simpa only [d1949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10285 p hg
    simpa only [d1949, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1948 p = 1 := by simpa only [d1949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10286 p hg
    simpa only [d1949, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10288 (p : Pattern) (guard : d1954 p = 1) : d543 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1949 p = 1 := by simpa only [d1954, d543, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10287 p hg
    simpa only [d1954, d543, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1953 p = 1 := by simpa only [d1954, d543, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10282 p hg
    simpa only [d1954, d543, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10289 (p : Pattern) (guard : d1948 p = 1) : d545 p ≤ (0 : Int) + d2 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1944 p = 1 := by simpa only [d1948, d545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9790 p hg
    simpa only [d1948, d545, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1947 p = 1 := by simpa only [d1948, d545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10274 p hg
    simpa only [d1948, d545, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10290 (p : Pattern) (guard : d1952 p = 1) : d545 p ≤ (0 : Int) + d2 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1947 p = 1 := by simpa only [d1952, d545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9794 p hg
    simpa only [d1952, d545, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1951 p = 1 := by simpa only [d1952, d545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10280 p hg
    simpa only [d1952, d545, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10291 (p : Pattern) (guard : d1953 p = 1) : d545 p ≤ (0 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1948 p = 1 := by simpa only [d1953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10289 p hg
    simpa only [d1953, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1952 p = 1 := by simpa only [d1953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10290 p hg
    simpa only [d1953, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10292 (p : Pattern) (guard : d1956 p = 1) : d546 p ≤ (0 : Int) + d2 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1951 p = 1 := by simpa only [d1956, d546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9798 p hg
    simpa only [d1956, d546, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1956, d546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1956, d546, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10293 (p : Pattern) (guard : d1957 p = 1) : d547 p ≤ (0 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1952 p = 1 := by simpa only [d1957, d547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10290 p hg
    simpa only [d1957, d547, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1956 p = 1 := by simpa only [d1957, d547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10292 p hg
    simpa only [d1957, d547, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10294 (p : Pattern) (guard : d1958 p = 1) : d548 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1953 p = 1 := by simpa only [d1958, d548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10291 p hg
    simpa only [d1958, d548, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1957 p = 1 := by simpa only [d1958, d548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10293 p hg
    simpa only [d1958, d548, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10295 (p : Pattern) (guard : d1959 p = 1) : d549 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1954 p = 1 := by simpa only [d1959, d549, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10288 p hg
    simpa only [d1959, d549, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1958 p = 1 := by simpa only [d1959, d549, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10294 p hg
    simpa only [d1959, d549, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10296 (p : Pattern) (guard : d1960 p = 1) : d550 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1955 p = 1 := by simpa only [d1960, d550, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10284 p hg
    simpa only [d1960, d550, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1959 p = 1 := by simpa only [d1960, d550, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10295 p hg
    simpa only [d1960, d550, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10297 (p : Pattern) (guard : d1947 p = 1) : d23 p ≤ (0 : Int) + d23 p := by
  omega
theorem compare10298 (p : Pattern) (guard : d1948 p = 1) : d538 p ≤ (0 : Int) + d135 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1944 p = 1 := by simpa only [d1948, d538, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9524 p hg
    simpa only [d1948, d538, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1947 p = 1 := by simpa only [d1948, d538, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10297 p hg
    simpa only [d1948, d538, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10299 (p : Pattern) (guard : d1949 p = 1) : d538 p ≤ (0 : Int) + d135 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1945 p = 1 := by simpa only [d1949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10270 p hg
    simpa only [d1949, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1948 p = 1 := by simpa only [d1949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10298 p hg
    simpa only [d1949, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10300 (p : Pattern) (guard : d1954 p = 1) : d542 p ≤ (0 : Int) + d136 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1949 p = 1 := by simpa only [d1954, d542, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10299 p hg
    simpa only [d1954, d542, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1953 p = 1 := by simpa only [d1954, d542, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10282 p hg
    simpa only [d1954, d542, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10301 (p : Pattern) (guard : d1948 p = 1) : d551 p ≤ (0 : Int) + d2 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1944 p = 1 := by simpa only [d1948, d551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9805 p hg
    simpa only [d1948, d551, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1947 p = 1 := by simpa only [d1948, d551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10274 p hg
    simpa only [d1948, d551, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10302 (p : Pattern) (guard : d1952 p = 1) : d551 p ≤ (0 : Int) + d2 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1947 p = 1 := by simpa only [d1952, d551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9810 p hg
    simpa only [d1952, d551, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1951 p = 1 := by simpa only [d1952, d551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10280 p hg
    simpa only [d1952, d551, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10303 (p : Pattern) (guard : d1953 p = 1) : d551 p ≤ (0 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1948 p = 1 := by simpa only [d1953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10301 p hg
    simpa only [d1953, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1952 p = 1 := by simpa only [d1953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10302 p hg
    simpa only [d1953, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10304 (p : Pattern) (guard : d1957 p = 1) : d552 p ≤ (0 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1952 p = 1 := by simpa only [d1957, d552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10302 p hg
    simpa only [d1957, d552, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1956 p = 1 := by simpa only [d1957, d552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10292 p hg
    simpa only [d1957, d552, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10305 (p : Pattern) (guard : d1958 p = 1) : d553 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1953 p = 1 := by simpa only [d1958, d553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10303 p hg
    simpa only [d1958, d553, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1957 p = 1 := by simpa only [d1958, d553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10304 p hg
    simpa only [d1958, d553, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10306 (p : Pattern) (guard : d1959 p = 1) : d554 p ≤ (0 : Int) + d137 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1954 p = 1 := by simpa only [d1959, d554, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10300 p hg
    simpa only [d1959, d554, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1958 p = 1 := by simpa only [d1959, d554, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10305 p hg
    simpa only [d1959, d554, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10307 (p : Pattern) (guard : d1952 p = 1) : d539 p ≤ (0 : Int) + d138 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1947 p = 1 := by simpa only [d1952, d539, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9534 p hg
    simpa only [d1952, d539, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1951 p = 1 := by simpa only [d1952, d539, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10280 p hg
    simpa only [d1952, d539, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10308 (p : Pattern) (guard : d1953 p = 1) : d539 p ≤ (0 : Int) + d138 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1948 p = 1 := by simpa only [d1953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10286 p hg
    simpa only [d1953, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1952 p = 1 := by simpa only [d1953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10307 p hg
    simpa only [d1953, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10309 (p : Pattern) (guard : d1952 p = 1) : d539 p ≤ (0 : Int) + d2 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1947 p = 1 := by simpa only [d1952, d539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9538 p hg
    simpa only [d1952, d539, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1951 p = 1 := by simpa only [d1952, d539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10280 p hg
    simpa only [d1952, d539, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10310 (p : Pattern) (guard : d1956 p = 1) : d540 p ≤ (0 : Int) + d2 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1951 p = 1 := by simpa only [d1956, d540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9540 p hg
    simpa only [d1956, d540, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1956, d540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1956, d540, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10311 (p : Pattern) (guard : d1957 p = 1) : d541 p ≤ (0 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1952 p = 1 := by simpa only [d1957, d541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10309 p hg
    simpa only [d1957, d541, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1956 p = 1 := by simpa only [d1957, d541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10310 p hg
    simpa only [d1957, d541, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10312 (p : Pattern) (guard : d1958 p = 1) : d543 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1953 p = 1 := by simpa only [d1958, d543, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10308 p hg
    simpa only [d1958, d543, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1957 p = 1 := by simpa only [d1958, d543, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10311 p hg
    simpa only [d1958, d543, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10313 (p : Pattern) (guard : d1956 p = 1) : d545 p ≤ (0 : Int) + d2 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1951 p = 1 := by simpa only [d1956, d545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9817 p hg
    simpa only [d1956, d545, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1956, d545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1956, d545, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10314 (p : Pattern) (guard : d1957 p = 1) : d545 p ≤ (0 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1952 p = 1 := by simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10290 p hg
    simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1956 p = 1 := by simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10313 p hg
    simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10315 (p : Pattern) (guard : d0 p = 1) : d546 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10316 (p : Pattern) (guard : d1961 p = 1) : d547 p ≤ (0 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1956 p = 1 := by simpa only [d1961, d547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10313 p hg
    simpa only [d1961, d547, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1961, d547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10315 p hg
    simpa only [d1961, d547, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10317 (p : Pattern) (guard : d1962 p = 1) : d548 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1957 p = 1 := by simpa only [d1962, d548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10314 p hg
    simpa only [d1962, d548, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1961 p = 1 := by simpa only [d1962, d548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10316 p hg
    simpa only [d1962, d548, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10318 (p : Pattern) (guard : d1963 p = 1) : d549 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1958 p = 1 := by simpa only [d1963, d549, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10312 p hg
    simpa only [d1963, d549, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1962 p = 1 := by simpa only [d1963, d549, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10317 p hg
    simpa only [d1963, d549, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10319 (p : Pattern) (guard : d1964 p = 1) : d555 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1959 p = 1 := by simpa only [d1964, d555, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10306 p hg
    simpa only [d1964, d555, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1963 p = 1 := by simpa only [d1964, d555, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10318 p hg
    simpa only [d1964, d555, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10320 (p : Pattern) (guard : d1965 p = 1) : d556 p ≤ (0 : Int) + d141 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1960 p = 1 := by simpa only [d1965, d556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10296 p hg
    simpa only [d1965, d556, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1964 p = 1 := by simpa only [d1965, d556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10319 p hg
    simpa only [d1965, d556, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10321 (p : Pattern) (guard : d1953 p = 1) : d539 p ≤ (0 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1948 p = 1 := by simpa only [d1953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10278 p hg
    simpa only [d1953, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1952 p = 1 := by simpa only [d1953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10309 p hg
    simpa only [d1953, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10322 (p : Pattern) (guard : d1958 p = 1) : d543 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1953 p = 1 := by simpa only [d1958, d543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10321 p hg
    simpa only [d1958, d543, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1957 p = 1 := by simpa only [d1958, d543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10311 p hg
    simpa only [d1958, d543, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10323 (p : Pattern) (guard : d1959 p = 1) : d544 p ≤ (0 : Int) + d137 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1954 p = 1 := by simpa only [d1959, d544, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10300 p hg
    simpa only [d1959, d544, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1958 p = 1 := by simpa only [d1959, d544, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10322 p hg
    simpa only [d1959, d544, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10324 (p : Pattern) (guard : d1964 p = 1) : d550 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1959 p = 1 := by simpa only [d1964, d550, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10323 p hg
    simpa only [d1964, d550, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1963 p = 1 := by simpa only [d1964, d550, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10318 p hg
    simpa only [d1964, d550, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10325 (p : Pattern) (guard : d1951 p = 1) : d23 p ≤ (0 : Int) + d23 p := by
  omega
theorem compare10326 (p : Pattern) (guard : d1952 p = 1) : d538 p ≤ (0 : Int) + d135 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1947 p = 1 := by simpa only [d1952, d538, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9559 p hg
    simpa only [d1952, d538, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1951 p = 1 := by simpa only [d1952, d538, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10325 p hg
    simpa only [d1952, d538, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10327 (p : Pattern) (guard : d1953 p = 1) : d538 p ≤ (0 : Int) + d135 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1948 p = 1 := by simpa only [d1953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10298 p hg
    simpa only [d1953, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1952 p = 1 := by simpa only [d1953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10326 p hg
    simpa only [d1953, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10328 (p : Pattern) (guard : d1958 p = 1) : d542 p ≤ (0 : Int) + d136 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1953 p = 1 := by simpa only [d1958, d542, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10327 p hg
    simpa only [d1958, d542, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1957 p = 1 := by simpa only [d1958, d542, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10311 p hg
    simpa only [d1958, d542, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10329 (p : Pattern) (guard : d1956 p = 1) : d551 p ≤ (0 : Int) + d2 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1951 p = 1 := by simpa only [d1956, d551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9830 p hg
    simpa only [d1956, d551, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1956, d551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1956, d551, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10330 (p : Pattern) (guard : d1957 p = 1) : d551 p ≤ (0 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1952 p = 1 := by simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10302 p hg
    simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1956 p = 1 := by simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10329 p hg
    simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10331 (p : Pattern) (guard : d1961 p = 1) : d552 p ≤ (0 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1956 p = 1 := by simpa only [d1961, d552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10329 p hg
    simpa only [d1961, d552, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1961, d552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10315 p hg
    simpa only [d1961, d552, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10332 (p : Pattern) (guard : d1962 p = 1) : d553 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1957 p = 1 := by simpa only [d1962, d553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10330 p hg
    simpa only [d1962, d553, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1961 p = 1 := by simpa only [d1962, d553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10331 p hg
    simpa only [d1962, d553, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10333 (p : Pattern) (guard : d1963 p = 1) : d554 p ≤ (0 : Int) + d137 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1958 p = 1 := by simpa only [d1963, d554, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10328 p hg
    simpa only [d1963, d554, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1962 p = 1 := by simpa only [d1963, d554, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10332 p hg
    simpa only [d1963, d554, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10334 (p : Pattern) (guard : d1956 p = 1) : d539 p ≤ (0 : Int) + d138 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1951 p = 1 := by simpa only [d1956, d539, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9566 p hg
    simpa only [d1956, d539, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1956, d539, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1956, d539, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10335 (p : Pattern) (guard : d1957 p = 1) : d539 p ≤ (0 : Int) + d138 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1952 p = 1 := by simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10307 p hg
    simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1956 p = 1 := by simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10334 p hg
    simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10336 (p : Pattern) (guard : d1956 p = 1) : d539 p ≤ (0 : Int) + d2 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1951 p = 1 := by simpa only [d1956, d539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9569 p hg
    simpa only [d1956, d539, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1956, d539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1956, d539, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10337 (p : Pattern) (guard : d0 p = 1) : d540 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10338 (p : Pattern) (guard : d1961 p = 1) : d541 p ≤ (0 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1956 p = 1 := by simpa only [d1961, d541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10336 p hg
    simpa only [d1961, d541, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1961, d541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10337 p hg
    simpa only [d1961, d541, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10339 (p : Pattern) (guard : d1962 p = 1) : d543 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1957 p = 1 := by simpa only [d1962, d543, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10335 p hg
    simpa only [d1962, d543, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1961 p = 1 := by simpa only [d1962, d543, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10338 p hg
    simpa only [d1962, d543, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10340 (p : Pattern) (guard : d0 p = 1) : d545 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10341 (p : Pattern) (guard : d1961 p = 1) : d545 p ≤ (0 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1956 p = 1 := by simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10313 p hg
    simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10340 p hg
    simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10342 (p : Pattern) (guard : d0 p = 1) : d547 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10343 (p : Pattern) (guard : d1966 p = 1) : d548 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10341 p hg
    simpa only [d1966, d548, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10342 p hg
    simpa only [d1966, d548, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10344 (p : Pattern) (guard : d1967 p = 1) : d549 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1962 p = 1 := by simpa only [d1967, d549, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10339 p hg
    simpa only [d1967, d549, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1966 p = 1 := by simpa only [d1967, d549, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10343 p hg
    simpa only [d1967, d549, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10345 (p : Pattern) (guard : d1968 p = 1) : d555 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1963 p = 1 := by simpa only [d1968, d555, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10333 p hg
    simpa only [d1968, d555, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1967 p = 1 := by simpa only [d1968, d555, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10344 p hg
    simpa only [d1968, d555, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10346 (p : Pattern) (guard : d1969 p = 1) : d556 p ≤ (0 : Int) + d141 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1964 p = 1 := by simpa only [d1969, d556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10324 p hg
    simpa only [d1969, d556, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1968 p = 1 := by simpa only [d1969, d556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10345 p hg
    simpa only [d1969, d556, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10347 (p : Pattern) (guard : d1970 p = 1) : d556 p ≤ (0 : Int) + d141 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1965 p = 1 := by simpa only [d1970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10320 p hg
    simpa only [d1970, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1969 p = 1 := by simpa only [d1970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10346 p hg
    simpa only [d1970, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10348 (p : Pattern) (guard : d1948 p = 1) : d540 p ≤ (0 : Int) + d138 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1944 p = 1 := by simpa only [d1948, d540, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9578 p hg
    simpa only [d1948, d540, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1947 p = 1 := by simpa only [d1948, d540, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10274 p hg
    simpa only [d1948, d540, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10349 (p : Pattern) (guard : d1949 p = 1) : d541 p ≤ (0 : Int) + d138 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1945 p = 1 := by simpa only [d1949, d541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10285 p hg
    simpa only [d1949, d541, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1948 p = 1 := by simpa only [d1949, d541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10348 p hg
    simpa only [d1949, d541, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10350 (p : Pattern) (guard : d1954 p = 1) : d541 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1949 p = 1 := by simpa only [d1954, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10349 p hg
    simpa only [d1954, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1953 p = 1 := by simpa only [d1954, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10282 p hg
    simpa only [d1954, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10351 (p : Pattern) (guard : d1958 p = 1) : d541 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1953 p = 1 := by simpa only [d1958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10282 p hg
    simpa only [d1958, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1957 p = 1 := by simpa only [d1958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10311 p hg
    simpa only [d1958, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10352 (p : Pattern) (guard : d1959 p = 1) : d541 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1954 p = 1 := by simpa only [d1959, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10350 p hg
    simpa only [d1959, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1958 p = 1 := by simpa only [d1959, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10351 p hg
    simpa only [d1959, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10353 (p : Pattern) (guard : d1962 p = 1) : d547 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1957 p = 1 := by simpa only [d1962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10293 p hg
    simpa only [d1962, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1961 p = 1 := by simpa only [d1962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10316 p hg
    simpa only [d1962, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10354 (p : Pattern) (guard : d1963 p = 1) : d557 p ≤ (0 : Int) + d2 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1958 p = 1 := by simpa only [d1963, d557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10351 p hg
    simpa only [d1963, d557, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1962 p = 1 := by simpa only [d1963, d557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10353 p hg
    simpa only [d1963, d557, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10355 (p : Pattern) (guard : d1964 p = 1) : d558 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1959 p = 1 := by simpa only [d1964, d558, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10352 p hg
    simpa only [d1964, d558, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1963 p = 1 := by simpa only [d1964, d558, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10354 p hg
    simpa only [d1964, d558, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10356 (p : Pattern) (guard : d1952 p = 1) : d540 p ≤ (0 : Int) + d138 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1947 p = 1 := by simpa only [d1952, d540, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9587 p hg
    simpa only [d1952, d540, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1951 p = 1 := by simpa only [d1952, d540, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10280 p hg
    simpa only [d1952, d540, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10357 (p : Pattern) (guard : d1953 p = 1) : d541 p ≤ (0 : Int) + d138 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1948 p = 1 := by simpa only [d1953, d541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10286 p hg
    simpa only [d1953, d541, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1952 p = 1 := by simpa only [d1953, d541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10356 p hg
    simpa only [d1953, d541, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10358 (p : Pattern) (guard : d1958 p = 1) : d541 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1953 p = 1 := by simpa only [d1958, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10357 p hg
    simpa only [d1958, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1957 p = 1 := by simpa only [d1958, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10311 p hg
    simpa only [d1958, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10359 (p : Pattern) (guard : d1962 p = 1) : d552 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1957 p = 1 := by simpa only [d1962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10304 p hg
    simpa only [d1962, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1961 p = 1 := by simpa only [d1962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10331 p hg
    simpa only [d1962, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban32Refined
