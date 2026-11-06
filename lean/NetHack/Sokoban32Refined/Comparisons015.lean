/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Comparisons014
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare2100 (p : Pattern) (guard : d0 p = 1) : d154 p ≤ (0 : Int) + d426 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2101 (p : Pattern) (guard : d1125 p = 1) : d236 p ≤ (0 : Int) + d426 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d1125, d236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2099 p hg
    simpa only [d1125, d236, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1125, d236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2100 p hg
    simpa only [d1125, d236, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2102 (p : Pattern) (guard : d1126 p = 1) : d237 p ≤ (0 : Int) + d427 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1122 p = 1 := by simpa only [d1126, d237, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2088 p hg
    simpa only [d1126, d237, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1125 p = 1 := by simpa only [d1126, d237, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2101 p hg
    simpa only [d1126, d237, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2103 (p : Pattern) (guard : d0 p = 1) : d161 p ≤ (0 : Int) + d416 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2104 (p : Pattern) (guard : d1122 p = 1) : d238 p ≤ (0 : Int) + d416 p := by
  cases selected : p 113 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d1122, d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1463 p hg
    simpa only [d1122, d238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1122, d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2103 p hg
    simpa only [d1122, d238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2105 (p : Pattern) (guard : d1092 p = 1) : d2 p ≤ (0 : Int) + d2 p := by
  omega
theorem compare2106 (p : Pattern) (guard : d1092 p = 1) : d107 p ≤ (0 : Int) + d428 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d107, d428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2093 p hg
    simpa only [d107, d428, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d107, d428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2105 p hg
    simpa only [d107, d428, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2107 (p : Pattern) (guard : d1092 p = 1) : d108 p ≤ (0 : Int) + d429 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d108, d429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2094 p hg
    simpa only [d108, d429, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d108, d429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2106 p hg
    simpa only [d108, d429, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2108 (p : Pattern) (guard : d0 p = 1) : d163 p ≤ (0 : Int) + d434 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2109 (p : Pattern) (guard : d1125 p = 1) : d239 p ≤ (0 : Int) + d435 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d1125, d239, d435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2107 p hg
    simpa only [d1125, d239, d435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1125, d239, d435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2108 p hg
    simpa only [d1125, d239, d435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2110 (p : Pattern) (guard : d1126 p = 1) : d240 p ≤ (0 : Int) + d436 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1122 p = 1 := by simpa only [d1126, d240, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2104 p hg
    simpa only [d1126, d240, d436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1125 p = 1 := by simpa only [d1126, d240, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2109 p hg
    simpa only [d1126, d240, d436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2111 (p : Pattern) (guard : d1126 p = 1) : d241 p ≤ (0 : Int) + d437 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1126 p = 1 := by simpa only [d241, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2102 p hg
    simpa only [d241, d437, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1126 p = 1 := by simpa only [d241, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2110 p hg
    simpa only [d241, d437, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2112 (p : Pattern) (guard : d1126 p = 1) : d242 p ≤ (0 : Int) + d438 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1126 p = 1 := by simpa only [d242, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2086 p hg
    simpa only [d242, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1126 p = 1 := by simpa only [d242, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2111 p hg
    simpa only [d242, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2113 (p : Pattern) (guard : d0 p = 1) : d154 p ≤ (0 : Int) + d408 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2114 (p : Pattern) (guard : d1125 p = 1) : d243 p ≤ (0 : Int) + d408 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d1125, d243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2073 p hg
    simpa only [d1125, d243, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1125, d243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2113 p hg
    simpa only [d1125, d243, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2115 (p : Pattern) (guard : d1126 p = 1) : d244 p ≤ (0 : Int) + d409 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1122 p = 1 := by simpa only [d1126, d244, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2088 p hg
    simpa only [d1126, d244, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1125 p = 1 := by simpa only [d1126, d244, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2114 p hg
    simpa only [d1126, d244, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2116 (p : Pattern) (guard : d0 p = 1) : d163 p ≤ (0 : Int) + d419 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2117 (p : Pattern) (guard : d1125 p = 1) : d245 p ≤ (0 : Int) + d419 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d1125, d245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2082 p hg
    simpa only [d1125, d245, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1125, d245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2116 p hg
    simpa only [d1125, d245, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2118 (p : Pattern) (guard : d1126 p = 1) : d246 p ≤ (0 : Int) + d439 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1122 p = 1 := by simpa only [d1126, d246, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2104 p hg
    simpa only [d1126, d246, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1125 p = 1 := by simpa only [d1126, d246, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2117 p hg
    simpa only [d1126, d246, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2119 (p : Pattern) (guard : d1126 p = 1) : d247 p ≤ (0 : Int) + d440 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1126 p = 1 := by simpa only [d247, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2115 p hg
    simpa only [d247, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1126 p = 1 := by simpa only [d247, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2118 p hg
    simpa only [d247, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2120 (p : Pattern) (guard : d0 p = 1) : d161 p ≤ (0 : Int) + d444 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2121 (p : Pattern) (guard : d1122 p = 1) : d248 p ≤ (0 : Int) + d445 p := by
  cases selected : p 113 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d1122, d248, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1447 p hg
    simpa only [d1122, d248, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1122, d248, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2120 p hg
    simpa only [d1122, d248, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2122 (p : Pattern) (guard : d0 p = 1) : d163 p ≤ (0 : Int) + d447 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2123 (p : Pattern) (guard : d1125 p = 1) : d249 p ≤ (0 : Int) + d448 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d1125, d249, d448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2099 p hg
    simpa only [d1125, d249, d448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1125, d249, d448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2122 p hg
    simpa only [d1125, d249, d448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2124 (p : Pattern) (guard : d1126 p = 1) : d250 p ≤ (0 : Int) + d449 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1122 p = 1 := by simpa only [d1126, d250, d449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2121 p hg
    simpa only [d1126, d250, d449, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1125 p = 1 := by simpa only [d1126, d250, d449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2123 p hg
    simpa only [d1126, d250, d449, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2125 (p : Pattern) (guard : d0 p = 1) : d167 p ≤ (0 : Int) + d419 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2126 (p : Pattern) (guard : d1122 p = 1) : d251 p ≤ (0 : Int) + d450 p := by
  cases selected : p 113 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d1122, d251, d450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1463 p hg
    simpa only [d1122, d251, d450, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1122, d251, d450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2125 p hg
    simpa only [d1122, d251, d450, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2127 (p : Pattern) (guard : d1092 p = 1) : d97 p ≤ (0 : Int) + d430 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1092, d430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1818 p hg
    simpa only [d1092, d430, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare919 p hg
    simpa only [d1092, d430, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2128 (p : Pattern) (guard : d1092 p = 1) : d109 p ≤ (0 : Int) + d431 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d109, d431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2127 p hg
    simpa only [d109, d431, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d109, d431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2079 p hg
    simpa only [d109, d431, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2129 (p : Pattern) (guard : d1092 p = 1) : d110 p ≤ (0 : Int) + d432 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d110, d432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2127 p hg
    simpa only [d110, d432, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d110, d432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2128 p hg
    simpa only [d110, d432, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2130 (p : Pattern) (guard : d1092 p = 1) : d111 p ≤ (0 : Int) + d433 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d111, d433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2128 p hg
    simpa only [d111, d433, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d111, d433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2105 p hg
    simpa only [d111, d433, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2131 (p : Pattern) (guard : d1092 p = 1) : d112 p ≤ (0 : Int) + d434 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d112, d434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2129 p hg
    simpa only [d112, d434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d112, d434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2130 p hg
    simpa only [d112, d434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2132 (p : Pattern) (guard : d1125 p = 1) : d130 p ≤ (0 : Int) + d451 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d1125, d130, d451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2131 p hg
    simpa only [d1125, d130, d451, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1125, d130, d451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1125, d130, d451, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2133 (p : Pattern) (guard : d1126 p = 1) : d252 p ≤ (0 : Int) + d452 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1122 p = 1 := by simpa only [d1126, d252, d452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2126 p hg
    simpa only [d1126, d252, d452, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1125 p = 1 := by simpa only [d1126, d252, d452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2132 p hg
    simpa only [d1126, d252, d452, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2134 (p : Pattern) (guard : d1126 p = 1) : d253 p ≤ (0 : Int) + d453 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1126 p = 1 := by simpa only [d253, d453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2124 p hg
    simpa only [d253, d453, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1126 p = 1 := by simpa only [d253, d453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2133 p hg
    simpa only [d253, d453, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2135 (p : Pattern) (guard : d1126 p = 1) : d254 p ≤ (0 : Int) + d454 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1126 p = 1 := by simpa only [d254, d454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2119 p hg
    simpa only [d254, d454, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1126 p = 1 := by simpa only [d254, d454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2134 p hg
    simpa only [d254, d454, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2136 (p : Pattern) (guard : d1126 p = 1) : d255 p ≤ (0 : Int) + d455 p := by
  cases selected : p 80 with
  | false =>
    have hg : d1126 p = 1 := by simpa only [d255, d455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2112 p hg
    simpa only [d255, d455, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1126 p = 1 := by simpa only [d255, d455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2135 p hg
    simpa only [d255, d455, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2137 (p : Pattern) (guard : d865 p = 1) : d45 p ≤ (0 : Int) + d51 p := by
  cases selected : p 113 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare436 p hg
    simpa only [d865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare240 p hg
    simpa only [d865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2138 (p : Pattern) (guard : d0 p = 1) : d66 p ≤ (0 : Int) + d51 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2139 (p : Pattern) (guard : d1073 p = 1) : d67 p ≤ (0 : Int) + d51 p := by
  cases selected : p 112 with
  | false =>
    have hg : d865 p = 1 := by simpa only [d1073, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2137 p hg
    simpa only [d1073, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1073, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2138 p hg
    simpa only [d1073, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2140 (p : Pattern) (guard : d0 p = 1) : d74 p ≤ (0 : Int) + d80 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2141 (p : Pattern) (guard : d865 p = 1) : d78 p ≤ (0 : Int) + d80 p := by
  cases selected : p 113 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d865, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2140 p hg
    simpa only [d865, d78, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d865, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare260 p hg
    simpa only [d865, d78, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2142 (p : Pattern) (guard : d0 p = 1) : d83 p ≤ (0 : Int) + d80 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2143 (p : Pattern) (guard : d1073 p = 1) : d84 p ≤ (0 : Int) + d80 p := by
  cases selected : p 112 with
  | false =>
    have hg : d865 p = 1 := by simpa only [d1073, d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2141 p hg
    simpa only [d1073, d84, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1073, d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2142 p hg
    simpa only [d1073, d84, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2144 (p : Pattern) (guard : d1073 p = 1) : d85 p ≤ (0 : Int) + d860 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1073 p = 1 := by simpa only [d85, d860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2139 p hg
    simpa only [d85, d860, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1073 p = 1 := by simpa only [d85, d860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2143 p hg
    simpa only [d85, d860, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2145 (p : Pattern) (guard : d0 p = 1) : d45 p ≤ (0 : Int) + d102 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2146 (p : Pattern) (guard : d1 p = 1) : d52 p ≤ (0 : Int) + d97 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d52, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare207 p hg
    simpa only [d52, d97, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d52, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare201 p hg
    simpa only [d52, d97, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2147 (p : Pattern) (guard : d1 p = 1) : d86 p ≤ (0 : Int) + d98 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d86, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare207 p hg
    simpa only [d86, d98, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d86, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2146 p hg
    simpa only [d86, d98, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2148 (p : Pattern) (guard : d1 p = 1) : d54 p ≤ (0 : Int) + d70 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d54, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare215 p hg
    simpa only [d54, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d54, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare201 p hg
    simpa only [d54, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2149 (p : Pattern) (guard : d1 p = 1) : d87 p ≤ (0 : Int) + d71 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d87, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare215 p hg
    simpa only [d87, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d87, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2148 p hg
    simpa only [d87, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2150 (p : Pattern) (guard : d1 p = 1) : d88 p ≤ (0 : Int) + d99 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d88, d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2147 p hg
    simpa only [d88, d99, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d88, d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2149 p hg
    simpa only [d88, d99, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2151 (p : Pattern) (guard : d1 p = 1) : d89 p ≤ (0 : Int) + d100 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d89, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2147 p hg
    simpa only [d89, d100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d89, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2150 p hg
    simpa only [d89, d100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2152 (p : Pattern) (guard : d1 p = 1) : d58 p ≤ (0 : Int) + d70 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d58, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare227 p hg
    simpa only [d58, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d58, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare201 p hg
    simpa only [d58, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2153 (p : Pattern) (guard : d1 p = 1) : d90 p ≤ (0 : Int) + d71 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d90, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare227 p hg
    simpa only [d90, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d90, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2152 p hg
    simpa only [d90, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2154 (p : Pattern) (guard : d1 p = 1) : d91 p ≤ (0 : Int) + d99 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d91, d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2147 p hg
    simpa only [d91, d99, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d91, d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2153 p hg
    simpa only [d91, d99, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2155 (p : Pattern) (guard : d1 p = 1) : d61 p ≤ (0 : Int) + d68 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d61, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare234 p hg
    simpa only [d61, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d61, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare201 p hg
    simpa only [d61, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2156 (p : Pattern) (guard : d1 p = 1) : d92 p ≤ (0 : Int) + d69 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d92, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare234 p hg
    simpa only [d92, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d92, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2155 p hg
    simpa only [d92, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2157 (p : Pattern) (guard : d1 p = 1) : d93 p ≤ (0 : Int) + d72 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d93, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2156 p hg
    simpa only [d93, d72, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d93, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2149 p hg
    simpa only [d93, d72, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2158 (p : Pattern) (guard : d1 p = 1) : d94 p ≤ (0 : Int) + d101 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d94, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2154 p hg
    simpa only [d94, d101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d94, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2157 p hg
    simpa only [d94, d101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2159 (p : Pattern) (guard : d1 p = 1) : d95 p ≤ (0 : Int) + d102 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d95, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2151 p hg
    simpa only [d95, d102, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d95, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2158 p hg
    simpa only [d95, d102, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2160 (p : Pattern) (guard : d865 p = 1) : d96 p ≤ (0 : Int) + d102 p := by
  cases selected : p 113 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d865, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2145 p hg
    simpa only [d865, d96, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d865, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2159 p hg
    simpa only [d865, d96, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2161 (p : Pattern) (guard : d0 p = 1) : d102 p ≤ (0 : Int) + d102 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2162 (p : Pattern) (guard : d1073 p = 1) : d103 p ≤ (0 : Int) + d102 p := by
  cases selected : p 112 with
  | false =>
    have hg : d865 p = 1 := by simpa only [d1073, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2160 p hg
    simpa only [d1073, d103, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1073, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2161 p hg
    simpa only [d1073, d103, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2163 (p : Pattern) (guard : d0 p = 1) : d77 p ≤ (0 : Int) + d108 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2164 (p : Pattern) (guard : d1 p = 1) : d10 p ≤ (0 : Int) + d2 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare222 p hg
    simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare677 p hg
    simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2165 (p : Pattern) (guard : d1 p = 1) : d12 p ≤ (0 : Int) + d2 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2164 p hg
    simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare666 p hg
    simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2166 (p : Pattern) (guard : d1 p = 1) : d39 p ≤ (0 : Int) + d2 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare666 p hg
    simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare201 p hg
    simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2167 (p : Pattern) (guard : d1 p = 1) : d40 p ≤ (0 : Int) + d2 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2165 p hg
    simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2166 p hg
    simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2168 (p : Pattern) (guard : d1 p = 1) : d68 p ≤ (0 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2167 p hg
    simpa only [d68, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare201 p hg
    simpa only [d68, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2169 (p : Pattern) (guard : d1 p = 1) : d22 p ≤ (0 : Int) + d2 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2164 p hg
    simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2170 (p : Pattern) (guard : d1 p = 1) : d23 p ≤ (0 : Int) + d2 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare201 p hg
    simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2171 (p : Pattern) (guard : d1 p = 1) : d24 p ≤ (0 : Int) + d2 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2169 p hg
    simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2170 p hg
    simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2172 (p : Pattern) (guard : d1 p = 1) : d70 p ≤ (0 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2171 p hg
    simpa only [d70, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare201 p hg
    simpa only [d70, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2173 (p : Pattern) (guard : d1 p = 1) : d75 p ≤ (0 : Int) + d2 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2168 p hg
    simpa only [d75, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2172 p hg
    simpa only [d75, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2174 (p : Pattern) (guard : d1 p = 1) : d104 p ≤ (0 : Int) + d107 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d104, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2150 p hg
    simpa only [d104, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d104, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2173 p hg
    simpa only [d104, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2175 (p : Pattern) (guard : d1 p = 1) : d105 p ≤ (0 : Int) + d108 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d105, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2151 p hg
    simpa only [d105, d108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d105, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2174 p hg
    simpa only [d105, d108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2176 (p : Pattern) (guard : d865 p = 1) : d106 p ≤ (0 : Int) + d108 p := by
  cases selected : p 113 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d865, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2163 p hg
    simpa only [d865, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d865, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2175 p hg
    simpa only [d865, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2177 (p : Pattern) (guard : d0 p = 1) : d113 p ≤ (0 : Int) + d108 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2178 (p : Pattern) (guard : d1073 p = 1) : d114 p ≤ (0 : Int) + d108 p := by
  cases selected : p 112 with
  | false =>
    have hg : d865 p = 1 := by simpa only [d1073, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2176 p hg
    simpa only [d1073, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1073, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2177 p hg
    simpa only [d1073, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2179 (p : Pattern) (guard : d1073 p = 1) : d115 p ≤ (0 : Int) + d1127 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1073 p = 1 := by simpa only [d115, d1127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2162 p hg
    simpa only [d115, d1127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1073 p = 1 := by simpa only [d115, d1127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2178 p hg
    simpa only [d115, d1127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2180 (p : Pattern) (guard : d1073 p = 1) : d116 p ≤ (0 : Int) + d1128 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1073 p = 1 := by simpa only [d116, d1128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2144 p hg
    simpa only [d116, d1128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1073 p = 1 := by simpa only [d116, d1128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2179 p hg
    simpa only [d116, d1128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2181 (p : Pattern) (guard : d865 p = 1) : d77 p ≤ (0 : Int) + d80 p := by
  cases selected : p 113 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare464 p hg
    simpa only [d865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare260 p hg
    simpa only [d865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2182 (p : Pattern) (guard : d1073 p = 1) : d117 p ≤ (0 : Int) + d80 p := by
  cases selected : p 112 with
  | false =>
    have hg : d865 p = 1 := by simpa only [d1073, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2181 p hg
    simpa only [d1073, d117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1073, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2142 p hg
    simpa only [d1073, d117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2183 (p : Pattern) (guard : d1073 p = 1) : d118 p ≤ (0 : Int) + d860 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1073 p = 1 := by simpa only [d118, d860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2139 p hg
    simpa only [d118, d860, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1073 p = 1 := by simpa only [d118, d860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2182 p hg
    simpa only [d118, d860, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2184 (p : Pattern) (guard : d1 p = 1) : d119 p ≤ (0 : Int) + d24 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare227 p hg
    simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare215 p hg
    simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2185 (p : Pattern) (guard : d1 p = 1) : d120 p ≤ (0 : Int) + d71 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d120, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2184 p hg
    simpa only [d120, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d120, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2152 p hg
    simpa only [d120, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2186 (p : Pattern) (guard : d1 p = 1) : d121 p ≤ (0 : Int) + d99 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d121, d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2147 p hg
    simpa only [d121, d99, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d121, d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2185 p hg
    simpa only [d121, d99, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2187 (p : Pattern) (guard : d1 p = 1) : d122 p ≤ (0 : Int) + d101 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d122, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2186 p hg
    simpa only [d122, d101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d122, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2157 p hg
    simpa only [d122, d101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2188 (p : Pattern) (guard : d1 p = 1) : d123 p ≤ (0 : Int) + d102 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d123, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2151 p hg
    simpa only [d123, d102, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d123, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2187 p hg
    simpa only [d123, d102, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2189 (p : Pattern) (guard : d865 p = 1) : d124 p ≤ (0 : Int) + d102 p := by
  cases selected : p 113 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d865, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2145 p hg
    simpa only [d865, d124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d865, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2188 p hg
    simpa only [d865, d124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2190 (p : Pattern) (guard : d0 p = 1) : d127 p ≤ (0 : Int) + d102 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2191 (p : Pattern) (guard : d1073 p = 1) : d128 p ≤ (0 : Int) + d102 p := by
  cases selected : p 112 with
  | false =>
    have hg : d865 p = 1 := by simpa only [d1073, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2189 p hg
    simpa only [d1073, d128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1073, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2190 p hg
    simpa only [d1073, d128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2192 (p : Pattern) (guard : d0 p = 1) : d77 p ≤ (0 : Int) + d112 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2193 (p : Pattern) (guard : d1 p = 1) : d13 p ≤ (0 : Int) + d2 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2164 p hg
    simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare201 p hg
    simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2194 (p : Pattern) (guard : d1 p = 1) : d14 p ≤ (0 : Int) + d2 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2165 p hg
    simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2193 p hg
    simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2195 (p : Pattern) (guard : d1 p = 1) : d15 p ≤ (0 : Int) + d97 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d15, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare207 p hg
    simpa only [d15, d97, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d15, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2194 p hg
    simpa only [d15, d97, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2196 (p : Pattern) (guard : d1 p = 1) : d53 p ≤ (0 : Int) + d97 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2195 p hg
    simpa only [d53, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2146 p hg
    simpa only [d53, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2197 (p : Pattern) (guard : d1 p = 1) : d25 p ≤ (0 : Int) + d70 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d25, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare215 p hg
    simpa only [d25, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d25, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2171 p hg
    simpa only [d25, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2198 (p : Pattern) (guard : d1 p = 1) : d55 p ≤ (0 : Int) + d70 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2197 p hg
    simpa only [d55, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2148 p hg
    simpa only [d55, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2199 (p : Pattern) (guard : d1 p = 1) : d56 p ≤ (0 : Int) + d109 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d56, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2196 p hg
    simpa only [d56, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d56, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2198 p hg
    simpa only [d56, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2200 (p : Pattern) (guard : d1 p = 1) : d57 p ≤ (0 : Int) + d110 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d57, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2196 p hg
    simpa only [d57, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d57, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2199 p hg
    simpa only [d57, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2201 (p : Pattern) (guard : d1 p = 1) : d81 p ≤ (0 : Int) + d111 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d81, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2199 p hg
    simpa only [d81, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d81, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2173 p hg
    simpa only [d81, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2202 (p : Pattern) (guard : d1 p = 1) : d82 p ≤ (0 : Int) + d112 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d82, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2200 p hg
    simpa only [d82, d112, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d82, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2201 p hg
    simpa only [d82, d112, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2203 (p : Pattern) (guard : d865 p = 1) : d129 p ≤ (0 : Int) + d112 p := by
  cases selected : p 113 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d865, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2192 p hg
    simpa only [d865, d129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d865, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2202 p hg
    simpa only [d865, d129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2204 (p : Pattern) (guard : d0 p = 1) : d130 p ≤ (0 : Int) + d112 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2205 (p : Pattern) (guard : d1073 p = 1) : d131 p ≤ (0 : Int) + d112 p := by
  cases selected : p 112 with
  | false =>
    have hg : d865 p = 1 := by simpa only [d1073, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2203 p hg
    simpa only [d1073, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1073, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2204 p hg
    simpa only [d1073, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2206 (p : Pattern) (guard : d1073 p = 1) : d132 p ≤ (0 : Int) + d1129 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1073 p = 1 := by simpa only [d132, d1129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2191 p hg
    simpa only [d132, d1129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1073 p = 1 := by simpa only [d132, d1129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2205 p hg
    simpa only [d132, d1129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2207 (p : Pattern) (guard : d1073 p = 1) : d133 p ≤ (0 : Int) + d1130 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1073 p = 1 := by simpa only [d133, d1130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2183 p hg
    simpa only [d133, d1130, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1073 p = 1 := by simpa only [d133, d1130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2206 p hg
    simpa only [d133, d1130, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2208 (p : Pattern) (guard : d1073 p = 1) : d134 p ≤ (0 : Int) + d1131 p := by
  cases selected : p 80 with
  | false =>
    have hg : d1073 p = 1 := by simpa only [d134, d1131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2180 p hg
    simpa only [d134, d1131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1073 p = 1 := by simpa only [d134, d1131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2207 p hg
    simpa only [d134, d1131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2209 (p : Pattern) (guard : d0 p = 1) : d45 p ≤ (0 : Int) + d468 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2210 (p : Pattern) (guard : d1095 p = 1) : d45 p ≤ (0 : Int) + d468 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1609 p hg
    simpa only [d1095, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2209 p hg
    simpa only [d1095, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2211 (p : Pattern) (guard : d0 p = 1) : d65 p ≤ (0 : Int) + d475 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2212 (p : Pattern) (guard : d1095 p = 1) : d66 p ≤ (0 : Int) + d475 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1095, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1802 p hg
    simpa only [d1095, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1095, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2211 p hg
    simpa only [d1095, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2213 (p : Pattern) (guard : d1095 p = 1) : d67 p ≤ (0 : Int) + d476 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1095 p = 1 := by simpa only [d67, d476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2210 p hg
    simpa only [d67, d476, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1095 p = 1 := by simpa only [d67, d476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2212 p hg
    simpa only [d67, d476, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2214 (p : Pattern) (guard : d0 p = 1) : d77 p ≤ (0 : Int) + d487 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2215 (p : Pattern) (guard : d1095 p = 1) : d78 p ≤ (0 : Int) + d488 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1095, d78, d488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1640 p hg
    simpa only [d1095, d78, d488, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1095, d78, d488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2214 p hg
    simpa only [d1095, d78, d488, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2216 (p : Pattern) (guard : d0 p = 1) : d82 p ≤ (0 : Int) + d492 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2217 (p : Pattern) (guard : d1095 p = 1) : d83 p ≤ (0 : Int) + d493 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1095, d83, d493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1809 p hg
    simpa only [d1095, d83, d493, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1095, d83, d493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2216 p hg
    simpa only [d1095, d83, d493, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2218 (p : Pattern) (guard : d1095 p = 1) : d84 p ≤ (0 : Int) + d494 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1095 p = 1 := by simpa only [d84, d494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2215 p hg
    simpa only [d84, d494, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1095 p = 1 := by simpa only [d84, d494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2217 p hg
    simpa only [d84, d494, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2219 (p : Pattern) (guard : d1095 p = 1) : d85 p ≤ (0 : Int) + d495 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1095 p = 1 := by simpa only [d85, d495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2213 p hg
    simpa only [d85, d495, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1095 p = 1 := by simpa only [d85, d495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2218 p hg
    simpa only [d85, d495, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2220 (p : Pattern) (guard : d0 p = 1) : d95 p ≤ (0 : Int) + d498 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2221 (p : Pattern) (guard : d1095 p = 1) : d96 p ≤ (0 : Int) + d499 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1095, d96, d499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1609 p hg
    simpa only [d1095, d96, d499, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1095, d96, d499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2220 p hg
    simpa only [d1095, d96, d499, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2222 (p : Pattern) (guard : d0 p = 1) : d102 p ≤ (0 : Int) + d507 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2223 (p : Pattern) (guard : d1095 p = 1) : d102 p ≤ (0 : Int) + d508 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1095, d508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1830 p hg
    simpa only [d1095, d508, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1095, d508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2222 p hg
    simpa only [d1095, d508, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2224 (p : Pattern) (guard : d1095 p = 1) : d103 p ≤ (0 : Int) + d509 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1095 p = 1 := by simpa only [d103, d509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2221 p hg
    simpa only [d103, d509, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1095 p = 1 := by simpa only [d103, d509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2223 p hg
    simpa only [d103, d509, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2225 (p : Pattern) (guard : d0 p = 1) : d105 p ≤ (0 : Int) + d512 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2226 (p : Pattern) (guard : d1095 p = 1) : d106 p ≤ (0 : Int) + d513 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1095, d106, d513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1679 p hg
    simpa only [d1095, d106, d513, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1095, d106, d513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2225 p hg
    simpa only [d1095, d106, d513, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2227 (p : Pattern) (guard : d0 p = 1) : d112 p ≤ (0 : Int) + d112 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2228 (p : Pattern) (guard : d1095 p = 1) : d113 p ≤ (0 : Int) + d515 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1095, d113, d515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1838 p hg
    simpa only [d1095, d113, d515, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1095, d113, d515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2227 p hg
    simpa only [d1095, d113, d515, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2229 (p : Pattern) (guard : d1095 p = 1) : d114 p ≤ (0 : Int) + d516 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1095 p = 1 := by simpa only [d114, d516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2226 p hg
    simpa only [d114, d516, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1095 p = 1 := by simpa only [d114, d516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2228 p hg
    simpa only [d114, d516, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2230 (p : Pattern) (guard : d1095 p = 1) : d115 p ≤ (0 : Int) + d517 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1095 p = 1 := by simpa only [d115, d517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2224 p hg
    simpa only [d115, d517, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1095 p = 1 := by simpa only [d115, d517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2229 p hg
    simpa only [d115, d517, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2231 (p : Pattern) (guard : d1095 p = 1) : d116 p ≤ (0 : Int) + d518 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1095 p = 1 := by simpa only [d116, d518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2219 p hg
    simpa only [d116, d518, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1095 p = 1 := by simpa only [d116, d518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2230 p hg
    simpa only [d116, d518, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2232 (p : Pattern) (guard : d0 p = 1) : d45 p ≤ (0 : Int) + d498 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2233 (p : Pattern) (guard : d1095 p = 1) : d45 p ≤ (0 : Int) + d499 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1095, d499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1609 p hg
    simpa only [d1095, d499, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1095, d499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2232 p hg
    simpa only [d1095, d499, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2234 (p : Pattern) (guard : d0 p = 1) : d65 p ≤ (0 : Int) + d521 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2235 (p : Pattern) (guard : d1095 p = 1) : d66 p ≤ (0 : Int) + d522 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1095, d66, d522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1802 p hg
    simpa only [d1095, d66, d522, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1095, d66, d522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2234 p hg
    simpa only [d1095, d66, d522, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2236 (p : Pattern) (guard : d1095 p = 1) : d67 p ≤ (0 : Int) + d523 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1095 p = 1 := by simpa only [d67, d523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2233 p hg
    simpa only [d67, d523, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1095 p = 1 := by simpa only [d67, d523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2235 p hg
    simpa only [d67, d523, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2237 (p : Pattern) (guard : d0 p = 1) : d77 p ≤ (0 : Int) + d512 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2238 (p : Pattern) (guard : d1095 p = 1) : d77 p ≤ (0 : Int) + d513 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1095, d513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1679 p hg
    simpa only [d1095, d513, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1095, d513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2237 p hg
    simpa only [d1095, d513, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2239 (p : Pattern) (guard : d0 p = 1) : d82 p ≤ (0 : Int) + d525 p := by
  change (0 : Int) = 1 at guard
  omega
end NetHack.Sokoban32Refined
