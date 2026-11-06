/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons014
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare2100 (p : Pattern) (guard : d1 p = 1) : d294 p ≤ (0 : Int) + d276 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d294, d276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2095 p hg
    simpa only [d294, d276, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d294, d276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2099 p hg
    simpa only [d294, d276, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2101 (p : Pattern) (guard : d1 p = 1) : d278 p ≤ (0 : Int) + d278 p := by
  omega
theorem compare2102 (p : Pattern) (guard : d1 p = 1) : d295 p ≤ (0 : Int) + d279 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d295, d279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2099 p hg
    simpa only [d295, d279, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d295, d279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2101 p hg
    simpa only [d295, d279, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2103 (p : Pattern) (guard : d1 p = 1) : d296 p ≤ (0 : Int) + d280 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d296, d280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2100 p hg
    simpa only [d296, d280, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d296, d280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2102 p hg
    simpa only [d296, d280, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2104 (p : Pattern) (guard : d0 p = 1) : d151 p ≤ (0 : Int) + d280 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2105 (p : Pattern) (guard : d4117 p = 1) : d297 p ≤ (0 : Int) + d280 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2103 p hg
    simpa only [d4117, d297, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2104 p hg
    simpa only [d4117, d297, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2106 (p : Pattern) (guard : d1 p = 1) : d282 p ≤ (0 : Int) + d282 p := by
  omega
theorem compare2107 (p : Pattern) (guard : d1 p = 1) : d298 p ≤ (0 : Int) + d283 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d298, d283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2106 p hg
    simpa only [d298, d283, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d298, d283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1322 p hg
    simpa only [d298, d283, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2108 (p : Pattern) (guard : d1 p = 1) : d299 p ≤ (0 : Int) + d284 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d299, d284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1343 p hg
    simpa only [d299, d284, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d299, d284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2107 p hg
    simpa only [d299, d284, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2109 (p : Pattern) (guard : d1 p = 1) : d300 p ≤ (0 : Int) + d285 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d300, d285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2098 p hg
    simpa only [d300, d285, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d300, d285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d300, d285, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2110 (p : Pattern) (guard : d1 p = 1) : d301 p ≤ (0 : Int) + d286 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d301, d286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2108 p hg
    simpa only [d301, d286, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d301, d286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2109 p hg
    simpa only [d301, d286, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2111 (p : Pattern) (guard : d1 p = 1) : d302 p ≤ (0 : Int) + d287 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d302, d287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2109 p hg
    simpa only [d302, d287, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d302, d287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d302, d287, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2112 (p : Pattern) (guard : d1 p = 1) : d303 p ≤ (0 : Int) + d288 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d303, d288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2110 p hg
    simpa only [d303, d288, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d303, d288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2111 p hg
    simpa only [d303, d288, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2113 (p : Pattern) (guard : d0 p = 1) : d155 p ≤ (0 : Int) + d288 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2114 (p : Pattern) (guard : d4117 p = 1) : d304 p ≤ (0 : Int) + d288 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2112 p hg
    simpa only [d4117, d304, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2113 p hg
    simpa only [d4117, d304, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2115 (p : Pattern) (guard : d4117 p = 1) : d305 p ≤ (0 : Int) + d4135 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d305, d4135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2105 p hg
    simpa only [d305, d4135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d305, d4135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2114 p hg
    simpa only [d305, d4135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2116 (p : Pattern) (guard : d4118 p = 1) : d306 p ≤ (0 : Int) + d4135 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4118, d306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2094 p hg
    simpa only [d4118, d306, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d4118, d306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2115 p hg
    simpa only [d4118, d306, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2117 (p : Pattern) (guard : d0 p = 1) : d476 p ≤ (0 : Int) + d4136 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2118 (p : Pattern) (guard : d4119 p = 1) : d512 p ≤ (0 : Int) + d4137 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4118 p = 1 := by simpa only [d4119, d512, d4137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2116 p hg
    simpa only [d4119, d512, d4137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4119, d512, d4137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2117 p hg
    simpa only [d4119, d512, d4137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2119 (p : Pattern) (guard : d4119 p = 1) : d513 p ≤ (0 : Int) + d4138 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4119 p = 1 := by simpa only [d513, d4138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2093 p hg
    simpa only [d513, d4138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4119 p = 1 := by simpa only [d513, d4138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2118 p hg
    simpa only [d513, d4138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2120 (p : Pattern) (guard : d4119 p = 1) : d514 p ≤ (0 : Int) + d4139 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4119 p = 1 := by simpa only [d514, d4139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2038 p hg
    simpa only [d514, d4139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4119 p = 1 := by simpa only [d514, d4139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2119 p hg
    simpa only [d514, d4139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2121 (p : Pattern) (guard : d4119 p = 1) : d515 p ≤ (0 : Int) + d4140 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4119 p = 1 := by simpa only [d515, d4140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2082 p hg
    simpa only [d515, d4140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4119 p = 1 := by simpa only [d515, d4140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2120 p hg
    simpa only [d515, d4140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2122 (p : Pattern) (guard : d4119 p = 1) : d516 p ≤ (0 : Int) + d4141 p := by
  cases selected : p 48 with
  | false =>
    have hg : d4119 p = 1 := by simpa only [d516, d4141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2078 p hg
    simpa only [d516, d4141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4119 p = 1 := by simpa only [d516, d4141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2121 p hg
    simpa only [d516, d4141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2123 (p : Pattern) (guard : d0 p = 1) : d500 p ≤ (0 : Int) + d426 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2124 (p : Pattern) (guard : d4111 p = 1) : d501 p ≤ (0 : Int) + d489 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4066 p = 1 := by simpa only [d4111, d501, d489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1933 p hg
    simpa only [d4111, d501, d489, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4111, d501, d489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2123 p hg
    simpa only [d4111, d501, d489, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2125 (p : Pattern) (guard : d0 p = 1) : d503 p ≤ (0 : Int) + d445 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2126 (p : Pattern) (guard : d4111 p = 1) : d504 p ≤ (0 : Int) + d490 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4066 p = 1 := by simpa only [d4111, d504, d490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1938 p hg
    simpa only [d4111, d504, d490, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4111, d504, d490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2125 p hg
    simpa only [d4111, d504, d490, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2127 (p : Pattern) (guard : d4111 p = 1) : d505 p ≤ (0 : Int) + d491 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4111 p = 1 := by simpa only [d505, d491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2124 p hg
    simpa only [d505, d491, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4111 p = 1 := by simpa only [d505, d491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2126 p hg
    simpa only [d505, d491, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2128 (p : Pattern) (guard : d0 p = 1) : d507 p ≤ (0 : Int) + d445 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2129 (p : Pattern) (guard : d4111 p = 1) : d508 p ≤ (0 : Int) + d492 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4066 p = 1 := by simpa only [d4111, d508, d492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1944 p hg
    simpa only [d4111, d508, d492, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4111, d508, d492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2128 p hg
    simpa only [d4111, d508, d492, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2130 (p : Pattern) (guard : d4111 p = 1) : d509 p ≤ (0 : Int) + d493 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4111 p = 1 := by simpa only [d509, d493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2124 p hg
    simpa only [d509, d493, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4111 p = 1 := by simpa only [d509, d493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2129 p hg
    simpa only [d509, d493, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2131 (p : Pattern) (guard : d4111 p = 1) : d510 p ≤ (0 : Int) + d494 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4111 p = 1 := by simpa only [d510, d494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2127 p hg
    simpa only [d510, d494, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4111 p = 1 := by simpa only [d510, d494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2130 p hg
    simpa only [d510, d494, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2132 (p : Pattern) (guard : d0 p = 1) : d512 p ≤ (0 : Int) + d477 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2133 (p : Pattern) (guard : d4111 p = 1) : d513 p ≤ (0 : Int) + d495 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4066 p = 1 := by simpa only [d4111, d513, d495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1951 p hg
    simpa only [d4111, d513, d495, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4111, d513, d495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2132 p hg
    simpa only [d4111, d513, d495, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2134 (p : Pattern) (guard : d4111 p = 1) : d514 p ≤ (0 : Int) + d496 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4111 p = 1 := by simpa only [d514, d496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2124 p hg
    simpa only [d514, d496, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4111 p = 1 := by simpa only [d514, d496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2133 p hg
    simpa only [d514, d496, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2135 (p : Pattern) (guard : d4111 p = 1) : d515 p ≤ (0 : Int) + d497 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4111 p = 1 := by simpa only [d515, d497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2127 p hg
    simpa only [d515, d497, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4111 p = 1 := by simpa only [d515, d497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2134 p hg
    simpa only [d515, d497, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2136 (p : Pattern) (guard : d4111 p = 1) : d516 p ≤ (0 : Int) + d498 p := by
  cases selected : p 48 with
  | false =>
    have hg : d4111 p = 1 := by simpa only [d516, d498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2131 p hg
    simpa only [d516, d498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4111 p = 1 := by simpa only [d516, d498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2135 p hg
    simpa only [d516, d498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2137 (p : Pattern) (guard : d0 p = 1) : d499 p ≤ (2 : Int) + d98 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2138 (p : Pattern) (guard : d1 p = 1) : d88 p ≤ (2 : Int) + d88 p := by
  omega
theorem compare2139 (p : Pattern) (guard : d0 p = 1) : d425 p ≤ (2 : Int) + d97 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2140 (p : Pattern) (guard : d4066 p = 1) : d500 p ≤ (2 : Int) + d98 p := by
  cases selected : p 116 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4066, d500, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2138 p hg
    simpa only [d4066, d500, d98, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4066, d500, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2139 p hg
    simpa only [d4066, d500, d98, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2141 (p : Pattern) (guard : d4103 p = 1) : d501 p ≤ (2 : Int) + d98 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4103, d501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2137 p hg
    simpa only [d4103, d501, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4066 p = 1 := by simpa only [d4103, d501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2140 p hg
    simpa only [d4103, d501, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2142 (p : Pattern) (guard : d0 p = 1) : d502 p ≤ (2 : Int) + d98 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2143 (p : Pattern) (guard : d0 p = 1) : d444 p ≤ (2 : Int) + d97 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2144 (p : Pattern) (guard : d4066 p = 1) : d503 p ≤ (2 : Int) + d98 p := by
  cases selected : p 116 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4066, d503, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2138 p hg
    simpa only [d4066, d503, d98, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4066, d503, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2143 p hg
    simpa only [d4066, d503, d98, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2145 (p : Pattern) (guard : d4103 p = 1) : d504 p ≤ (2 : Int) + d98 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4103, d504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2142 p hg
    simpa only [d4103, d504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4066 p = 1 := by simpa only [d4103, d504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2144 p hg
    simpa only [d4103, d504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2146 (p : Pattern) (guard : d4103 p = 1) : d505 p ≤ (2 : Int) + d98 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4103 p = 1 := by simpa only [d505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2141 p hg
    simpa only [d505, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4103 p = 1 := by simpa only [d505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2145 p hg
    simpa only [d505, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2147 (p : Pattern) (guard : d0 p = 1) : d506 p ≤ (2 : Int) + d164 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2148 (p : Pattern) (guard : d1 p = 1) : d158 p ≤ (2 : Int) + d158 p := by
  omega
theorem compare2149 (p : Pattern) (guard : d0 p = 1) : d444 p ≤ (2 : Int) + d163 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2150 (p : Pattern) (guard : d4066 p = 1) : d507 p ≤ (2 : Int) + d164 p := by
  cases selected : p 116 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4066, d507, d164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2148 p hg
    simpa only [d4066, d507, d164, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4066, d507, d164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2149 p hg
    simpa only [d4066, d507, d164, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2151 (p : Pattern) (guard : d4103 p = 1) : d508 p ≤ (2 : Int) + d164 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4103, d508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2147 p hg
    simpa only [d4103, d508, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4066 p = 1 := by simpa only [d4103, d508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2150 p hg
    simpa only [d4103, d508, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2152 (p : Pattern) (guard : d4103 p = 1) : d509 p ≤ (2 : Int) + d4142 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4103 p = 1 := by simpa only [d509, d4142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2141 p hg
    simpa only [d509, d4142, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4103 p = 1 := by simpa only [d509, d4142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2151 p hg
    simpa only [d509, d4142, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2153 (p : Pattern) (guard : d4103 p = 1) : d510 p ≤ (2 : Int) + d4143 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4103 p = 1 := by simpa only [d510, d4143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2146 p hg
    simpa only [d510, d4143, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4103 p = 1 := by simpa only [d510, d4143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2152 p hg
    simpa only [d510, d4143, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2154 (p : Pattern) (guard : d0 p = 1) : d511 p ≤ (2 : Int) + d225 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2155 (p : Pattern) (guard : d1 p = 1) : d114 p ≤ (2 : Int) + d114 p := by
  omega
theorem compare2156 (p : Pattern) (guard : d1 p = 1) : d103 p ≤ (2 : Int) + d103 p := by
  omega
theorem compare2157 (p : Pattern) (guard : d1 p = 1) : d3 p ≤ (2 : Int) + d1 p := by
  change (3 : Int) ≤ (2 : Int) + 1
  decide
theorem compare2158 (p : Pattern) (guard : d1 p = 1) : d115 p ≤ (2 : Int) + d102 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d115, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2157 p hg
    simpa only [d115, d102, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d115, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d115, d102, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2159 (p : Pattern) (guard : d1 p = 1) : d116 p ≤ (2 : Int) + d103 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d116, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2157 p hg
    simpa only [d116, d103, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d116, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2158 p hg
    simpa only [d116, d103, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2160 (p : Pattern) (guard : d1 p = 1) : d268 p ≤ (2 : Int) + d103 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2156 p hg
    simpa only [d268, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2159 p hg
    simpa only [d268, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2161 (p : Pattern) (guard : d1 p = 1) : d117 p ≤ (2 : Int) + d117 p := by
  omega
theorem compare2162 (p : Pattern) (guard : d1 p = 1) : d269 p ≤ (2 : Int) + d118 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d269, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2160 p hg
    simpa only [d269, d118, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d269, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2161 p hg
    simpa only [d269, d118, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2163 (p : Pattern) (guard : d1 p = 1) : d121 p ≤ (2 : Int) + d121 p := by
  omega
theorem compare2164 (p : Pattern) (guard : d1 p = 1) : d270 p ≤ (2 : Int) + d122 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d270, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2160 p hg
    simpa only [d270, d122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d270, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2163 p hg
    simpa only [d270, d122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2165 (p : Pattern) (guard : d1 p = 1) : d271 p ≤ (2 : Int) + d123 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d271, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2162 p hg
    simpa only [d271, d123, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d271, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2164 p hg
    simpa only [d271, d123, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2166 (p : Pattern) (guard : d1 p = 1) : d272 p ≤ (2 : Int) + d124 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d272, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2160 p hg
    simpa only [d272, d124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d272, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d272, d124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2167 (p : Pattern) (guard : d1 p = 1) : d107 p ≤ (2 : Int) + d107 p := by
  omega
theorem compare2168 (p : Pattern) (guard : d1 p = 1) : d7 p ≤ (2 : Int) + d5 p := by
  change (7 : Int) ≤ (2 : Int) + 5
  decide
theorem compare2169 (p : Pattern) (guard : d1 p = 1) : d119 p ≤ (2 : Int) + d106 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d119, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2168 p hg
    simpa only [d119, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d119, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d119, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2170 (p : Pattern) (guard : d1 p = 1) : d120 p ≤ (2 : Int) + d107 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d120, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2168 p hg
    simpa only [d120, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d120, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2169 p hg
    simpa only [d120, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2171 (p : Pattern) (guard : d1 p = 1) : d273 p ≤ (2 : Int) + d107 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2167 p hg
    simpa only [d273, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2170 p hg
    simpa only [d273, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2172 (p : Pattern) (guard : d1 p = 1) : d274 p ≤ (2 : Int) + d125 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d274, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2171 p hg
    simpa only [d274, d125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d274, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d274, d125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2173 (p : Pattern) (guard : d1 p = 1) : d275 p ≤ (2 : Int) + d126 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d275, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2166 p hg
    simpa only [d275, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d275, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2172 p hg
    simpa only [d275, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2174 (p : Pattern) (guard : d1 p = 1) : d276 p ≤ (2 : Int) + d127 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d276, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2165 p hg
    simpa only [d276, d127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d276, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2173 p hg
    simpa only [d276, d127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2175 (p : Pattern) (guard : d1 p = 1) : d58 p ≤ (2 : Int) + d58 p := by
  omega
theorem compare2176 (p : Pattern) (guard : d1 p = 1) : d12 p ≤ (2 : Int) + d10 p := by
  change (12 : Int) ≤ (2 : Int) + 10
  decide
theorem compare2177 (p : Pattern) (guard : d1 p = 1) : d12 p ≤ (2 : Int) + d57 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2176 p hg
    simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2178 (p : Pattern) (guard : d1 p = 1) : d12 p ≤ (2 : Int) + d58 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2176 p hg
    simpa only [d58, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2177 p hg
    simpa only [d58, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2179 (p : Pattern) (guard : d1 p = 1) : d59 p ≤ (2 : Int) + d58 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2175 p hg
    simpa only [d59, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2178 p hg
    simpa only [d59, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2180 (p : Pattern) (guard : d1 p = 1) : d277 p ≤ (2 : Int) + d70 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d277, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2179 p hg
    simpa only [d277, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d277, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d277, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2181 (p : Pattern) (guard : d1 p = 1) : d278 p ≤ (2 : Int) + d128 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d278, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2180 p hg
    simpa only [d278, d128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d278, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d278, d128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2182 (p : Pattern) (guard : d1 p = 1) : d279 p ≤ (2 : Int) + d129 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d279, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2173 p hg
    simpa only [d279, d129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d279, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2181 p hg
    simpa only [d279, d129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2183 (p : Pattern) (guard : d1 p = 1) : d280 p ≤ (2 : Int) + d130 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d280, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2174 p hg
    simpa only [d280, d130, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d280, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2182 p hg
    simpa only [d280, d130, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2184 (p : Pattern) (guard : d1 p = 1) : d281 p ≤ (2 : Int) + d131 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d281, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2155 p hg
    simpa only [d281, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d281, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2183 p hg
    simpa only [d281, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2185 (p : Pattern) (guard : d1 p = 1) : d214 p ≤ (2 : Int) + d214 p := by
  omega
theorem compare2186 (p : Pattern) (guard : d1 p = 1) : d116 p ≤ (2 : Int) + d116 p := by
  omega
theorem compare2187 (p : Pattern) (guard : d1 p = 1) : d5 p ≤ (2 : Int) + d3 p := by
  change (5 : Int) ≤ (2 : Int) + 3
  decide
theorem compare2188 (p : Pattern) (guard : d1 p = 1) : d106 p ≤ (2 : Int) + d115 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d106, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2187 p hg
    simpa only [d106, d115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d106, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d106, d115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2189 (p : Pattern) (guard : d1 p = 1) : d107 p ≤ (2 : Int) + d116 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d107, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2187 p hg
    simpa only [d107, d116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d107, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2188 p hg
    simpa only [d107, d116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2190 (p : Pattern) (guard : d1 p = 1) : d282 p ≤ (2 : Int) + d116 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2186 p hg
    simpa only [d282, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2189 p hg
    simpa only [d282, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2191 (p : Pattern) (guard : d1 p = 1) : d283 p ≤ (2 : Int) + d139 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d283, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2190 p hg
    simpa only [d283, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d283, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d283, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2192 (p : Pattern) (guard : d1 p = 1) : d284 p ≤ (2 : Int) + d140 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d284, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2164 p hg
    simpa only [d284, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d284, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2191 p hg
    simpa only [d284, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2193 (p : Pattern) (guard : d1 p = 1) : d285 p ≤ (2 : Int) + d215 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d285, d215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2172 p hg
    simpa only [d285, d215, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d285, d215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d285, d215, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2194 (p : Pattern) (guard : d1 p = 1) : d286 p ≤ (2 : Int) + d216 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d286, d216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2192 p hg
    simpa only [d286, d216, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d286, d216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2193 p hg
    simpa only [d286, d216, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2195 (p : Pattern) (guard : d1 p = 1) : d287 p ≤ (2 : Int) + d217 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d287, d217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2193 p hg
    simpa only [d287, d217, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d287, d217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d287, d217, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2196 (p : Pattern) (guard : d1 p = 1) : d288 p ≤ (2 : Int) + d218 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d288, d218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2194 p hg
    simpa only [d288, d218, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d288, d218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2195 p hg
    simpa only [d288, d218, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2197 (p : Pattern) (guard : d1 p = 1) : d289 p ≤ (2 : Int) + d219 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d289, d219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2185 p hg
    simpa only [d289, d219, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d289, d219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2196 p hg
    simpa only [d289, d219, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2198 (p : Pattern) (guard : d1 p = 1) : d290 p ≤ (2 : Int) + d220 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d290, d220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2184 p hg
    simpa only [d290, d220, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d290, d220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2197 p hg
    simpa only [d290, d220, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2199 (p : Pattern) (guard : d1 p = 1) : d105 p ≤ (2 : Int) + d105 p := by
  omega
theorem compare2200 (p : Pattern) (guard : d1 p = 1) : d117 p ≤ (2 : Int) + d104 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d117, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2159 p hg
    simpa only [d117, d104, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d117, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d117, d104, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2201 (p : Pattern) (guard : d1 p = 1) : d269 p ≤ (2 : Int) + d105 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d269, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2160 p hg
    simpa only [d269, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d269, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2200 p hg
    simpa only [d269, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2202 (p : Pattern) (guard : d1 p = 1) : d291 p ≤ (2 : Int) + d105 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2199 p hg
    simpa only [d291, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2201 p hg
    simpa only [d291, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2203 (p : Pattern) (guard : d1 p = 1) : d121 p ≤ (2 : Int) + d108 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d121, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2170 p hg
    simpa only [d121, d108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d121, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d121, d108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2204 (p : Pattern) (guard : d1 p = 1) : d292 p ≤ (2 : Int) + d109 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d292, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2171 p hg
    simpa only [d292, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d292, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2203 p hg
    simpa only [d292, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2205 (p : Pattern) (guard : d1 p = 1) : d293 p ≤ (2 : Int) + d110 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d293, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2201 p hg
    simpa only [d293, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d293, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2204 p hg
    simpa only [d293, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2206 (p : Pattern) (guard : d1 p = 1) : d294 p ≤ (2 : Int) + d111 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d294, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2202 p hg
    simpa only [d294, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d294, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2205 p hg
    simpa only [d294, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2207 (p : Pattern) (guard : d1 p = 1) : d12 p ≤ (2 : Int) + d59 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2178 p hg
    simpa only [d59, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d59, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2208 (p : Pattern) (guard : d1 p = 1) : d277 p ≤ (2 : Int) + d60 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d277, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2179 p hg
    simpa only [d277, d60, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d277, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2207 p hg
    simpa only [d277, d60, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2209 (p : Pattern) (guard : d1 p = 1) : d278 p ≤ (2 : Int) + d112 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d278, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2208 p hg
    simpa only [d278, d112, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d278, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d278, d112, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2210 (p : Pattern) (guard : d1 p = 1) : d295 p ≤ (2 : Int) + d113 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d295, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2205 p hg
    simpa only [d295, d113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d295, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2209 p hg
    simpa only [d295, d113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2211 (p : Pattern) (guard : d1 p = 1) : d296 p ≤ (2 : Int) + d114 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d296, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2206 p hg
    simpa only [d296, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d296, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2210 p hg
    simpa only [d296, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2212 (p : Pattern) (guard : d1 p = 1) : d151 p ≤ (2 : Int) + d151 p := by
  omega
theorem compare2213 (p : Pattern) (guard : d1 p = 1) : d297 p ≤ (2 : Int) + d152 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d297, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2211 p hg
    simpa only [d297, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d297, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2212 p hg
    simpa only [d297, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2214 (p : Pattern) (guard : d1 p = 1) : d108 p ≤ (2 : Int) + d117 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d108, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2189 p hg
    simpa only [d108, d117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d108, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d108, d117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2215 (p : Pattern) (guard : d1 p = 1) : d298 p ≤ (2 : Int) + d132 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d298, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2190 p hg
    simpa only [d298, d132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d298, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2214 p hg
    simpa only [d298, d132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2216 (p : Pattern) (guard : d1 p = 1) : d299 p ≤ (2 : Int) + d133 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d299, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2201 p hg
    simpa only [d299, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d299, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2215 p hg
    simpa only [d299, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2217 (p : Pattern) (guard : d1 p = 1) : d300 p ≤ (2 : Int) + d211 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d300, d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2204 p hg
    simpa only [d300, d211, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d300, d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d300, d211, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2218 (p : Pattern) (guard : d1 p = 1) : d301 p ≤ (2 : Int) + d212 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d301, d212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2216 p hg
    simpa only [d301, d212, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d301, d212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2217 p hg
    simpa only [d301, d212, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2219 (p : Pattern) (guard : d1 p = 1) : d302 p ≤ (2 : Int) + d213 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d302, d213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2217 p hg
    simpa only [d302, d213, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d302, d213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d302, d213, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2220 (p : Pattern) (guard : d1 p = 1) : d303 p ≤ (2 : Int) + d214 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d303, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2218 p hg
    simpa only [d303, d214, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d303, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2219 p hg
    simpa only [d303, d214, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2221 (p : Pattern) (guard : d1 p = 1) : d155 p ≤ (2 : Int) + d155 p := by
  omega
theorem compare2222 (p : Pattern) (guard : d1 p = 1) : d304 p ≤ (2 : Int) + d221 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d304, d221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2220 p hg
    simpa only [d304, d221, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d304, d221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2221 p hg
    simpa only [d304, d221, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2223 (p : Pattern) (guard : d1 p = 1) : d305 p ≤ (2 : Int) + d222 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d305, d222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2213 p hg
    simpa only [d305, d222, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d305, d222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2222 p hg
    simpa only [d305, d222, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2224 (p : Pattern) (guard : d1 p = 1) : d306 p ≤ (2 : Int) + d223 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d306, d223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2198 p hg
    simpa only [d306, d223, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d306, d223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2223 p hg
    simpa only [d306, d223, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2225 (p : Pattern) (guard : d0 p = 1) : d476 p ≤ (2 : Int) + d224 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2226 (p : Pattern) (guard : d4066 p = 1) : d512 p ≤ (2 : Int) + d225 p := by
  cases selected : p 116 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4066, d512, d225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2224 p hg
    simpa only [d4066, d512, d225, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4066, d512, d225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2225 p hg
    simpa only [d4066, d512, d225, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2227 (p : Pattern) (guard : d4103 p = 1) : d513 p ≤ (2 : Int) + d225 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4103, d513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2154 p hg
    simpa only [d4103, d513, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4066 p = 1 := by simpa only [d4103, d513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2226 p hg
    simpa only [d4103, d513, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2228 (p : Pattern) (guard : d4103 p = 1) : d514 p ≤ (2 : Int) + d4144 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4103 p = 1 := by simpa only [d514, d4144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2141 p hg
    simpa only [d514, d4144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4103 p = 1 := by simpa only [d514, d4144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2227 p hg
    simpa only [d514, d4144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2229 (p : Pattern) (guard : d4103 p = 1) : d515 p ≤ (2 : Int) + d4145 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4103 p = 1 := by simpa only [d515, d4145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2146 p hg
    simpa only [d515, d4145, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4103 p = 1 := by simpa only [d515, d4145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2228 p hg
    simpa only [d515, d4145, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2230 (p : Pattern) (guard : d4103 p = 1) : d516 p ≤ (2 : Int) + d4146 p := by
  cases selected : p 48 with
  | false =>
    have hg : d4103 p = 1 := by simpa only [d516, d4146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2153 p hg
    simpa only [d516, d4146, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4103 p = 1 := by simpa only [d516, d4146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2229 p hg
    simpa only [d516, d4146, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2231 (p : Pattern) (guard : d1 p = 1) : d52 p ≤ (0 : Int) + d52 p := by
  omega
theorem compare2232 (p : Pattern) (guard : d0 p = 1) : d76 p ≤ (0 : Int) + d392 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2233 (p : Pattern) (guard : d4077 p = 1) : d77 p ≤ (0 : Int) + d653 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4077, d77, d653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2231 p hg
    simpa only [d4077, d77, d653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4077, d77, d653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2232 p hg
    simpa only [d4077, d77, d653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2234 (p : Pattern) (guard : d1 p = 1) : d82 p ≤ (0 : Int) + d82 p := by
  omega
theorem compare2235 (p : Pattern) (guard : d0 p = 1) : d86 p ≤ (0 : Int) + d399 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2236 (p : Pattern) (guard : d4077 p = 1) : d87 p ≤ (0 : Int) + d654 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4077, d87, d654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2234 p hg
    simpa only [d4077, d87, d654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4077, d87, d654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2235 p hg
    simpa only [d4077, d87, d654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2237 (p : Pattern) (guard : d4077 p = 1) : d88 p ≤ (0 : Int) + d655 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d88, d655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2233 p hg
    simpa only [d88, d655, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d88, d655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2236 p hg
    simpa only [d88, d655, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2238 (p : Pattern) (guard : d0 p = 1) : d86 p ≤ (0 : Int) + d407 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2239 (p : Pattern) (guard : d4077 p = 1) : d87 p ≤ (0 : Int) + d656 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4077, d87, d656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2234 p hg
    simpa only [d4077, d87, d656, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4077, d87, d656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2238 p hg
    simpa only [d4077, d87, d656, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
