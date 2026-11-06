import NetHack.Soko22Hazard87.Compare012
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare3250 (p : Pattern) (guard : d2129 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d2129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2128 p = 1 := by simpa only [d2129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3249 p hg
    simpa only [d2129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3251 (p : Pattern) (guard : d2130 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d2127 p = 1 := by simpa only [d2130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3246 p hg
    simpa only [d2130, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2129 p = 1 := by simpa only [d2130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3250 p hg
    simpa only [d2130, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3252 (p : Pattern) (guard : d2131 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d2131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2130 p = 1 := by simpa only [d2131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3251 p hg
    simpa only [d2131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3253 (p : Pattern) (guard : d2132 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d2131 p = 1 := by simpa only [d2132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3252 p hg
    simpa only [d2132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d2132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3254 (p : Pattern) (guard : d2133 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d2133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2132 p = 1 := by simpa only [d2133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3253 p hg
    simpa only [d2133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3255 (p : Pattern) (guard : d2134 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d2134, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2099 p = 1 := by simpa only [d2134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3243 p hg
    simpa only [d2134, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3256 (p : Pattern) (guard : d2135 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d2134 p = 1 := by simpa only [d2135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3255 p hg
    simpa only [d2135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d2135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3257 (p : Pattern) (guard : d2136 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d2136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2135 p = 1 := by simpa only [d2136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3256 p hg
    simpa only [d2136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3258 (p : Pattern) (guard : d2137 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d2137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2103 p = 1 := by simpa only [d2137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3247 p hg
    simpa only [d2137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3259 (p : Pattern) (guard : d2138 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d2137 p = 1 := by simpa only [d2138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3258 p hg
    simpa only [d2138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d2138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3260 (p : Pattern) (guard : d2139 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d2139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2138 p = 1 := by simpa only [d2139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3259 p hg
    simpa only [d2139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3261 (p : Pattern) (guard : d2140 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d2136 p = 1 := by simpa only [d2140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3257 p hg
    simpa only [d2140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2139 p = 1 := by simpa only [d2140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3260 p hg
    simpa only [d2140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3262 (p : Pattern) (guard : d2141 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d2141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2140 p = 1 := by simpa only [d2141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3261 p hg
    simpa only [d2141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3263 (p : Pattern) (guard : d2142 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d2141 p = 1 := by simpa only [d2142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3262 p hg
    simpa only [d2142, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d2142, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3264 (p : Pattern) (guard : d2144 p = 1) : d47660 p ≤ (0 : Int) + d47735 p := by
  cases selected : p 163 with
  | false =>
    have hg : d2143 p = 1 := by simpa only [d2144, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare889 p hg
    simpa only [d2144, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2144, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2486 p hg
    simpa only [d2144, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3265 (p : Pattern) (guard : d2145 p = 1) : d47663 p ≤ (0 : Int) + d47736 p := by
  cases selected : p 162 with
  | false =>
    have hg : d2144 p = 1 := by simpa only [d2145, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3264 p hg
    simpa only [d2145, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2145, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2488 p hg
    simpa only [d2145, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3266 (p : Pattern) (guard : d2146 p = 1) : d47664 p ≤ (0 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2146, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2485 p hg
    simpa only [d2146, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2145 p = 1 := by simpa only [d2146, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3265 p hg
    simpa only [d2146, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3267 (p : Pattern) (guard : d2147 p = 1) : d47685 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d2146 p = 1 := by simpa only [d2147, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3266 p hg
    simpa only [d2147, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2147, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2491 p hg
    simpa only [d2147, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3268 (p : Pattern) (guard : d2148 p = 1) : d47685 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d2147 p = 1 := by simpa only [d2148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3267 p hg
    simpa only [d2148, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2038 p = 1 := by simpa only [d2148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3207 p hg
    simpa only [d2148, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3269 (p : Pattern) (guard : d2149 p = 1) : d47685 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d2148 p = 1 := by simpa only [d2149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3268 p hg
    simpa only [d2149, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2057 p = 1 := by simpa only [d2149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3212 p hg
    simpa only [d2149, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3270 (p : Pattern) (guard : d2150 p = 1) : d47685 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d2149 p = 1 := by simpa only [d2150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3269 p hg
    simpa only [d2150, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2070 p = 1 := by simpa only [d2150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3218 p hg
    simpa only [d2150, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3271 (p : Pattern) (guard : d2151 p = 1) : d47686 p ≤ (0 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2151, d47686, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2484 p hg
    simpa only [d2151, d47686, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2150 p = 1 := by simpa only [d2151, d47686, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3270 p hg
    simpa only [d2151, d47686, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3272 (p : Pattern) (guard : d2152 p = 1) : d47687 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2152, d47687, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2483 p hg
    simpa only [d2152, d47687, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2151 p = 1 := by simpa only [d2152, d47687, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3271 p hg
    simpa only [d2152, d47687, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3273 (p : Pattern) (guard : d2153 p = 1) : d47687 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d2152 p = 1 := by simpa only [d2153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3272 p hg
    simpa only [d2153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2075 p = 1 := by simpa only [d2153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3223 p hg
    simpa only [d2153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3274 (p : Pattern) (guard : d2154 p = 1) : d47687 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d2153 p = 1 := by simpa only [d2154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3273 p hg
    simpa only [d2154, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2089 p = 1 := by simpa only [d2154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3233 p hg
    simpa only [d2154, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3275 (p : Pattern) (guard : d2155 p = 1) : d47687 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d2154 p = 1 := by simpa only [d2155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3274 p hg
    simpa only [d2155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2499 p hg
    simpa only [d2155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3276 (p : Pattern) (guard : d2156 p = 1) : d47699 p ≤ (0 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d2155 p = 1 := by simpa only [d2156, d47699, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3275 p hg
    simpa only [d2156, d47699, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2156, d47699, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2503 p hg
    simpa only [d2156, d47699, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3277 (p : Pattern) (guard : d2157 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2157, d47700, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22 p hg
    simpa only [d2157, d47700, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2156 p = 1 := by simpa only [d2157, d47700, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3276 p hg
    simpa only [d2157, d47700, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3278 (p : Pattern) (guard : d2158 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d2157 p = 1 := by simpa only [d2158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3277 p hg
    simpa only [d2158, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2094 p = 1 := by simpa only [d2158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3238 p hg
    simpa only [d2158, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3279 (p : Pattern) (guard : d2159 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d2158 p = 1 := by simpa only [d2159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3278 p hg
    simpa only [d2159, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d2159, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3280 (p : Pattern) (guard : d2160 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d2159 p = 1 := by simpa only [d2160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3279 p hg
    simpa only [d2160, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d2160, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3281 (p : Pattern) (guard : d2161 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d2161, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2160 p = 1 := by simpa only [d2161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3280 p hg
    simpa only [d2161, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3282 (p : Pattern) (guard : d2101 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d2100 p = 1 := by simpa only [d2101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3244 p hg
    simpa only [d2101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d2101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3283 (p : Pattern) (guard : d2102 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d2102, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2101 p = 1 := by simpa only [d2102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3282 p hg
    simpa only [d2102, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3284 (p : Pattern) (guard : d2162 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d2161 p = 1 := by simpa only [d2162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3281 p hg
    simpa only [d2162, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2102 p = 1 := by simpa only [d2162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3283 p hg
    simpa only [d2162, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3285 (p : Pattern) (guard : d4566 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d2162 p = 1 := by simpa only [d4566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3284 p hg
    simpa only [d4566, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d4566, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3286 (p : Pattern) (guard : d2275 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d2102 p = 1 := by simpa only [d2275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3283 p hg
    simpa only [d2275, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d2275, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3287 (p : Pattern) (guard : d2276 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d2275 p = 1 := by simpa only [d2276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3286 p hg
    simpa only [d2276, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d2276, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3288 (p : Pattern) (guard : d4567 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d4566 p = 1 := by simpa only [d4567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3285 p hg
    simpa only [d4567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2276 p = 1 := by simpa only [d4567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3287 p hg
    simpa only [d4567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3289 (p : Pattern) (guard : d51793 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d2142 p = 1 := by simpa only [d51793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3263 p hg
    simpa only [d51793, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4567 p = 1 := by simpa only [d51793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3288 p hg
    simpa only [d51793, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3290 (p : Pattern) (guard : d51794 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 73 with
  | false =>
    have hg : d2133 p = 1 := by simpa only [d51794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3254 p hg
    simpa only [d51794, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d51793 p = 1 := by simpa only [d51794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3289 p hg
    simpa only [d51794, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3291 (p : Pattern) (guard : d51795 p = 1) : d47700 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d51795, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20 p hg
    simpa only [d51795, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d51794 p = 1 := by simpa only [d51795, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3290 p hg
    simpa only [d51795, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3292 (p : Pattern) (guard : d51794 p = 1) : d47700 p ≤ (0 : Int) + d47700 p := by
  omega
theorem compare3293 (p : Pattern) (guard : d2281 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d2126 p = 1 := by simpa only [d2281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3245 p hg
    simpa only [d2281, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d2281, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3294 (p : Pattern) (guard : d2282 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d2128 p = 1 := by simpa only [d2282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3249 p hg
    simpa only [d2282, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d2282, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3295 (p : Pattern) (guard : d2283 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d2281 p = 1 := by simpa only [d2283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3293 p hg
    simpa only [d2283, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2282 p = 1 := by simpa only [d2283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3294 p hg
    simpa only [d2283, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3296 (p : Pattern) (guard : d2284 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d2284, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2283 p = 1 := by simpa only [d2284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3295 p hg
    simpa only [d2284, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3297 (p : Pattern) (guard : d2285 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d2284 p = 1 := by simpa only [d2285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3296 p hg
    simpa only [d2285, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d2285, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3298 (p : Pattern) (guard : d2286 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d2286, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2285 p = 1 := by simpa only [d2286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3297 p hg
    simpa only [d2286, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3299 (p : Pattern) (guard : d2287 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d2135 p = 1 := by simpa only [d2287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3256 p hg
    simpa only [d2287, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d2287, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3300 (p : Pattern) (guard : d2288 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d2138 p = 1 := by simpa only [d2288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3259 p hg
    simpa only [d2288, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d2288, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3301 (p : Pattern) (guard : d2289 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d2287 p = 1 := by simpa only [d2289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3299 p hg
    simpa only [d2289, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2288 p = 1 := by simpa only [d2289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3300 p hg
    simpa only [d2289, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3302 (p : Pattern) (guard : d2290 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d2290, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2289 p = 1 := by simpa only [d2290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3301 p hg
    simpa only [d2290, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3303 (p : Pattern) (guard : d2291 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d2290 p = 1 := by simpa only [d2291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3302 p hg
    simpa only [d2291, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d2291, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3304 (p : Pattern) (guard : d2292 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d2160 p = 1 := by simpa only [d2292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3280 p hg
    simpa only [d2292, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d2292, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3305 (p : Pattern) (guard : d2115 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d2101 p = 1 := by simpa only [d2115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3282 p hg
    simpa only [d2115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d2115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3306 (p : Pattern) (guard : d2293 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d2292 p = 1 := by simpa only [d2293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3304 p hg
    simpa only [d2293, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2115 p = 1 := by simpa only [d2293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3305 p hg
    simpa only [d2293, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3307 (p : Pattern) (guard : d4571 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d2293 p = 1 := by simpa only [d4571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3306 p hg
    simpa only [d4571, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d4571, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3308 (p : Pattern) (guard : d2298 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d2115 p = 1 := by simpa only [d2298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3305 p hg
    simpa only [d2298, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d2298, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3309 (p : Pattern) (guard : d2299 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d2298 p = 1 := by simpa only [d2299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3308 p hg
    simpa only [d2299, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d2299, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3310 (p : Pattern) (guard : d4572 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d4571 p = 1 := by simpa only [d4572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3307 p hg
    simpa only [d4572, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2299 p = 1 := by simpa only [d4572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3309 p hg
    simpa only [d4572, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3311 (p : Pattern) (guard : d51796 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d2291 p = 1 := by simpa only [d51796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3303 p hg
    simpa only [d51796, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4572 p = 1 := by simpa only [d51796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3310 p hg
    simpa only [d51796, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3312 (p : Pattern) (guard : d51797 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 73 with
  | false =>
    have hg : d2286 p = 1 := by simpa only [d51797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3298 p hg
    simpa only [d51797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d51796 p = 1 := by simpa only [d51797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3311 p hg
    simpa only [d51797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3313 (p : Pattern) (guard : d51798 p = 1) : d47700 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 71 with
  | false =>
    have hg : d51794 p = 1 := by simpa only [d51798, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3292 p hg
    simpa only [d51798, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d51797 p = 1 := by simpa only [d51798, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3312 p hg
    simpa only [d51798, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3314 (p : Pattern) (guard : d51799 p = 1) : d47700 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 70 with
  | false =>
    have hg : d51795 p = 1 := by simpa only [d51799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3291 p hg
    simpa only [d51799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d51798 p = 1 := by simpa only [d51799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3313 p hg
    simpa only [d51799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3315 (p : Pattern) (guard : d2105 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d2104 p = 1 := by simpa only [d2105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3248 p hg
    simpa only [d2105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d2105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3316 (p : Pattern) (guard : d2106 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d2106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2105 p = 1 := by simpa only [d2106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3315 p hg
    simpa only [d2106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3317 (p : Pattern) (guard : d2305 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d2106 p = 1 := by simpa only [d2305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3316 p hg
    simpa only [d2305, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d2305, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3318 (p : Pattern) (guard : d2306 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d2306, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2305 p = 1 := by simpa only [d2306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3317 p hg
    simpa only [d2306, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3319 (p : Pattern) (guard : d2307 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d2306 p = 1 := by simpa only [d2307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3318 p hg
    simpa only [d2307, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d2307, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3320 (p : Pattern) (guard : d2308 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d2308, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2307 p = 1 := by simpa only [d2308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3319 p hg
    simpa only [d2308, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3321 (p : Pattern) (guard : d2309 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d2309, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2308 p = 1 := by simpa only [d2309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3320 p hg
    simpa only [d2309, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3322 (p : Pattern) (guard : d2310 p = 1) : d47700 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 71 with
  | false =>
    have hg : d2111 p = 1 := by simpa only [d2310, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2414 p hg
    simpa only [d2310, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2309 p = 1 := by simpa only [d2310, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3321 p hg
    simpa only [d2310, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3323 (p : Pattern) (guard : d2309 p = 1) : d47700 p ≤ (0 : Int) + d47700 p := by
  omega
theorem compare3324 (p : Pattern) (guard : d2116 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d2105 p = 1 := by simpa only [d2116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3315 p hg
    simpa only [d2116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d2116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3325 (p : Pattern) (guard : d2311 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d2116 p = 1 := by simpa only [d2311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3324 p hg
    simpa only [d2311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d2311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3326 (p : Pattern) (guard : d2312 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d2312, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2311 p = 1 := by simpa only [d2312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3325 p hg
    simpa only [d2312, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3327 (p : Pattern) (guard : d2313 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d2312 p = 1 := by simpa only [d2313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3326 p hg
    simpa only [d2313, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d2313, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3328 (p : Pattern) (guard : d2314 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d2314, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2313 p = 1 := by simpa only [d2314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3327 p hg
    simpa only [d2314, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3329 (p : Pattern) (guard : d2315 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d2315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2314 p = 1 := by simpa only [d2315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3328 p hg
    simpa only [d2315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3330 (p : Pattern) (guard : d2316 p = 1) : d47700 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 71 with
  | false =>
    have hg : d2309 p = 1 := by simpa only [d2316, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3323 p hg
    simpa only [d2316, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2315 p = 1 := by simpa only [d2316, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3329 p hg
    simpa only [d2316, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3331 (p : Pattern) (guard : d2317 p = 1) : d47700 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 70 with
  | false =>
    have hg : d2310 p = 1 := by simpa only [d2317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3322 p hg
    simpa only [d2317, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2316 p = 1 := by simpa only [d2317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3330 p hg
    simpa only [d2317, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3332 (p : Pattern) (guard : d51800 p = 1) : d47700 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 69 with
  | false =>
    have hg : d51799 p = 1 := by simpa only [d51800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3314 p hg
    simpa only [d51800, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2317 p = 1 := by simpa only [d51800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3331 p hg
    simpa only [d51800, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3333 (p : Pattern) (guard : d51801 p = 1) : d47700 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 51 with
  | false =>
    have hg : d51800 p = 1 := by simpa only [d51801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3332 p hg
    simpa only [d51801, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d51801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2481 p hg
    simpa only [d51801, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3334 (p : Pattern) (guard : d64479 p = 1) : d47700 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 50 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d64479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2481 p hg
    simpa only [d64479, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d51801 p = 1 := by simpa only [d64479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3333 p hg
    simpa only [d64479, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3335 (p : Pattern) (guard : d64480 p = 1) : d47768 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 49 with
  | false =>
    have hg : d64479 p = 1 := by simpa only [d64480, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3334 p hg
    simpa only [d64480, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d64480, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2528 p hg
    simpa only [d64480, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3336 (p : Pattern) (guard : d64481 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 48 with
  | false =>
    have hg : d64480 p = 1 := by simpa only [d64481, d47911, d65730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3335 p hg
    simpa only [d64481, d47911, d65730, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d64481, d47911, d65730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2530 p hg
    simpa only [d64481, d47911, d65730, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3337 (p : Pattern) (guard : d64482 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d64482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d64482, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d64481 p = 1 := by simpa only [d64482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3336 p hg
    simpa only [d64482, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3338 (p : Pattern) (guard : d64483 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d64483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d64483, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d64482 p = 1 := by simpa only [d64483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3337 p hg
    simpa only [d64483, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3339 (p : Pattern) (guard : d64484 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d64484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d64484, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d64483 p = 1 := by simpa only [d64484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3338 p hg
    simpa only [d64484, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3340 (p : Pattern) (guard : d64485 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d64485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d64485, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d64484 p = 1 := by simpa only [d64485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3339 p hg
    simpa only [d64485, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3341 (p : Pattern) (guard : d64486 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d64486, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d64486, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d64485 p = 1 := by simpa only [d64486, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3340 p hg
    simpa only [d64486, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3342 (p : Pattern) (guard : d64487 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d64487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d64487, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d64486 p = 1 := by simpa only [d64487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3341 p hg
    simpa only [d64487, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3343 (p : Pattern) (guard : d64488 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d64488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d64488, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d64487 p = 1 := by simpa only [d64488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3342 p hg
    simpa only [d64488, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3344 (p : Pattern) (guard : d64489 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d64489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d64489, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d64488 p = 1 := by simpa only [d64489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3343 p hg
    simpa only [d64489, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3345 (p : Pattern) (guard : d64490 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 10252 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d64490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d64490, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d64489 p = 1 := by simpa only [d64490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3344 p hg
    simpa only [d64490, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3346 (p : Pattern) (guard : d64491 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 10251 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d64491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d64491, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d64490 p = 1 := by simpa only [d64491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3345 p hg
    simpa only [d64491, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3347 (p : Pattern) (guard : d64492 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 10250 with
  | false =>
    have hg : d64478 p = 1 := by simpa only [d64492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3203 p hg
    simpa only [d64492, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d64491 p = 1 := by simpa only [d64492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3346 p hg
    simpa only [d64492, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3348 (p : Pattern) (guard : d64493 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 260 with
  | false =>
    have hg : d64492 p = 1 := by simpa only [d64493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3347 p hg
    simpa only [d64493, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d64493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d64493, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3349 (p : Pattern) (guard : d64494 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 259 with
  | false =>
    have hg : d64493 p = 1 := by simpa only [d64494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3348 p hg
    simpa only [d64494, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d64494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d64494, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3350 (p : Pattern) (guard : d64495 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 258 with
  | false =>
    have hg : d64494 p = 1 := by simpa only [d64495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3349 p hg
    simpa only [d64495, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d64495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d64495, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3351 (p : Pattern) (guard : d64496 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 257 with
  | false =>
    have hg : d64495 p = 1 := by simpa only [d64496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3350 p hg
    simpa only [d64496, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d64496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d64496, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3352 (p : Pattern) (guard : d64497 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 256 with
  | false =>
    have hg : d64496 p = 1 := by simpa only [d64497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3351 p hg
    simpa only [d64497, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d64497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d64497, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3353 (p : Pattern) (guard : d64498 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 255 with
  | false =>
    have hg : d64497 p = 1 := by simpa only [d64498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3352 p hg
    simpa only [d64498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d64498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d64498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3354 (p : Pattern) (guard : d64499 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 254 with
  | false =>
    have hg : d64498 p = 1 := by simpa only [d64499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3353 p hg
    simpa only [d64499, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d64499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d64499, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3355 (p : Pattern) (guard : d64500 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 253 with
  | false =>
    have hg : d64499 p = 1 := by simpa only [d64500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3354 p hg
    simpa only [d64500, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d64500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d64500, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3356 (p : Pattern) (guard : d64501 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 252 with
  | false =>
    have hg : d64500 p = 1 := by simpa only [d64501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3355 p hg
    simpa only [d64501, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d64501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d64501, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3357 (p : Pattern) (guard : d64502 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 251 with
  | false =>
    have hg : d64501 p = 1 := by simpa only [d64502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3356 p hg
    simpa only [d64502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d64502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d64502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3358 (p : Pattern) (guard : d64503 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 250 with
  | false =>
    have hg : d64502 p = 1 := by simpa only [d64503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3357 p hg
    simpa only [d64503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d64503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d64503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3359 (p : Pattern) (guard : d64504 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 249 with
  | false =>
    have hg : d64503 p = 1 := by simpa only [d64504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3358 p hg
    simpa only [d64504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d64504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d64504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3360 (p : Pattern) (guard : d64505 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 245 with
  | false =>
    have hg : d64504 p = 1 := by simpa only [d64505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3359 p hg
    simpa only [d64505, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d64505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d64505, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3361 (p : Pattern) (guard : d64506 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 200 with
  | false =>
    have hg : d64505 p = 1 := by simpa only [d64506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3360 p hg
    simpa only [d64506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d64506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d64506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3362 (p : Pattern) (guard : d64507 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 199 with
  | false =>
    have hg : d64506 p = 1 := by simpa only [d64507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3361 p hg
    simpa only [d64507, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d64507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d64507, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3363 (p : Pattern) (guard : d64508 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 186 with
  | false =>
    have hg : d64507 p = 1 := by simpa only [d64508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3362 p hg
    simpa only [d64508, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d64508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d64508, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3364 (p : Pattern) (guard : d64509 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 185 with
  | false =>
    have hg : d64508 p = 1 := by simpa only [d64509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3363 p hg
    simpa only [d64509, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d64509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d64509, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3365 (p : Pattern) (guard : d64510 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 184 with
  | false =>
    have hg : d64509 p = 1 := by simpa only [d64510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3364 p hg
    simpa only [d64510, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d64510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d64510, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3366 (p : Pattern) (guard : d64511 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 181 with
  | false =>
    have hg : d64510 p = 1 := by simpa only [d64511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3365 p hg
    simpa only [d64511, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d64511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d64511, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3367 (p : Pattern) (guard : d64512 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 177 with
  | false =>
    have hg : d64511 p = 1 := by simpa only [d64512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3366 p hg
    simpa only [d64512, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d64512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d64512, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3368 (p : Pattern) (guard : d64513 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 164 with
  | false =>
    have hg : d64512 p = 1 := by simpa only [d64513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3367 p hg
    simpa only [d64513, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d64513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d64513, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3369 (p : Pattern) (guard : d64514 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 156 with
  | false =>
    have hg : d64513 p = 1 := by simpa only [d64514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3368 p hg
    simpa only [d64514, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d64514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d64514, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3370 (p : Pattern) (guard : d64515 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 155 with
  | false =>
    have hg : d64514 p = 1 := by simpa only [d64515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3369 p hg
    simpa only [d64515, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d64515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d64515, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3371 (p : Pattern) (guard : d64516 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 134 with
  | false =>
    have hg : d64515 p = 1 := by simpa only [d64516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3370 p hg
    simpa only [d64516, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d64516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d64516, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3372 (p : Pattern) (guard : d64517 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 133 with
  | false =>
    have hg : d64516 p = 1 := by simpa only [d64517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3371 p hg
    simpa only [d64517, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d64517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d64517, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3373 (p : Pattern) (guard : d64518 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 120 with
  | false =>
    have hg : d64517 p = 1 := by simpa only [d64518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3372 p hg
    simpa only [d64518, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d64518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d64518, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3374 (p : Pattern) (guard : d64519 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 118 with
  | false =>
    have hg : d64518 p = 1 := by simpa only [d64519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3373 p hg
    simpa only [d64519, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d64519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d64519, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3375 (p : Pattern) (guard : d64520 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 114 with
  | false =>
    have hg : d64519 p = 1 := by simpa only [d64520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3374 p hg
    simpa only [d64520, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d64520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d64520, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3376 (p : Pattern) (guard : d64521 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 111 with
  | false =>
    have hg : d64520 p = 1 := by simpa only [d64521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3375 p hg
    simpa only [d64521, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d64521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d64521, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3377 (p : Pattern) (guard : d64522 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 98 with
  | false =>
    have hg : d64521 p = 1 := by simpa only [d64522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3376 p hg
    simpa only [d64522, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d64522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d64522, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3378 (p : Pattern) (guard : d64523 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 97 with
  | false =>
    have hg : d64522 p = 1 := by simpa only [d64523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3377 p hg
    simpa only [d64523, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d64523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d64523, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3379 (p : Pattern) (guard : d64524 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 94 with
  | false =>
    have hg : d64523 p = 1 := by simpa only [d64524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3378 p hg
    simpa only [d64524, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d64524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d64524, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3380 (p : Pattern) (guard : d64525 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 76 with
  | false =>
    have hg : d64524 p = 1 := by simpa only [d64525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3379 p hg
    simpa only [d64525, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d64525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d64525, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3381 (p : Pattern) (guard : d64526 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 67 with
  | false =>
    have hg : d64525 p = 1 := by simpa only [d64526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3380 p hg
    simpa only [d64526, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d64526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d64526, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3382 (p : Pattern) (guard : d64527 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 52 with
  | false =>
    have hg : d64526 p = 1 := by simpa only [d64527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3381 p hg
    simpa only [d64527, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d64527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d64527, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3383 (p : Pattern) (guard : d64528 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 47 with
  | false =>
    have hg : d64527 p = 1 := by simpa only [d64528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3382 p hg
    simpa only [d64528, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d64528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d64528, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3384 (p : Pattern) (guard : d64529 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 46 with
  | false =>
    have hg : d64528 p = 1 := by simpa only [d64529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3383 p hg
    simpa only [d64529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d64529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d64529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3385 (p : Pattern) (guard : d64530 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 45 with
  | false =>
    have hg : d64529 p = 1 := by simpa only [d64530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3384 p hg
    simpa only [d64530, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d64530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d64530, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3386 (p : Pattern) (guard : d64531 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 30 with
  | false =>
    have hg : d64530 p = 1 := by simpa only [d64531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3385 p hg
    simpa only [d64531, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d64531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d64531, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3387 (p : Pattern) (guard : d64532 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 29 with
  | false =>
    have hg : d64531 p = 1 := by simpa only [d64532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3386 p hg
    simpa only [d64532, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d64532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d64532, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3388 (p : Pattern) (guard : d64533 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 28 with
  | false =>
    have hg : d64532 p = 1 := by simpa only [d64533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3387 p hg
    simpa only [d64533, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d64533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d64533, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3389 (p : Pattern) (guard : d64534 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 27 with
  | false =>
    have hg : d64533 p = 1 := by simpa only [d64534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3388 p hg
    simpa only [d64534, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d64534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d64534, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3390 (p : Pattern) (guard : d64535 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 25 with
  | false =>
    have hg : d64534 p = 1 := by simpa only [d64535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3389 p hg
    simpa only [d64535, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d64535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d64535, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3391 (p : Pattern) (guard : d0 p = 1) : d47911 p ≤ (-1 : Int) + d65730 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3392 (p : Pattern) (guard : d0 p = 1) : d47700 p ≤ (-1 : Int) + d47767 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3393 (p : Pattern) (guard : d0 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3394 (p : Pattern) (guard : d0 p = 1) : d47676 p ≤ (-1 : Int) + d47746 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3395 (p : Pattern) (guard : d0 p = 1) : d47681 p ≤ (-1 : Int) + d47751 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3396 (p : Pattern) (guard : d0 p = 1) : d47655 p ≤ (-1 : Int) + d47734 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3397 (p : Pattern) (guard : d0 p = 1) : d47659 p ≤ (-1 : Int) + d47661 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3398 (p : Pattern) (guard : d25 p = 1) : d47660 p ≤ (-1 : Int) + d47735 p := by
  cases selected : p 163 with
  | false =>
    have hg : d24 p = 1 := by simpa only [d25, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1167 p hg
    simpa only [d25, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d25, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3397 p hg
    simpa only [d25, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3399 (p : Pattern) (guard : d0 p = 1) : d47662 p ≤ (-1 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3400 (p : Pattern) (guard : d26 p = 1) : d47663 p ≤ (-1 : Int) + d47736 p := by
  cases selected : p 162 with
  | false =>
    have hg : d25 p = 1 := by simpa only [d26, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3398 p hg
    simpa only [d26, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d26, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3399 p hg
    simpa only [d26, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3401 (p : Pattern) (guard : d27 p = 1) : d47664 p ≤ (-1 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d27, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3396 p hg
    simpa only [d27, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d26 p = 1 := by simpa only [d27, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3400 p hg
    simpa only [d27, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3402 (p : Pattern) (guard : d0 p = 1) : d47684 p ≤ (-1 : Int) + d47754 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3403 (p : Pattern) (guard : d28 p = 1) : d47685 p ≤ (-1 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d27 p = 1 := by simpa only [d28, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3401 p hg
    simpa only [d28, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d28, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3402 p hg
    simpa only [d28, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3404 (p : Pattern) (guard : d0 p = 1) : d47685 p ≤ (-1 : Int) + d47755 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3405 (p : Pattern) (guard : d29 p = 1) : d47685 p ≤ (-1 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d28 p = 1 := by simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3403 p hg
    simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3404 p hg
    simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3406 (p : Pattern) (guard : d30 p = 1) : d47685 p ≤ (-1 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d29 p = 1 := by simpa only [d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3405 p hg
    simpa only [d30, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3404 p hg
    simpa only [d30, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3407 (p : Pattern) (guard : d31 p = 1) : d47685 p ≤ (-1 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d30 p = 1 := by simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3406 p hg
    simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3404 p hg
    simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3408 (p : Pattern) (guard : d32 p = 1) : d47686 p ≤ (-1 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d32, d47686, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3395 p hg
    simpa only [d32, d47686, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d31 p = 1 := by simpa only [d32, d47686, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3407 p hg
    simpa only [d32, d47686, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3409 (p : Pattern) (guard : d33 p = 1) : d47687 p ≤ (-1 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d33, d47687, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3394 p hg
    simpa only [d33, d47687, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d32 p = 1 := by simpa only [d33, d47687, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3408 p hg
    simpa only [d33, d47687, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3410 (p : Pattern) (guard : d0 p = 1) : d47687 p ≤ (-1 : Int) + d47757 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3411 (p : Pattern) (guard : d34 p = 1) : d47687 p ≤ (-1 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d33 p = 1 := by simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3409 p hg
    simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3410 p hg
    simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3412 (p : Pattern) (guard : d35 p = 1) : d47687 p ≤ (-1 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d34 p = 1 := by simpa only [d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3411 p hg
    simpa only [d35, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3410 p hg
    simpa only [d35, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3413 (p : Pattern) (guard : d36 p = 1) : d47687 p ≤ (-1 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d35 p = 1 := by simpa only [d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3412 p hg
    simpa only [d36, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3410 p hg
    simpa only [d36, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3414 (p : Pattern) (guard : d0 p = 1) : d47698 p ≤ (-1 : Int) + d47764 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3415 (p : Pattern) (guard : d37 p = 1) : d47699 p ≤ (-1 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d36 p = 1 := by simpa only [d37, d47699, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3413 p hg
    simpa only [d37, d47699, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d37, d47699, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3414 p hg
    simpa only [d37, d47699, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3416 (p : Pattern) (guard : d38 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d38, d47700, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1133 p hg
    simpa only [d38, d47700, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d37 p = 1 := by simpa only [d38, d47700, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3415 p hg
    simpa only [d38, d47700, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3417 (p : Pattern) (guard : d39 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d38 p = 1 := by simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3416 p hg
    simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3393 p hg
    simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3418 (p : Pattern) (guard : d40 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d39 p = 1 := by simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3417 p hg
    simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3393 p hg
    simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3419 (p : Pattern) (guard : d41 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d40 p = 1 := by simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3418 p hg
    simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3393 p hg
    simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3420 (p : Pattern) (guard : d42 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3393 p hg
    simpa only [d42, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d41 p = 1 := by simpa only [d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3419 p hg
    simpa only [d42, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3421 (p : Pattern) (guard : d43 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d42 p = 1 := by simpa only [d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3420 p hg
    simpa only [d43, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3393 p hg
    simpa only [d43, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3422 (p : Pattern) (guard : d100 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3393 p hg
    simpa only [d100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d43 p = 1 := by simpa only [d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3421 p hg
    simpa only [d100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3423 (p : Pattern) (guard : d101 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d100 p = 1 := by simpa only [d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3422 p hg
    simpa only [d101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3393 p hg
    simpa only [d101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3424 (p : Pattern) (guard : d102 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3393 p hg
    simpa only [d102, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d101 p = 1 := by simpa only [d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3423 p hg
    simpa only [d102, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3425 (p : Pattern) (guard : d103 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3393 p hg
    simpa only [d103, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d102 p = 1 := by simpa only [d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3424 p hg
    simpa only [d103, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3426 (p : Pattern) (guard : d104 p = 1) : d47700 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d104, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1131 p hg
    simpa only [d104, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d103 p = 1 := by simpa only [d104, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3425 p hg
    simpa only [d104, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3427 (p : Pattern) (guard : d49 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d41 p = 1 := by simpa only [d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3419 p hg
    simpa only [d49, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3393 p hg
    simpa only [d49, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3428 (p : Pattern) (guard : d50 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d49 p = 1 := by simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3427 p hg
    simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3393 p hg
    simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3429 (p : Pattern) (guard : d107 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3393 p hg
    simpa only [d107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d50 p = 1 := by simpa only [d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3428 p hg
    simpa only [d107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3430 (p : Pattern) (guard : d108 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d107 p = 1 := by simpa only [d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3429 p hg
    simpa only [d108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3393 p hg
    simpa only [d108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3431 (p : Pattern) (guard : d109 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3393 p hg
    simpa only [d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d108 p = 1 := by simpa only [d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3430 p hg
    simpa only [d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3432 (p : Pattern) (guard : d110 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3393 p hg
    simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d109 p = 1 := by simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3431 p hg
    simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3433 (p : Pattern) (guard : d406 p = 1) : d47700 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d406, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1131 p hg
    simpa only [d406, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d110 p = 1 := by simpa only [d406, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3432 p hg
    simpa only [d406, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3434 (p : Pattern) (guard : d65943 p = 1) : d47700 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 70 with
  | false =>
    have hg : d104 p = 1 := by simpa only [d65943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3426 p hg
    simpa only [d65943, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d406 p = 1 := by simpa only [d65943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3433 p hg
    simpa only [d65943, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3435 (p : Pattern) (guard : d65944 p = 1) : d47700 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 69 with
  | false =>
    have hg : d65943 p = 1 := by simpa only [d65944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3434 p hg
    simpa only [d65944, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d65944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3392 p hg
    simpa only [d65944, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3436 (p : Pattern) (guard : d65945 p = 1) : d47700 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 51 with
  | false =>
    have hg : d65944 p = 1 := by simpa only [d65945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3435 p hg
    simpa only [d65945, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d65945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3392 p hg
    simpa only [d65945, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3437 (p : Pattern) (guard : d65946 p = 1) : d47700 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 50 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d65946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3392 p hg
    simpa only [d65946, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d65945 p = 1 := by simpa only [d65946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3436 p hg
    simpa only [d65946, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3438 (p : Pattern) (guard : d0 p = 1) : d47767 p ≤ (-1 : Int) + d47767 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3439 (p : Pattern) (guard : d65947 p = 1) : d47768 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 49 with
  | false =>
    have hg : d65946 p = 1 := by simpa only [d65947, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3437 p hg
    simpa only [d65947, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d65947, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3438 p hg
    simpa only [d65947, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3440 (p : Pattern) (guard : d0 p = 1) : d47910 p ≤ (-1 : Int) + d47909 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3441 (p : Pattern) (guard : d65948 p = 1) : d47911 p ≤ (-1 : Int) + d65730 p := by
  cases selected : p 48 with
  | false =>
    have hg : d65947 p = 1 := by simpa only [d65948, d47911, d65730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3439 p hg
    simpa only [d65948, d47911, d65730, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d65948, d47911, d65730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3440 p hg
    simpa only [d65948, d47911, d65730, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3442 (p : Pattern) (guard : d65949 p = 1) : d47911 p ≤ (-1 : Int) + d65730 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d65949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3391 p hg
    simpa only [d65949, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d65948 p = 1 := by simpa only [d65949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3441 p hg
    simpa only [d65949, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3443 (p : Pattern) (guard : d65950 p = 1) : d47911 p ≤ (-1 : Int) + d65730 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d65950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3391 p hg
    simpa only [d65950, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d65949 p = 1 := by simpa only [d65950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3442 p hg
    simpa only [d65950, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3444 (p : Pattern) (guard : d65951 p = 1) : d47911 p ≤ (-1 : Int) + d65730 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d65951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3391 p hg
    simpa only [d65951, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d65950 p = 1 := by simpa only [d65951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3443 p hg
    simpa only [d65951, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3445 (p : Pattern) (guard : d65952 p = 1) : d47911 p ≤ (-1 : Int) + d65730 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d65952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3391 p hg
    simpa only [d65952, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d65951 p = 1 := by simpa only [d65952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3444 p hg
    simpa only [d65952, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3446 (p : Pattern) (guard : d65953 p = 1) : d47911 p ≤ (-1 : Int) + d65730 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d65953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3391 p hg
    simpa only [d65953, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d65952 p = 1 := by simpa only [d65953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3445 p hg
    simpa only [d65953, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3447 (p : Pattern) (guard : d139 p = 1) : d47660 p ≤ (-1 : Int) + d47735 p := by
  cases selected : p 163 with
  | false =>
    have hg : d138 p = 1 := by simpa only [d139, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1237 p hg
    simpa only [d139, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d139, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3397 p hg
    simpa only [d139, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3448 (p : Pattern) (guard : d140 p = 1) : d47663 p ≤ (-1 : Int) + d47736 p := by
  cases selected : p 162 with
  | false =>
    have hg : d139 p = 1 := by simpa only [d140, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3447 p hg
    simpa only [d140, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d140, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3399 p hg
    simpa only [d140, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3449 (p : Pattern) (guard : d141 p = 1) : d47664 p ≤ (-1 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d141, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3396 p hg
    simpa only [d141, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d140 p = 1 := by simpa only [d141, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3448 p hg
    simpa only [d141, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3450 (p : Pattern) (guard : d142 p = 1) : d47685 p ≤ (-1 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d141 p = 1 := by simpa only [d142, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3449 p hg
    simpa only [d142, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d142, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3402 p hg
    simpa only [d142, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3451 (p : Pattern) (guard : d143 p = 1) : d47685 p ≤ (-1 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d142 p = 1 := by simpa only [d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3450 p hg
    simpa only [d143, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d28 p = 1 := by simpa only [d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3403 p hg
    simpa only [d143, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3452 (p : Pattern) (guard : d144 p = 1) : d47685 p ≤ (-1 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d143 p = 1 := by simpa only [d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3451 p hg
    simpa only [d144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d29 p = 1 := by simpa only [d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3405 p hg
    simpa only [d144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3453 (p : Pattern) (guard : d145 p = 1) : d47685 p ≤ (-1 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d144 p = 1 := by simpa only [d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3452 p hg
    simpa only [d145, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d30 p = 1 := by simpa only [d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3406 p hg
    simpa only [d145, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3454 (p : Pattern) (guard : d146 p = 1) : d47686 p ≤ (-1 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d146, d47686, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3395 p hg
    simpa only [d146, d47686, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d145 p = 1 := by simpa only [d146, d47686, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3453 p hg
    simpa only [d146, d47686, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3455 (p : Pattern) (guard : d147 p = 1) : d47687 p ≤ (-1 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d147, d47687, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3394 p hg
    simpa only [d147, d47687, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d146 p = 1 := by simpa only [d147, d47687, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3454 p hg
    simpa only [d147, d47687, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3456 (p : Pattern) (guard : d148 p = 1) : d47687 p ≤ (-1 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d147 p = 1 := by simpa only [d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3455 p hg
    simpa only [d148, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d33 p = 1 := by simpa only [d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3409 p hg
    simpa only [d148, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3457 (p : Pattern) (guard : d149 p = 1) : d47687 p ≤ (-1 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d148 p = 1 := by simpa only [d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3456 p hg
    simpa only [d149, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d34 p = 1 := by simpa only [d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3411 p hg
    simpa only [d149, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3458 (p : Pattern) (guard : d150 p = 1) : d47687 p ≤ (-1 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d149 p = 1 := by simpa only [d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3457 p hg
    simpa only [d150, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3410 p hg
    simpa only [d150, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3459 (p : Pattern) (guard : d151 p = 1) : d47699 p ≤ (-1 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d150 p = 1 := by simpa only [d151, d47699, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3458 p hg
    simpa only [d151, d47699, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d151, d47699, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3414 p hg
    simpa only [d151, d47699, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3460 (p : Pattern) (guard : d152 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d152, d47700, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1133 p hg
    simpa only [d152, d47700, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d151 p = 1 := by simpa only [d152, d47700, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3459 p hg
    simpa only [d152, d47700, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3461 (p : Pattern) (guard : d153 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d152 p = 1 := by simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3460 p hg
    simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d38 p = 1 := by simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3416 p hg
    simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3462 (p : Pattern) (guard : d154 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d153 p = 1 := by simpa only [d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3461 p hg
    simpa only [d154, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3393 p hg
    simpa only [d154, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3463 (p : Pattern) (guard : d155 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d154 p = 1 := by simpa only [d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3462 p hg
    simpa only [d155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3393 p hg
    simpa only [d155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3464 (p : Pattern) (guard : d156 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3393 p hg
    simpa only [d156, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d155 p = 1 := by simpa only [d156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3463 p hg
    simpa only [d156, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3465 (p : Pattern) (guard : d157 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d156 p = 1 := by simpa only [d157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3464 p hg
    simpa only [d157, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d42 p = 1 := by simpa only [d157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3420 p hg
    simpa only [d157, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3466 (p : Pattern) (guard : d280 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3393 p hg
    simpa only [d280, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d157 p = 1 := by simpa only [d280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3465 p hg
    simpa only [d280, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3467 (p : Pattern) (guard : d281 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d280 p = 1 := by simpa only [d281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3466 p hg
    simpa only [d281, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3393 p hg
    simpa only [d281, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3468 (p : Pattern) (guard : d282 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3393 p hg
    simpa only [d282, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d281 p = 1 := by simpa only [d282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3467 p hg
    simpa only [d282, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3469 (p : Pattern) (guard : d283 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3393 p hg
    simpa only [d283, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d282 p = 1 := by simpa only [d283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3468 p hg
    simpa only [d283, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3470 (p : Pattern) (guard : d284 p = 1) : d47700 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d284, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1131 p hg
    simpa only [d284, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d283 p = 1 := by simpa only [d284, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3469 p hg
    simpa only [d284, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3471 (p : Pattern) (guard : d203 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d155 p = 1 := by simpa only [d203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3463 p hg
    simpa only [d203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3393 p hg
    simpa only [d203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3472 (p : Pattern) (guard : d204 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d203 p = 1 := by simpa only [d204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3471 p hg
    simpa only [d204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d49 p = 1 := by simpa only [d204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3427 p hg
    simpa only [d204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3473 (p : Pattern) (guard : d287 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3393 p hg
    simpa only [d287, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d204 p = 1 := by simpa only [d287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3472 p hg
    simpa only [d287, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3474 (p : Pattern) (guard : d288 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d287 p = 1 := by simpa only [d288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3473 p hg
    simpa only [d288, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3393 p hg
    simpa only [d288, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3475 (p : Pattern) (guard : d289 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3393 p hg
    simpa only [d289, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d288 p = 1 := by simpa only [d289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3474 p hg
    simpa only [d289, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3476 (p : Pattern) (guard : d290 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3393 p hg
    simpa only [d290, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d289 p = 1 := by simpa only [d290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3475 p hg
    simpa only [d290, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3477 (p : Pattern) (guard : d53655 p = 1) : d47700 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d53655, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1131 p hg
    simpa only [d53655, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d290 p = 1 := by simpa only [d53655, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3476 p hg
    simpa only [d53655, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3478 (p : Pattern) (guard : d65954 p = 1) : d47700 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 70 with
  | false =>
    have hg : d284 p = 1 := by simpa only [d65954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3470 p hg
    simpa only [d65954, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53655 p = 1 := by simpa only [d65954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3477 p hg
    simpa only [d65954, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3479 (p : Pattern) (guard : d65955 p = 1) : d47700 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 69 with
  | false =>
    have hg : d65954 p = 1 := by simpa only [d65955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3478 p hg
    simpa only [d65955, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d65955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3392 p hg
    simpa only [d65955, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3480 (p : Pattern) (guard : d65956 p = 1) : d47700 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 51 with
  | false =>
    have hg : d65955 p = 1 := by simpa only [d65956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3479 p hg
    simpa only [d65956, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d65956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3392 p hg
    simpa only [d65956, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3481 (p : Pattern) (guard : d65957 p = 1) : d47700 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 50 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d65957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3392 p hg
    simpa only [d65957, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d65956 p = 1 := by simpa only [d65957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3480 p hg
    simpa only [d65957, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3482 (p : Pattern) (guard : d65958 p = 1) : d47768 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 49 with
  | false =>
    have hg : d65957 p = 1 := by simpa only [d65958, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3481 p hg
    simpa only [d65958, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d65958, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3438 p hg
    simpa only [d65958, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3483 (p : Pattern) (guard : d65959 p = 1) : d47911 p ≤ (-1 : Int) + d65730 p := by
  cases selected : p 48 with
  | false =>
    have hg : d65958 p = 1 := by simpa only [d65959, d47911, d65730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3482 p hg
    simpa only [d65959, d47911, d65730, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d65959, d47911, d65730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3440 p hg
    simpa only [d65959, d47911, d65730, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3484 (p : Pattern) (guard : d65960 p = 1) : d47911 p ≤ (-1 : Int) + d65730 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d65960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3391 p hg
    simpa only [d65960, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d65959 p = 1 := by simpa only [d65960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3483 p hg
    simpa only [d65960, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3485 (p : Pattern) (guard : d65961 p = 1) : d47911 p ≤ (-1 : Int) + d65730 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d65961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3391 p hg
    simpa only [d65961, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d65960 p = 1 := by simpa only [d65961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3484 p hg
    simpa only [d65961, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3486 (p : Pattern) (guard : d65962 p = 1) : d47911 p ≤ (-1 : Int) + d65730 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d65962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3391 p hg
    simpa only [d65962, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d65961 p = 1 := by simpa only [d65962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3485 p hg
    simpa only [d65962, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3487 (p : Pattern) (guard : d65963 p = 1) : d47911 p ≤ (-1 : Int) + d65730 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d65963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3391 p hg
    simpa only [d65963, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d65962 p = 1 := by simpa only [d65963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3486 p hg
    simpa only [d65963, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3488 (p : Pattern) (guard : d65964 p = 1) : d47911 p ≤ (-1 : Int) + d65730 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d65964, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3391 p hg
    simpa only [d65964, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d65963 p = 1 := by simpa only [d65964, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3487 p hg
    simpa only [d65964, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3489 (p : Pattern) (guard : d65965 p = 1) : d47911 p ≤ (-1 : Int) + d65730 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d65953 p = 1 := by simpa only [d65965, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3446 p hg
    simpa only [d65965, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d65964 p = 1 := by simpa only [d65965, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3488 p hg
    simpa only [d65965, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3490 (p : Pattern) (guard : d319 p = 1) : d47660 p ≤ (-1 : Int) + d47735 p := by
  cases selected : p 163 with
  | false =>
    have hg : d318 p = 1 := by simpa only [d319, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1300 p hg
    simpa only [d319, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d319, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3397 p hg
    simpa only [d319, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3491 (p : Pattern) (guard : d320 p = 1) : d47663 p ≤ (-1 : Int) + d47736 p := by
  cases selected : p 162 with
  | false =>
    have hg : d319 p = 1 := by simpa only [d320, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3490 p hg
    simpa only [d320, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d320, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3399 p hg
    simpa only [d320, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3492 (p : Pattern) (guard : d321 p = 1) : d47664 p ≤ (-1 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d321, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3396 p hg
    simpa only [d321, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d320 p = 1 := by simpa only [d321, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3491 p hg
    simpa only [d321, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3493 (p : Pattern) (guard : d322 p = 1) : d47685 p ≤ (-1 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d321 p = 1 := by simpa only [d322, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3492 p hg
    simpa only [d322, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d322, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3402 p hg
    simpa only [d322, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3494 (p : Pattern) (guard : d323 p = 1) : d47685 p ≤ (-1 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d322 p = 1 := by simpa only [d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3493 p hg
    simpa only [d323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d142 p = 1 := by simpa only [d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3450 p hg
    simpa only [d323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3495 (p : Pattern) (guard : d324 p = 1) : d47685 p ≤ (-1 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d323 p = 1 := by simpa only [d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3494 p hg
    simpa only [d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d143 p = 1 := by simpa only [d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3451 p hg
    simpa only [d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3496 (p : Pattern) (guard : d325 p = 1) : d47685 p ≤ (-1 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d324 p = 1 := by simpa only [d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3495 p hg
    simpa only [d325, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d144 p = 1 := by simpa only [d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3452 p hg
    simpa only [d325, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3497 (p : Pattern) (guard : d326 p = 1) : d47686 p ≤ (-1 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d326, d47686, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3395 p hg
    simpa only [d326, d47686, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325 p = 1 := by simpa only [d326, d47686, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3496 p hg
    simpa only [d326, d47686, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3498 (p : Pattern) (guard : d327 p = 1) : d47687 p ≤ (-1 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d327, d47687, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3394 p hg
    simpa only [d327, d47687, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d326 p = 1 := by simpa only [d327, d47687, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3497 p hg
    simpa only [d327, d47687, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3499 (p : Pattern) (guard : d328 p = 1) : d47687 p ≤ (-1 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d327 p = 1 := by simpa only [d328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3498 p hg
    simpa only [d328, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d147 p = 1 := by simpa only [d328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3455 p hg
    simpa only [d328, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
