/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons288
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare40460 (p : Pattern) (guard : d0 p = 1) : d2197 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare40461 (p : Pattern) (guard : d8111 p = 1) : d2198 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40418 p hg
    simpa only [d8111, d2198, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40460 p hg
    simpa only [d8111, d2198, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40462 (p : Pattern) (guard : d8112 p = 1) : d2202 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40458 p hg
    simpa only [d8112, d2202, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40461 p hg
    simpa only [d8112, d2202, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40463 (p : Pattern) (guard : d8113 p = 1) : d2256 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2256, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40459 p hg
    simpa only [d8113, d2256, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2256, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40462 p hg
    simpa only [d8113, d2256, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40464 (p : Pattern) (guard : d8117 p = 1) : d2206 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40260 p hg
    simpa only [d8117, d2206, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8117, d2206, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40465 (p : Pattern) (guard : d8118 p = 1) : d2207 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40462 p hg
    simpa only [d8118, d2207, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40464 p hg
    simpa only [d8118, d2207, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40466 (p : Pattern) (guard : d8119 p = 1) : d2257 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d2257, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40463 p hg
    simpa only [d8119, d2257, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d2257, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40465 p hg
    simpa only [d8119, d2257, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40467 (p : Pattern) (guard : d0 p = 1) : d2212 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare40468 (p : Pattern) (guard : d8105 p = 1) : d2212 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40245 p hg
    simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40467 p hg
    simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40469 (p : Pattern) (guard : d0 p = 1) : d2213 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare40470 (p : Pattern) (guard : d8111 p = 1) : d2258 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40468 p hg
    simpa only [d8111, d2258, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40469 p hg
    simpa only [d8111, d2258, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40471 (p : Pattern) (guard : d8112 p = 1) : d2259 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40257 p hg
    simpa only [d8112, d2259, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40470 p hg
    simpa only [d8112, d2259, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40472 (p : Pattern) (guard : d8118 p = 1) : d2260 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40471 p hg
    simpa only [d8118, d2260, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40268 p hg
    simpa only [d8118, d2260, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40473 (p : Pattern) (guard : d8124 p = 1) : d2261 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d2261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40472 p hg
    simpa only [d8124, d2261, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d2261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34736 p hg
    simpa only [d8124, d2261, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40474 (p : Pattern) (guard : d8125 p = 1) : d2262 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d2262, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40466 p hg
    simpa only [d8125, d2262, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d2262, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40473 p hg
    simpa only [d8125, d2262, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40475 (p : Pattern) (guard : d8094 p = 1) : d2185 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d2185, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34924 p hg
    simpa only [d8094, d2185, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d2185, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39998 p hg
    simpa only [d8094, d2185, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40476 (p : Pattern) (guard : d8100 p = 1) : d2185 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40475 p hg
    simpa only [d8100, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40412 p hg
    simpa only [d8100, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40477 (p : Pattern) (guard : d8106 p = 1) : d2201 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2201, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40476 p hg
    simpa only [d8106, d2201, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2201, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40457 p hg
    simpa only [d8106, d2201, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40478 (p : Pattern) (guard : d0 p = 1) : d2210 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare40479 (p : Pattern) (guard : d8111 p = 1) : d2232 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40444 p hg
    simpa only [d8111, d2232, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40478 p hg
    simpa only [d8111, d2232, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40480 (p : Pattern) (guard : d8112 p = 1) : d2263 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2263, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40477 p hg
    simpa only [d8112, d2263, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2263, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40479 p hg
    simpa only [d8112, d2263, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40481 (p : Pattern) (guard : d0 p = 1) : d2205 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare40482 (p : Pattern) (guard : d8117 p = 1) : d2234 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40461 p hg
    simpa only [d8117, d2234, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40481 p hg
    simpa only [d8117, d2234, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40483 (p : Pattern) (guard : d8118 p = 1) : d2264 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2264, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40480 p hg
    simpa only [d8118, d2264, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2264, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40482 p hg
    simpa only [d8118, d2264, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40484 (p : Pattern) (guard : d0 p = 1) : d2238 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare40485 (p : Pattern) (guard : d8117 p = 1) : d2239 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40461 p hg
    simpa only [d8117, d2239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40484 p hg
    simpa only [d8117, d2239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40486 (p : Pattern) (guard : d0 p = 1) : d2241 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare40487 (p : Pattern) (guard : d8123 p = 1) : d2242 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d2242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40485 p hg
    simpa only [d8123, d2242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d2242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40486 p hg
    simpa only [d8123, d2242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40488 (p : Pattern) (guard : d8124 p = 1) : d2265 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d2265, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40483 p hg
    simpa only [d8124, d2265, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d2265, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40487 p hg
    simpa only [d8124, d2265, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40489 (p : Pattern) (guard : d8117 p = 1) : d2266 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40470 p hg
    simpa only [d8117, d2266, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8117, d2266, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40490 (p : Pattern) (guard : d8123 p = 1) : d2267 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d2267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40489 p hg
    simpa only [d8123, d2267, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d2267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d2267, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40491 (p : Pattern) (guard : d8129 p = 1) : d2268 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d2268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40490 p hg
    simpa only [d8129, d2268, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d2268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8129, d2268, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40492 (p : Pattern) (guard : d8130 p = 1) : d2269 p ≤ (0 : Int) + d411 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d2269, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40488 p hg
    simpa only [d8130, d2269, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d2269, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40491 p hg
    simpa only [d8130, d2269, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40493 (p : Pattern) (guard : d8131 p = 1) : d2270 p ≤ (0 : Int) + d412 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d2270, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40474 p hg
    simpa only [d8131, d2270, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d2270, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40492 p hg
    simpa only [d8131, d2270, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40494 (p : Pattern) (guard : d8132 p = 1) : d2314 p ≤ (0 : Int) + d413 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d2314, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40456 p hg
    simpa only [d8132, d2314, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d2314, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40493 p hg
    simpa only [d8132, d2314, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40495 (p : Pattern) (guard : d8107 p = 1) : d2201 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40361 p hg
    simpa only [d8107, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40477 p hg
    simpa only [d8107, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40496 (p : Pattern) (guard : d8113 p = 1) : d2256 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2256, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40495 p hg
    simpa only [d8113, d2256, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2256, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40462 p hg
    simpa only [d8113, d2256, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40497 (p : Pattern) (guard : d8119 p = 1) : d2257 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d2257, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40496 p hg
    simpa only [d8119, d2257, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d2257, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40465 p hg
    simpa only [d8119, d2257, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40498 (p : Pattern) (guard : d8125 p = 1) : d2262 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d2262, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40497 p hg
    simpa only [d8125, d2262, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d2262, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40473 p hg
    simpa only [d8125, d2262, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40499 (p : Pattern) (guard : d8094 p = 1) : d2185 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d2185, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35070 p hg
    simpa only [d8094, d2185, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d2185, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39998 p hg
    simpa only [d8094, d2185, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40500 (p : Pattern) (guard : d8100 p = 1) : d2185 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40499 p hg
    simpa only [d8100, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40412 p hg
    simpa only [d8100, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40501 (p : Pattern) (guard : d8106 p = 1) : d2201 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2201, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40500 p hg
    simpa only [d8106, d2201, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2201, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40457 p hg
    simpa only [d8106, d2201, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40502 (p : Pattern) (guard : d8112 p = 1) : d2263 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2263, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40501 p hg
    simpa only [d8112, d2263, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2263, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40479 p hg
    simpa only [d8112, d2263, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40503 (p : Pattern) (guard : d8118 p = 1) : d2264 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2264, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40502 p hg
    simpa only [d8118, d2264, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2264, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40482 p hg
    simpa only [d8118, d2264, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40504 (p : Pattern) (guard : d8124 p = 1) : d2265 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d2265, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40503 p hg
    simpa only [d8124, d2265, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d2265, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40487 p hg
    simpa only [d8124, d2265, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40505 (p : Pattern) (guard : d8130 p = 1) : d2269 p ≤ (0 : Int) + d421 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d2269, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40504 p hg
    simpa only [d8130, d2269, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d2269, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40491 p hg
    simpa only [d8130, d2269, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40506 (p : Pattern) (guard : d8131 p = 1) : d2270 p ≤ (0 : Int) + d422 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d2270, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40498 p hg
    simpa only [d8131, d2270, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d2270, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40505 p hg
    simpa only [d8131, d2270, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40507 (p : Pattern) (guard : d8137 p = 1) : d2294 p ≤ (0 : Int) + d444 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d2294, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40506 p hg
    simpa only [d8137, d2294, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d2294, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36809 p hg
    simpa only [d8137, d2294, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40508 (p : Pattern) (guard : d8138 p = 1) : d2315 p ≤ (0 : Int) + d445 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8132 p = 1 := by simpa only [d8138, d2315, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40494 p hg
    simpa only [d8138, d2315, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8137 p = 1 := by simpa only [d8138, d2315, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40507 p hg
    simpa only [d8138, d2315, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40509 (p : Pattern) (guard : d8139 p = 1) : d2316 p ≤ (0 : Int) + d446 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8133 p = 1 := by simpa only [d8139, d2316, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40405 p hg
    simpa only [d8139, d2316, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8138 p = 1 := by simpa only [d8139, d2316, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40508 p hg
    simpa only [d8139, d2316, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40510 (p : Pattern) (guard : d8140 p = 1) : d2317 p ≤ (0 : Int) + d447 p := by
  cases selected : p 71 with
  | false =>
    have hg : d8134 p = 1 := by simpa only [d8140, d2317, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40292 p hg
    simpa only [d8140, d2317, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8139 p = 1 := by simpa only [d8140, d2317, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40509 p hg
    simpa only [d8140, d2317, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40511 (p : Pattern) (guard : d8087 p = 1) : d2186 p ≤ (0 : Int) + d322 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8087, d2186, d322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39937 p hg
    simpa only [d8087, d2186, d322, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8086 p = 1 := by simpa only [d8087, d2186, d322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40048 p hg
    simpa only [d8087, d2186, d322, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40512 (p : Pattern) (guard : d8091 p = 1) : d2187 p ≤ (0 : Int) + d324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d2187, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40101 p hg
    simpa only [d8091, d2187, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d2187, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34344 p hg
    simpa only [d8091, d2187, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40513 (p : Pattern) (guard : d8092 p = 1) : d2188 p ≤ (0 : Int) + d325 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8087 p = 1 := by simpa only [d8092, d2188, d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40511 p hg
    simpa only [d8092, d2188, d325, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8091 p = 1 := by simpa only [d8092, d2188, d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40512 p hg
    simpa only [d8092, d2188, d325, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40514 (p : Pattern) (guard : d8097 p = 1) : d2192 p ≤ (0 : Int) + d338 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8092 p = 1 := by simpa only [d8097, d2192, d338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40513 p hg
    simpa only [d8097, d2192, d338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8096 p = 1 := by simpa only [d8097, d2192, d338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40328 p hg
    simpa only [d8097, d2192, d338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40515 (p : Pattern) (guard : d8102 p = 1) : d2199 p ≤ (0 : Int) + d346 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d2199, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40302 p hg
    simpa only [d8102, d2199, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d2199, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40335 p hg
    simpa only [d8102, d2199, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40516 (p : Pattern) (guard : d8103 p = 1) : d2200 p ≤ (0 : Int) + d347 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8097 p = 1 := by simpa only [d8103, d2200, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40514 p hg
    simpa only [d8103, d2200, d347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8102 p = 1 := by simpa only [d8103, d2200, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40515 p hg
    simpa only [d8103, d2200, d347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40517 (p : Pattern) (guard : d8107 p = 1) : d2206 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2206, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40031 p hg
    simpa only [d8107, d2206, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2206, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34455 p hg
    simpa only [d8107, d2206, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40518 (p : Pattern) (guard : d8108 p = 1) : d2207 p ≤ (0 : Int) + d362 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d2207, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40307 p hg
    simpa only [d8108, d2207, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d2207, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40517 p hg
    simpa only [d8108, d2207, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40519 (p : Pattern) (guard : d8109 p = 1) : d2208 p ≤ (0 : Int) + d363 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8103 p = 1 := by simpa only [d8109, d2208, d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40516 p hg
    simpa only [d8109, d2208, d363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8108 p = 1 := by simpa only [d8109, d2208, d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40518 p hg
    simpa only [d8109, d2208, d363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40520 (p : Pattern) (guard : d8096 p = 1) : d2211 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d2211, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40143 p hg
    simpa only [d8096, d2211, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d2211, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40022 p hg
    simpa only [d8096, d2211, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40521 (p : Pattern) (guard : d8102 p = 1) : d2215 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d2215, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40520 p hg
    simpa only [d8102, d2215, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d2215, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40347 p hg
    simpa only [d8102, d2215, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40522 (p : Pattern) (guard : d8101 p = 1) : d2218 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2218, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40254 p hg
    simpa only [d8101, d2218, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2218, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40043 p hg
    simpa only [d8101, d2218, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40523 (p : Pattern) (guard : d8107 p = 1) : d2220 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2220, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40522 p hg
    simpa only [d8107, d2220, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2220, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40184 p hg
    simpa only [d8107, d2220, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40524 (p : Pattern) (guard : d8108 p = 1) : d2221 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d2221, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40521 p hg
    simpa only [d8108, d2221, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d2221, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40523 p hg
    simpa only [d8108, d2221, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40525 (p : Pattern) (guard : d8101 p = 1) : d2222 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2222, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40209 p hg
    simpa only [d8101, d2222, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2222, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34443 p hg
    simpa only [d8101, d2222, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40526 (p : Pattern) (guard : d8107 p = 1) : d2223 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2223, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40525 p hg
    simpa only [d8107, d2223, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2223, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40184 p hg
    simpa only [d8107, d2223, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40527 (p : Pattern) (guard : d8113 p = 1) : d2226 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2226, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40526 p hg
    simpa only [d8113, d2226, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2226, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40189 p hg
    simpa only [d8113, d2226, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40528 (p : Pattern) (guard : d8114 p = 1) : d2227 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d2227, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40524 p hg
    simpa only [d8114, d2227, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d2227, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40527 p hg
    simpa only [d8114, d2227, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40529 (p : Pattern) (guard : d8115 p = 1) : d2228 p ≤ (0 : Int) + d377 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8109 p = 1 := by simpa only [d8115, d2228, d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40519 p hg
    simpa only [d8115, d2228, d377, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8114 p = 1 := by simpa only [d8115, d2228, d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40528 p hg
    simpa only [d8115, d2228, d377, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40530 (p : Pattern) (guard : d8085 p = 1) : d357 p ≤ (0 : Int) + d357 p := by
  omega
theorem compare40531 (p : Pattern) (guard : d8086 p = 1) : d2229 p ≤ (0 : Int) + d381 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d2229, d381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34462 p hg
    simpa only [d8086, d2229, d381, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d2229, d381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40530 p hg
    simpa only [d8086, d2229, d381, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40532 (p : Pattern) (guard : d8091 p = 1) : d2230 p ≤ (0 : Int) + d382 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d2230, d382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40531 p hg
    simpa only [d8091, d2230, d382, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d2230, d382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40253 p hg
    simpa only [d8091, d2230, d382, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40533 (p : Pattern) (guard : d8095 p = 1) : d2187 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2187, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40282 p hg
    simpa only [d8095, d2187, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2187, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34367 p hg
    simpa only [d8095, d2187, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40534 (p : Pattern) (guard : d8096 p = 1) : d2231 p ≤ (0 : Int) + d383 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d2231, d383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40532 p hg
    simpa only [d8096, d2231, d383, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d2231, d383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40533 p hg
    simpa only [d8096, d2231, d383, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40535 (p : Pattern) (guard : d8090 p = 1) : d2209 p ≤ (0 : Int) + d350 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d2209, d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34969 p hg
    simpa only [d8090, d2209, d350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d2209, d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39959 p hg
    simpa only [d8090, d2209, d350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40536 (p : Pattern) (guard : d8095 p = 1) : d2209 p ≤ (0 : Int) + d351 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40535 p hg
    simpa only [d8095, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40052 p hg
    simpa only [d8095, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40537 (p : Pattern) (guard : d8101 p = 1) : d2232 p ≤ (0 : Int) + d352 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2232, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40536 p hg
    simpa only [d8101, d2232, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2232, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40106 p hg
    simpa only [d8101, d2232, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40538 (p : Pattern) (guard : d8102 p = 1) : d2233 p ≤ (0 : Int) + d384 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d2233, d384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40534 p hg
    simpa only [d8102, d2233, d384, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d2233, d384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40537 p hg
    simpa only [d8102, d2233, d384, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40539 (p : Pattern) (guard : d8090 p = 1) : d2196 p ≤ (0 : Int) + d366 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d2196, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34974 p hg
    simpa only [d8090, d2196, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d2196, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39959 p hg
    simpa only [d8090, d2196, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40540 (p : Pattern) (guard : d8095 p = 1) : d2196 p ≤ (0 : Int) + d367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40539 p hg
    simpa only [d8095, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39999 p hg
    simpa only [d8095, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40541 (p : Pattern) (guard : d8101 p = 1) : d2198 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2198, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40540 p hg
    simpa only [d8101, d2198, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2198, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40077 p hg
    simpa only [d8101, d2198, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40542 (p : Pattern) (guard : d8094 p = 1) : d2203 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d2203, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34979 p hg
    simpa only [d8094, d2203, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d2203, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39998 p hg
    simpa only [d8094, d2203, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40543 (p : Pattern) (guard : d8100 p = 1) : d2203 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40542 p hg
    simpa only [d8100, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40056 p hg
    simpa only [d8100, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40544 (p : Pattern) (guard : d8106 p = 1) : d2205 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2205, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40543 p hg
    simpa only [d8106, d2205, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2205, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40112 p hg
    simpa only [d8106, d2205, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40545 (p : Pattern) (guard : d8107 p = 1) : d2234 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2234, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40541 p hg
    simpa only [d8107, d2234, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2234, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40544 p hg
    simpa only [d8107, d2234, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40546 (p : Pattern) (guard : d8108 p = 1) : d2235 p ≤ (0 : Int) + d385 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d2235, d385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40538 p hg
    simpa only [d8108, d2235, d385, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d2235, d385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40545 p hg
    simpa only [d8108, d2235, d385, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40547 (p : Pattern) (guard : d8094 p = 1) : d2236 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d2236, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34986 p hg
    simpa only [d8094, d2236, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d2236, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39998 p hg
    simpa only [d8094, d2236, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40548 (p : Pattern) (guard : d8100 p = 1) : d2236 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40547 p hg
    simpa only [d8100, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40061 p hg
    simpa only [d8100, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40549 (p : Pattern) (guard : d8106 p = 1) : d2238 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2238, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40548 p hg
    simpa only [d8106, d2238, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2238, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40116 p hg
    simpa only [d8106, d2238, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40550 (p : Pattern) (guard : d8107 p = 1) : d2239 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2239, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40335 p hg
    simpa only [d8107, d2239, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2239, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40549 p hg
    simpa only [d8107, d2239, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40551 (p : Pattern) (guard : d8094 p = 1) : d2216 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d2216, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34992 p hg
    simpa only [d8094, d2216, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d2216, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39998 p hg
    simpa only [d8094, d2216, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40552 (p : Pattern) (guard : d8100 p = 1) : d2216 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40551 p hg
    simpa only [d8100, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40065 p hg
    simpa only [d8100, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40553 (p : Pattern) (guard : d8106 p = 1) : d2240 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2240, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40552 p hg
    simpa only [d8106, d2240, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2240, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40119 p hg
    simpa only [d8106, d2240, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40554 (p : Pattern) (guard : d8112 p = 1) : d2241 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2241, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40553 p hg
    simpa only [d8112, d2241, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2241, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34543 p hg
    simpa only [d8112, d2241, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40555 (p : Pattern) (guard : d8113 p = 1) : d2242 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2242, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40550 p hg
    simpa only [d8113, d2242, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2242, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40554 p hg
    simpa only [d8113, d2242, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40556 (p : Pattern) (guard : d8114 p = 1) : d2243 p ≤ (0 : Int) + d388 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d2243, d388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40546 p hg
    simpa only [d8114, d2243, d388, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d2243, d388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40555 p hg
    simpa only [d8114, d2243, d388, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40557 (p : Pattern) (guard : d8101 p = 1) : d2214 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2214, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40360 p hg
    simpa only [d8101, d2214, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2214, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40092 p hg
    simpa only [d8101, d2214, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40558 (p : Pattern) (guard : d8106 p = 1) : d2244 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2244, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40363 p hg
    simpa only [d8106, d2244, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2244, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34532 p hg
    simpa only [d8106, d2244, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40559 (p : Pattern) (guard : d8107 p = 1) : d2245 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2245, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40557 p hg
    simpa only [d8107, d2245, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2245, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40558 p hg
    simpa only [d8107, d2245, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40560 (p : Pattern) (guard : d8113 p = 1) : d2247 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2247, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40559 p hg
    simpa only [d8113, d2247, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2247, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40218 p hg
    simpa only [d8113, d2247, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40561 (p : Pattern) (guard : d8119 p = 1) : d2253 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d2253, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40560 p hg
    simpa only [d8119, d2253, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d2253, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40228 p hg
    simpa only [d8119, d2253, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40562 (p : Pattern) (guard : d8120 p = 1) : d2254 p ≤ (0 : Int) + d392 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d2254, d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40556 p hg
    simpa only [d8120, d2254, d392, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d2254, d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40561 p hg
    simpa only [d8120, d2254, d392, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40563 (p : Pattern) (guard : d8121 p = 1) : d2255 p ≤ (0 : Int) + d393 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8115 p = 1 := by simpa only [d8121, d2255, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40529 p hg
    simpa only [d8121, d2255, d393, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8120 p = 1 := by simpa only [d8121, d2255, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40562 p hg
    simpa only [d8121, d2255, d393, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40564 (p : Pattern) (guard : d8127 p = 1) : d2271 p ≤ (0 : Int) + d401 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8121 p = 1 := by simpa only [d8127, d2271, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40563 p hg
    simpa only [d8127, d2271, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8126 p = 1 := by simpa only [d8127, d2271, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40395 p hg
    simpa only [d8127, d2271, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40565 (p : Pattern) (guard : d8107 p = 1) : d2259 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2259, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40107 p hg
    simpa only [d8107, d2259, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2259, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40248 p hg
    simpa only [d8107, d2259, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40566 (p : Pattern) (guard : d8113 p = 1) : d2260 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2260, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40565 p hg
    simpa only [d8113, d2260, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2260, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40121 p hg
    simpa only [d8113, d2260, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40567 (p : Pattern) (guard : d8119 p = 1) : d2261 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d2261, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40566 p hg
    simpa only [d8119, d2261, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d2261, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34613 p hg
    simpa only [d8119, d2261, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40568 (p : Pattern) (guard : d8120 p = 1) : d2275 p ≤ (0 : Int) + d406 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d2275, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40410 p hg
    simpa only [d8120, d2275, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d2275, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40567 p hg
    simpa only [d8120, d2275, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40569 (p : Pattern) (guard : d8125 p = 1) : d2269 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d2269, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40442 p hg
    simpa only [d8125, d2269, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d2269, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40273 p hg
    simpa only [d8125, d2269, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40570 (p : Pattern) (guard : d8126 p = 1) : d2276 p ≤ (0 : Int) + d408 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d2276, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40568 p hg
    simpa only [d8126, d2276, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d2276, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40569 p hg
    simpa only [d8126, d2276, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40571 (p : Pattern) (guard : d8107 p = 1) : d2277 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2277, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40031 p hg
    simpa only [d8107, d2277, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2277, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40120 p hg
    simpa only [d8107, d2277, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40572 (p : Pattern) (guard : d8113 p = 1) : d2278 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2278, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40571 p hg
    simpa only [d8113, d2278, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2278, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40121 p hg
    simpa only [d8113, d2278, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40573 (p : Pattern) (guard : d8119 p = 1) : d2280 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d2280, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40572 p hg
    simpa only [d8119, d2280, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d2280, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40398 p hg
    simpa only [d8119, d2280, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40574 (p : Pattern) (guard : d8125 p = 1) : d2282 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d2282, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40573 p hg
    simpa only [d8125, d2282, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d2282, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40400 p hg
    simpa only [d8125, d2282, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40575 (p : Pattern) (guard : d8118 p = 1) : d2279 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2279, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40554 p hg
    simpa only [d8118, d2279, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2279, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34734 p hg
    simpa only [d8118, d2279, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40576 (p : Pattern) (guard : d8124 p = 1) : d2281 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d2281, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40575 p hg
    simpa only [d8124, d2281, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d2281, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34736 p hg
    simpa only [d8124, d2281, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40577 (p : Pattern) (guard : d8130 p = 1) : d2283 p ≤ (0 : Int) + d411 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d2283, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40576 p hg
    simpa only [d8130, d2283, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d2283, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36647 p hg
    simpa only [d8130, d2283, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40578 (p : Pattern) (guard : d8131 p = 1) : d2284 p ≤ (0 : Int) + d412 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d2284, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40574 p hg
    simpa only [d8131, d2284, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d2284, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40577 p hg
    simpa only [d8131, d2284, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40579 (p : Pattern) (guard : d8132 p = 1) : d2285 p ≤ (0 : Int) + d413 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d2285, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40570 p hg
    simpa only [d8132, d2285, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d2285, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40578 p hg
    simpa only [d8132, d2285, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40580 (p : Pattern) (guard : d8133 p = 1) : d2286 p ≤ (0 : Int) + d414 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8127 p = 1 := by simpa only [d8133, d2286, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40564 p hg
    simpa only [d8133, d2286, d414, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8132 p = 1 := by simpa only [d8133, d2286, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40579 p hg
    simpa only [d8133, d2286, d414, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40581 (p : Pattern) (guard : d8102 p = 1) : d2287 p ≤ (0 : Int) + d415 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d2287, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40328 p hg
    simpa only [d8102, d2287, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d2287, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40430 p hg
    simpa only [d8102, d2287, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40582 (p : Pattern) (guard : d8107 p = 1) : d2202 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2202, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40383 p hg
    simpa only [d8107, d2202, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2202, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40437 p hg
    simpa only [d8107, d2202, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40583 (p : Pattern) (guard : d8108 p = 1) : d2288 p ≤ (0 : Int) + d416 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d2288, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40581 p hg
    simpa only [d8108, d2288, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d2288, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40582 p hg
    simpa only [d8108, d2288, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40584 (p : Pattern) (guard : d8113 p = 1) : d2207 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2207, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40407 p hg
    simpa only [d8113, d2207, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2207, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40240 p hg
    simpa only [d8113, d2207, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40585 (p : Pattern) (guard : d8114 p = 1) : d2289 p ≤ (0 : Int) + d417 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d2289, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40583 p hg
    simpa only [d8114, d2289, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d2289, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40584 p hg
    simpa only [d8114, d2289, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40586 (p : Pattern) (guard : d8101 p = 1) : d2211 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2211, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40283 p hg
    simpa only [d8101, d2211, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2211, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40106 p hg
    simpa only [d8101, d2211, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40587 (p : Pattern) (guard : d8107 p = 1) : d2215 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2215, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40586 p hg
    simpa only [d8107, d2215, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2215, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40414 p hg
    simpa only [d8107, d2215, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40588 (p : Pattern) (guard : d8113 p = 1) : d2221 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2221, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40587 p hg
    simpa only [d8113, d2221, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2221, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40420 p hg
    simpa only [d8113, d2221, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40589 (p : Pattern) (guard : d8119 p = 1) : d2227 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d2227, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40588 p hg
    simpa only [d8119, d2227, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d2227, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40425 p hg
    simpa only [d8119, d2227, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40590 (p : Pattern) (guard : d8120 p = 1) : d2290 p ≤ (0 : Int) + d418 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d2290, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40585 p hg
    simpa only [d8120, d2290, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d2290, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40589 p hg
    simpa only [d8120, d2290, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40591 (p : Pattern) (guard : d8090 p = 1) : d2185 p ≤ (0 : Int) + d350 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d2185, d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35039 p hg
    simpa only [d8090, d2185, d350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d2185, d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39959 p hg
    simpa only [d8090, d2185, d350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40592 (p : Pattern) (guard : d8095 p = 1) : d2185 p ≤ (0 : Int) + d351 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40591 p hg
    simpa only [d8095, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40177 p hg
    simpa only [d8095, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40593 (p : Pattern) (guard : d8101 p = 1) : d2201 p ≤ (0 : Int) + d352 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2201, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40592 p hg
    simpa only [d8101, d2201, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2201, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40232 p hg
    simpa only [d8101, d2201, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40594 (p : Pattern) (guard : d8094 p = 1) : d2209 p ≤ (0 : Int) + d321 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d2209, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35044 p hg
    simpa only [d8094, d2209, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d2209, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39998 p hg
    simpa only [d8094, d2209, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40595 (p : Pattern) (guard : d8100 p = 1) : d2209 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40594 p hg
    simpa only [d8100, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40211 p hg
    simpa only [d8100, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40596 (p : Pattern) (guard : d8106 p = 1) : d2232 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2232, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40595 p hg
    simpa only [d8106, d2232, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2232, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40256 p hg
    simpa only [d8106, d2232, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40597 (p : Pattern) (guard : d8107 p = 1) : d2263 p ≤ (0 : Int) + d355 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2263, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40593 p hg
    simpa only [d8107, d2263, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2263, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40596 p hg
    simpa only [d8107, d2263, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40598 (p : Pattern) (guard : d8094 p = 1) : d2196 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d2196, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35050 p hg
    simpa only [d8094, d2196, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d2196, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39998 p hg
    simpa only [d8094, d2196, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40599 (p : Pattern) (guard : d8100 p = 1) : d2196 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40598 p hg
    simpa only [d8100, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40182 p hg
    simpa only [d8100, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
