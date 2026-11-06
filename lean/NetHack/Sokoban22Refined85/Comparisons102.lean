/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons101
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare14280 (p : Pattern) (guard : d4902 p = 1) : d79 p ≤ (0 : Int) + d2259 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d79, d2259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14253 p hg
    simpa only [d79, d2259, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d79, d2259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14279 p hg
    simpa only [d79, d2259, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14281 (p : Pattern) (guard : d4902 p = 1) : d80 p ≤ (0 : Int) + d2260 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d80, d2260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14280 p hg
    simpa only [d80, d2260, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d80, d2260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14262 p hg
    simpa only [d80, d2260, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14282 (p : Pattern) (guard : d4902 p = 1) : d81 p ≤ (0 : Int) + d2261 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d81, d2261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14281 p hg
    simpa only [d81, d2261, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d81, d2261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d81, d2261, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14283 (p : Pattern) (guard : d4902 p = 1) : d82 p ≤ (0 : Int) + d2262 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d82, d2262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14278 p hg
    simpa only [d82, d2262, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d82, d2262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14282 p hg
    simpa only [d82, d2262, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14284 (p : Pattern) (guard : d4902 p = 1) : d54 p ≤ (0 : Int) + d2263 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d54, d2263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14221 p hg
    simpa only [d54, d2263, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d54, d2263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14253 p hg
    simpa only [d54, d2263, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14285 (p : Pattern) (guard : d4902 p = 1) : d56 p ≤ (0 : Int) + d2264 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d56, d2264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14284 p hg
    simpa only [d56, d2264, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d56, d2264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14255 p hg
    simpa only [d56, d2264, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14286 (p : Pattern) (guard : d4902 p = 1) : d65 p ≤ (0 : Int) + d2265 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d65, d2265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14285 p hg
    simpa only [d65, d2265, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d65, d2265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14263 p hg
    simpa only [d65, d2265, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14287 (p : Pattern) (guard : d4902 p = 1) : d83 p ≤ (0 : Int) + d2266 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d83, d2266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14279 p hg
    simpa only [d83, d2266, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d83, d2266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d83, d2266, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14288 (p : Pattern) (guard : d4902 p = 1) : d84 p ≤ (0 : Int) + d2267 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d84, d2267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14287 p hg
    simpa only [d84, d2267, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d84, d2267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d84, d2267, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14289 (p : Pattern) (guard : d4902 p = 1) : d85 p ≤ (0 : Int) + d2268 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d85, d2268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14288 p hg
    simpa only [d85, d2268, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d85, d2268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d85, d2268, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14290 (p : Pattern) (guard : d4902 p = 1) : d86 p ≤ (0 : Int) + d2269 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d86, d2269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14286 p hg
    simpa only [d86, d2269, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d86, d2269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14289 p hg
    simpa only [d86, d2269, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14291 (p : Pattern) (guard : d4902 p = 1) : d87 p ≤ (0 : Int) + d2270 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d87, d2270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14283 p hg
    simpa only [d87, d2270, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d87, d2270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14290 p hg
    simpa only [d87, d2270, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14292 (p : Pattern) (guard : d4902 p = 1) : d88 p ≤ (0 : Int) + d2271 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d88, d2271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14276 p hg
    simpa only [d88, d2271, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d88, d2271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14291 p hg
    simpa only [d88, d2271, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14293 (p : Pattern) (guard : d4902 p = 1) : d16 p ≤ (0 : Int) + d2272 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14215 p hg
    simpa only [d2272, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14221 p hg
    simpa only [d2272, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14294 (p : Pattern) (guard : d4902 p = 1) : d22 p ≤ (0 : Int) + d2273 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d22, d2273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14293 p hg
    simpa only [d22, d2273, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d22, d2273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14222 p hg
    simpa only [d22, d2273, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14295 (p : Pattern) (guard : d4902 p = 1) : d29 p ≤ (0 : Int) + d2274 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d29, d2274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14294 p hg
    simpa only [d29, d2274, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d29, d2274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14227 p hg
    simpa only [d29, d2274, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14296 (p : Pattern) (guard : d4902 p = 1) : d82 p ≤ (0 : Int) + d2275 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d82, d2275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14295 p hg
    simpa only [d82, d2275, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d82, d2275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14282 p hg
    simpa only [d82, d2275, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14297 (p : Pattern) (guard : d4902 p = 1) : d87 p ≤ (0 : Int) + d2276 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d87, d2276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14296 p hg
    simpa only [d87, d2276, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d87, d2276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14290 p hg
    simpa only [d87, d2276, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14298 (p : Pattern) (guard : d4902 p = 1) : d89 p ≤ (0 : Int) + d2277 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d89, d2277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14225 p hg
    simpa only [d89, d2277, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d89, d2277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14261 p hg
    simpa only [d89, d2277, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14299 (p : Pattern) (guard : d4902 p = 1) : d90 p ≤ (0 : Int) + d2278 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d90, d2278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14298 p hg
    simpa only [d90, d2278, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d90, d2278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14262 p hg
    simpa only [d90, d2278, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14300 (p : Pattern) (guard : d4902 p = 1) : d91 p ≤ (0 : Int) + d2279 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d91, d2279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14262 p hg
    simpa only [d91, d2279, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d91, d2279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d91, d2279, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14301 (p : Pattern) (guard : d4902 p = 1) : d92 p ≤ (0 : Int) + d2280 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d92, d2280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14299 p hg
    simpa only [d92, d2280, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d92, d2280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14300 p hg
    simpa only [d92, d2280, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14302 (p : Pattern) (guard : d4902 p = 1) : d93 p ≤ (0 : Int) + d2281 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d93, d2281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14300 p hg
    simpa only [d93, d2281, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d93, d2281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d93, d2281, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14303 (p : Pattern) (guard : d4902 p = 1) : d94 p ≤ (0 : Int) + d2282 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d94, d2282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14301 p hg
    simpa only [d94, d2282, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d94, d2282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14302 p hg
    simpa only [d94, d2282, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14304 (p : Pattern) (guard : d4902 p = 1) : d95 p ≤ (0 : Int) + d2283 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d95, d2283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14302 p hg
    simpa only [d95, d2283, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d95, d2283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d95, d2283, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14305 (p : Pattern) (guard : d4902 p = 1) : d96 p ≤ (0 : Int) + d2284 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d96, d2284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14303 p hg
    simpa only [d96, d2284, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d96, d2284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14304 p hg
    simpa only [d96, d2284, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14306 (p : Pattern) (guard : d4902 p = 1) : d97 p ≤ (0 : Int) + d2285 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d97, d2285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14297 p hg
    simpa only [d97, d2285, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d97, d2285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14305 p hg
    simpa only [d97, d2285, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14307 (p : Pattern) (guard : d4902 p = 1) : d98 p ≤ (0 : Int) + d2286 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d98, d2286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14292 p hg
    simpa only [d98, d2286, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d98, d2286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14306 p hg
    simpa only [d98, d2286, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14308 (p : Pattern) (guard : d4902 p = 1) : d16 p ≤ (0 : Int) + d2287 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14210 p hg
    simpa only [d2287, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14221 p hg
    simpa only [d2287, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14309 (p : Pattern) (guard : d4902 p = 1) : d22 p ≤ (0 : Int) + d2288 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d22, d2288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14308 p hg
    simpa only [d22, d2288, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d22, d2288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14222 p hg
    simpa only [d22, d2288, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14310 (p : Pattern) (guard : d4902 p = 1) : d29 p ≤ (0 : Int) + d2289 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d29, d2289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14309 p hg
    simpa only [d29, d2289, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d29, d2289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14227 p hg
    simpa only [d29, d2289, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14311 (p : Pattern) (guard : d4902 p = 1) : d52 p ≤ (0 : Int) + d2290 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d52, d2290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14310 p hg
    simpa only [d52, d2290, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d52, d2290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14247 p hg
    simpa only [d52, d2290, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14312 (p : Pattern) (guard : d4902 p = 1) : d76 p ≤ (0 : Int) + d2291 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d76, d2291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14286 p hg
    simpa only [d76, d2291, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d76, d2291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14274 p hg
    simpa only [d76, d2291, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14313 (p : Pattern) (guard : d4902 p = 1) : d77 p ≤ (0 : Int) + d2292 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d77, d2292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14311 p hg
    simpa only [d77, d2292, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d77, d2292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14312 p hg
    simpa only [d77, d2292, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14314 (p : Pattern) (guard : d4902 p = 1) : d88 p ≤ (0 : Int) + d2293 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d88, d2293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14313 p hg
    simpa only [d88, d2293, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d88, d2293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14291 p hg
    simpa only [d88, d2293, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14315 (p : Pattern) (guard : d4902 p = 1) : d99 p ≤ (0 : Int) + d2294 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d99, d2294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14291 p hg
    simpa only [d99, d2294, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d99, d2294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d99, d2294, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14316 (p : Pattern) (guard : d4902 p = 1) : d100 p ≤ (0 : Int) + d2295 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d100, d2295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14314 p hg
    simpa only [d100, d2295, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d100, d2295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14315 p hg
    simpa only [d100, d2295, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14317 (p : Pattern) (guard : d4902 p = 1) : d101 p ≤ (0 : Int) + d2296 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d101, d2296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14307 p hg
    simpa only [d101, d2296, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d101, d2296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14316 p hg
    simpa only [d101, d2296, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14318 (p : Pattern) (guard : d0 p = 1) : d14 p ≤ (0 : Int) + d320 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare14319 (p : Pattern) (guard : d4902 p = 1) : d14 p ≤ (0 : Int) + d2297 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4902, d2297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1207 p hg
    simpa only [d4902, d2297, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4902, d2297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14318 p hg
    simpa only [d4902, d2297, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14320 (p : Pattern) (guard : d4902 p = 1) : d14 p ≤ (0 : Int) + d2298 p := by
  cases selected : p 204 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14319 p hg
    simpa only [d2298, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14202 p hg
    simpa only [d2298, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14321 (p : Pattern) (guard : d4902 p = 1) : d16 p ≤ (0 : Int) + d2299 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d16, d2299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14320 p hg
    simpa only [d16, d2299, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d16, d2299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14205 p hg
    simpa only [d16, d2299, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14322 (p : Pattern) (guard : d4902 p = 1) : d16 p ≤ (0 : Int) + d2300 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14321 p hg
    simpa only [d2300, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14215 p hg
    simpa only [d2300, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14323 (p : Pattern) (guard : d4902 p = 1) : d22 p ≤ (0 : Int) + d2301 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d22, d2301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14322 p hg
    simpa only [d22, d2301, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d22, d2301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14222 p hg
    simpa only [d22, d2301, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14324 (p : Pattern) (guard : d4902 p = 1) : d29 p ≤ (0 : Int) + d2302 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d29, d2302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14323 p hg
    simpa only [d29, d2302, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d29, d2302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14227 p hg
    simpa only [d29, d2302, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14325 (p : Pattern) (guard : d4902 p = 1) : d52 p ≤ (0 : Int) + d2303 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d52, d2303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14324 p hg
    simpa only [d52, d2303, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d52, d2303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14247 p hg
    simpa only [d52, d2303, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14326 (p : Pattern) (guard : d4902 p = 1) : d54 p ≤ (0 : Int) + d2304 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d54, d2304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14210 p hg
    simpa only [d54, d2304, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d54, d2304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14253 p hg
    simpa only [d54, d2304, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14327 (p : Pattern) (guard : d4902 p = 1) : d56 p ≤ (0 : Int) + d2305 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d56, d2305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14326 p hg
    simpa only [d56, d2305, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d56, d2305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14255 p hg
    simpa only [d56, d2305, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14328 (p : Pattern) (guard : d4902 p = 1) : d65 p ≤ (0 : Int) + d2306 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d65, d2306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14327 p hg
    simpa only [d65, d2306, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d65, d2306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14263 p hg
    simpa only [d65, d2306, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14329 (p : Pattern) (guard : d4902 p = 1) : d76 p ≤ (0 : Int) + d2307 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d76, d2307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14328 p hg
    simpa only [d76, d2307, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d76, d2307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14274 p hg
    simpa only [d76, d2307, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14330 (p : Pattern) (guard : d4902 p = 1) : d77 p ≤ (0 : Int) + d2308 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d77, d2308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14325 p hg
    simpa only [d77, d2308, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d77, d2308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14329 p hg
    simpa only [d77, d2308, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14331 (p : Pattern) (guard : d4902 p = 1) : d88 p ≤ (0 : Int) + d2309 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d88, d2309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14330 p hg
    simpa only [d88, d2309, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d88, d2309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14291 p hg
    simpa only [d88, d2309, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14332 (p : Pattern) (guard : d4902 p = 1) : d97 p ≤ (0 : Int) + d2310 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d97, d2310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14291 p hg
    simpa only [d97, d2310, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d97, d2310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14305 p hg
    simpa only [d97, d2310, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14333 (p : Pattern) (guard : d4902 p = 1) : d98 p ≤ (0 : Int) + d2311 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d98, d2311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14331 p hg
    simpa only [d98, d2311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d98, d2311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14332 p hg
    simpa only [d98, d2311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14334 (p : Pattern) (guard : d4902 p = 1) : d52 p ≤ (0 : Int) + d2312 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d52, d2312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14295 p hg
    simpa only [d52, d2312, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d52, d2312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14247 p hg
    simpa only [d52, d2312, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14335 (p : Pattern) (guard : d4902 p = 1) : d77 p ≤ (0 : Int) + d2313 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d77, d2313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14334 p hg
    simpa only [d77, d2313, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d77, d2313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14312 p hg
    simpa only [d77, d2313, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14336 (p : Pattern) (guard : d4902 p = 1) : d88 p ≤ (0 : Int) + d2314 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d88, d2314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14335 p hg
    simpa only [d88, d2314, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d88, d2314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14291 p hg
    simpa only [d88, d2314, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14337 (p : Pattern) (guard : d4902 p = 1) : d100 p ≤ (0 : Int) + d2315 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d100, d2315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14336 p hg
    simpa only [d100, d2315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d100, d2315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14315 p hg
    simpa only [d100, d2315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14338 (p : Pattern) (guard : d4902 p = 1) : d101 p ≤ (0 : Int) + d2316 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d101, d2316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14333 p hg
    simpa only [d101, d2316, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d101, d2316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14337 p hg
    simpa only [d101, d2316, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14339 (p : Pattern) (guard : d4902 p = 1) : d101 p ≤ (0 : Int) + d2317 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14317 p hg
    simpa only [d2317, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14338 p hg
    simpa only [d2317, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14340 (p : Pattern) (guard : d0 p = 1) : d103 p ≤ (0 : Int) + d320 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare14341 (p : Pattern) (guard : d4902 p = 1) : d103 p ≤ (0 : Int) + d2318 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4902, d2318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1274 p hg
    simpa only [d4902, d2318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4902, d2318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14340 p hg
    simpa only [d4902, d2318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14342 (p : Pattern) (guard : d4902 p = 1) : d103 p ≤ (0 : Int) + d2319 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4902, d2319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1274 p hg
    simpa only [d4902, d2319, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4902, d2319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11610 p hg
    simpa only [d4902, d2319, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14343 (p : Pattern) (guard : d4902 p = 1) : d103 p ≤ (0 : Int) + d2320 p := by
  cases selected : p 204 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14341 p hg
    simpa only [d2320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14342 p hg
    simpa only [d2320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14344 (p : Pattern) (guard : d4902 p = 1) : d104 p ≤ (0 : Int) + d2321 p := by
  cases selected : p 204 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d104, d2321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14342 p hg
    simpa only [d104, d2321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d104, d2321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d104, d2321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14345 (p : Pattern) (guard : d4902 p = 1) : d105 p ≤ (0 : Int) + d2322 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d105, d2322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14343 p hg
    simpa only [d105, d2322, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d105, d2322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14344 p hg
    simpa only [d105, d2322, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14346 (p : Pattern) (guard : d0 p = 1) : d103 p ≤ (0 : Int) + d332 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare14347 (p : Pattern) (guard : d4902 p = 1) : d103 p ≤ (0 : Int) + d2323 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4902, d2323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1274 p hg
    simpa only [d4902, d2323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4902, d2323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14346 p hg
    simpa only [d4902, d2323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14348 (p : Pattern) (guard : d4902 p = 1) : d103 p ≤ (0 : Int) + d2324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14347 p hg
    simpa only [d2324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14342 p hg
    simpa only [d2324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14349 (p : Pattern) (guard : d4902 p = 1) : d105 p ≤ (0 : Int) + d2325 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d105, d2325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14348 p hg
    simpa only [d105, d2325, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d105, d2325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14344 p hg
    simpa only [d105, d2325, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14350 (p : Pattern) (guard : d4902 p = 1) : d105 p ≤ (0 : Int) + d2326 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14345 p hg
    simpa only [d2326, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14349 p hg
    simpa only [d2326, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14351 (p : Pattern) (guard : d4902 p = 1) : d105 p ≤ (0 : Int) + d2327 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d105, d2327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14342 p hg
    simpa only [d105, d2327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d105, d2327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14344 p hg
    simpa only [d105, d2327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14352 (p : Pattern) (guard : d4902 p = 1) : d107 p ≤ (0 : Int) + d2328 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4902, d2328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2051 p hg
    simpa only [d4902, d2328, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4902, d2328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11614 p hg
    simpa only [d4902, d2328, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14353 (p : Pattern) (guard : d4902 p = 1) : d108 p ≤ (0 : Int) + d2329 p := by
  cases selected : p 204 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d108, d2329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14352 p hg
    simpa only [d108, d2329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d108, d2329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d108, d2329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14354 (p : Pattern) (guard : d4902 p = 1) : d109 p ≤ (0 : Int) + d2330 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d109, d2330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14352 p hg
    simpa only [d109, d2330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d109, d2330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14353 p hg
    simpa only [d109, d2330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14355 (p : Pattern) (guard : d4902 p = 1) : d110 p ≤ (0 : Int) + d2331 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d110, d2331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14351 p hg
    simpa only [d110, d2331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d110, d2331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14354 p hg
    simpa only [d110, d2331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14356 (p : Pattern) (guard : d4902 p = 1) : d111 p ≤ (0 : Int) + d2332 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d111, d2332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14350 p hg
    simpa only [d111, d2332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d111, d2332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14355 p hg
    simpa only [d111, d2332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14357 (p : Pattern) (guard : d4902 p = 1) : d112 p ≤ (0 : Int) + d2333 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d112, d2333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14259 p hg
    simpa only [d112, d2333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d112, d2333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d112, d2333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14358 (p : Pattern) (guard : d4902 p = 1) : d113 p ≤ (0 : Int) + d2334 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d113, d2334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14355 p hg
    simpa only [d113, d2334, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d113, d2334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14357 p hg
    simpa only [d113, d2334, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14359 (p : Pattern) (guard : d4902 p = 1) : d114 p ≤ (0 : Int) + d2335 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d114, d2335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14356 p hg
    simpa only [d114, d2335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d114, d2335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14358 p hg
    simpa only [d114, d2335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14360 (p : Pattern) (guard : d4902 p = 1) : d116 p ≤ (0 : Int) + d2336 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4902, d2336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d4902, d2336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4902, d2336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11639 p hg
    simpa only [d4902, d2336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14361 (p : Pattern) (guard : d4902 p = 1) : d117 p ≤ (0 : Int) + d2337 p := by
  cases selected : p 204 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d117, d2337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14360 p hg
    simpa only [d117, d2337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d117, d2337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d117, d2337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14362 (p : Pattern) (guard : d4902 p = 1) : d118 p ≤ (0 : Int) + d2338 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d118, d2338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14342 p hg
    simpa only [d118, d2338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d118, d2338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14361 p hg
    simpa only [d118, d2338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14363 (p : Pattern) (guard : d4902 p = 1) : d120 p ≤ (0 : Int) + d2339 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4902, d2339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3159 p hg
    simpa only [d4902, d2339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4902, d2339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11672 p hg
    simpa only [d4902, d2339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14364 (p : Pattern) (guard : d4902 p = 1) : d121 p ≤ (0 : Int) + d2340 p := by
  cases selected : p 204 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d121, d2340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14363 p hg
    simpa only [d121, d2340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d121, d2340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d121, d2340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14365 (p : Pattern) (guard : d4902 p = 1) : d122 p ≤ (0 : Int) + d2341 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d122, d2341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14342 p hg
    simpa only [d122, d2341, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d122, d2341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14364 p hg
    simpa only [d122, d2341, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14366 (p : Pattern) (guard : d4902 p = 1) : d123 p ≤ (0 : Int) + d2342 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d123, d2342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14362 p hg
    simpa only [d123, d2342, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d123, d2342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14365 p hg
    simpa only [d123, d2342, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14367 (p : Pattern) (guard : d4902 p = 1) : d124 p ≤ (0 : Int) + d2343 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d124, d2343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14342 p hg
    simpa only [d124, d2343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d124, d2343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d124, d2343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14368 (p : Pattern) (guard : d4902 p = 1) : d125 p ≤ (0 : Int) + d2344 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d125, d2344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14352 p hg
    simpa only [d125, d2344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d125, d2344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d125, d2344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14369 (p : Pattern) (guard : d4902 p = 1) : d126 p ≤ (0 : Int) + d2345 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d126, d2345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14367 p hg
    simpa only [d126, d2345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d126, d2345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14368 p hg
    simpa only [d126, d2345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14370 (p : Pattern) (guard : d4902 p = 1) : d127 p ≤ (0 : Int) + d2346 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d127, d2346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14366 p hg
    simpa only [d127, d2346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d127, d2346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14369 p hg
    simpa only [d127, d2346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14371 (p : Pattern) (guard : d4902 p = 1) : d128 p ≤ (0 : Int) + d2347 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d128, d2347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14269 p hg
    simpa only [d128, d2347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d128, d2347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d128, d2347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14372 (p : Pattern) (guard : d4902 p = 1) : d129 p ≤ (0 : Int) + d2348 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d129, d2348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14369 p hg
    simpa only [d129, d2348, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d129, d2348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14371 p hg
    simpa only [d129, d2348, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14373 (p : Pattern) (guard : d4902 p = 1) : d130 p ≤ (0 : Int) + d2349 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d130, d2349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14370 p hg
    simpa only [d130, d2349, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d130, d2349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14372 p hg
    simpa only [d130, d2349, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14374 (p : Pattern) (guard : d4902 p = 1) : d131 p ≤ (0 : Int) + d2350 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d131, d2350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14359 p hg
    simpa only [d131, d2350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d131, d2350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14373 p hg
    simpa only [d131, d2350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14375 (p : Pattern) (guard : d0 p = 1) : d103 p ≤ (0 : Int) + d330 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare14376 (p : Pattern) (guard : d4902 p = 1) : d103 p ≤ (0 : Int) + d2351 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4902, d2351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1274 p hg
    simpa only [d4902, d2351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4902, d2351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14375 p hg
    simpa only [d4902, d2351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14377 (p : Pattern) (guard : d4902 p = 1) : d103 p ≤ (0 : Int) + d2352 p := by
  cases selected : p 204 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14376 p hg
    simpa only [d2352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14342 p hg
    simpa only [d2352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14378 (p : Pattern) (guard : d4902 p = 1) : d105 p ≤ (0 : Int) + d2353 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d105, d2353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14377 p hg
    simpa only [d105, d2353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d105, d2353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14344 p hg
    simpa only [d105, d2353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14379 (p : Pattern) (guard : d4902 p = 1) : d132 p ≤ (0 : Int) + d2354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d132, d2354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14360 p hg
    simpa only [d132, d2354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d132, d2354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14361 p hg
    simpa only [d132, d2354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14380 (p : Pattern) (guard : d4902 p = 1) : d133 p ≤ (0 : Int) + d2355 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d133, d2355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14378 p hg
    simpa only [d133, d2355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d133, d2355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14379 p hg
    simpa only [d133, d2355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14381 (p : Pattern) (guard : d4902 p = 1) : d134 p ≤ (0 : Int) + d2356 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d134, d2356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14354 p hg
    simpa only [d134, d2356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d134, d2356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14259 p hg
    simpa only [d134, d2356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14382 (p : Pattern) (guard : d4902 p = 1) : d135 p ≤ (0 : Int) + d2357 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d135, d2357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14380 p hg
    simpa only [d135, d2357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d135, d2357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14381 p hg
    simpa only [d135, d2357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14383 (p : Pattern) (guard : d4902 p = 1) : d136 p ≤ (0 : Int) + d2358 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d136, d2358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14354 p hg
    simpa only [d136, d2358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d136, d2358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14261 p hg
    simpa only [d136, d2358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14384 (p : Pattern) (guard : d4902 p = 1) : d137 p ≤ (0 : Int) + d2359 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d137, d2359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14383 p hg
    simpa only [d137, d2359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d137, d2359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d137, d2359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14385 (p : Pattern) (guard : d4902 p = 1) : d138 p ≤ (0 : Int) + d2360 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d138, d2360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14382 p hg
    simpa only [d138, d2360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d138, d2360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14384 p hg
    simpa only [d138, d2360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14386 (p : Pattern) (guard : d4902 p = 1) : d139 p ≤ (0 : Int) + d2361 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d139, d2361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14360 p hg
    simpa only [d139, d2361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d139, d2361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d139, d2361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14387 (p : Pattern) (guard : d4902 p = 1) : d140 p ≤ (0 : Int) + d2362 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d140, d2362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14365 p hg
    simpa only [d140, d2362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d140, d2362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14386 p hg
    simpa only [d140, d2362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14388 (p : Pattern) (guard : d4902 p = 1) : d141 p ≤ (0 : Int) + d2363 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d141, d2363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14368 p hg
    simpa only [d141, d2363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d141, d2363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14269 p hg
    simpa only [d141, d2363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14389 (p : Pattern) (guard : d4902 p = 1) : d142 p ≤ (0 : Int) + d2364 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d142, d2364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14387 p hg
    simpa only [d142, d2364, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d142, d2364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14388 p hg
    simpa only [d142, d2364, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14390 (p : Pattern) (guard : d4902 p = 1) : d143 p ≤ (0 : Int) + d2365 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d143, d2365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14368 p hg
    simpa only [d143, d2365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d143, d2365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14271 p hg
    simpa only [d143, d2365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14391 (p : Pattern) (guard : d4902 p = 1) : d144 p ≤ (0 : Int) + d2366 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d144, d2366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14390 p hg
    simpa only [d144, d2366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d144, d2366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d144, d2366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14392 (p : Pattern) (guard : d4902 p = 1) : d145 p ≤ (0 : Int) + d2367 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d145, d2367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14389 p hg
    simpa only [d145, d2367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d145, d2367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14391 p hg
    simpa only [d145, d2367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14393 (p : Pattern) (guard : d4902 p = 1) : d146 p ≤ (0 : Int) + d2368 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d146, d2368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14385 p hg
    simpa only [d146, d2368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d146, d2368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14392 p hg
    simpa only [d146, d2368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14394 (p : Pattern) (guard : d4902 p = 1) : d147 p ≤ (0 : Int) + d2369 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d147, d2369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14374 p hg
    simpa only [d147, d2369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d147, d2369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14393 p hg
    simpa only [d147, d2369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14395 (p : Pattern) (guard : d4902 p = 1) : d111 p ≤ (0 : Int) + d2370 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d111, d2370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14351 p hg
    simpa only [d111, d2370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d111, d2370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14355 p hg
    simpa only [d111, d2370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14396 (p : Pattern) (guard : d4902 p = 1) : d114 p ≤ (0 : Int) + d2371 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d114, d2371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14395 p hg
    simpa only [d114, d2371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d114, d2371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14358 p hg
    simpa only [d114, d2371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14397 (p : Pattern) (guard : d4902 p = 1) : d148 p ≤ (0 : Int) + d2372 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d148, d2372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14363 p hg
    simpa only [d148, d2372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d148, d2372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14364 p hg
    simpa only [d148, d2372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14398 (p : Pattern) (guard : d4902 p = 1) : d149 p ≤ (0 : Int) + d2373 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d149, d2373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14379 p hg
    simpa only [d149, d2373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d149, d2373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14397 p hg
    simpa only [d149, d2373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14399 (p : Pattern) (guard : d4902 p = 1) : d150 p ≤ (0 : Int) + d2374 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d150, d2374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14398 p hg
    simpa only [d150, d2374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d150, d2374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d150, d2374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14400 (p : Pattern) (guard : d4902 p = 1) : d151 p ≤ (0 : Int) + d2375 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d151, d2375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14399 p hg
    simpa only [d151, d2375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d151, d2375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d151, d2375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14401 (p : Pattern) (guard : d4902 p = 1) : d152 p ≤ (0 : Int) + d2376 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d152, d2376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14396 p hg
    simpa only [d152, d2376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d152, d2376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14400 p hg
    simpa only [d152, d2376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14402 (p : Pattern) (guard : d4902 p = 1) : d133 p ≤ (0 : Int) + d2377 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d133, d2377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14351 p hg
    simpa only [d133, d2377, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d133, d2377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14379 p hg
    simpa only [d133, d2377, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14403 (p : Pattern) (guard : d4902 p = 1) : d135 p ≤ (0 : Int) + d2378 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d135, d2378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14402 p hg
    simpa only [d135, d2378, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d135, d2378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14381 p hg
    simpa only [d135, d2378, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14404 (p : Pattern) (guard : d4902 p = 1) : d138 p ≤ (0 : Int) + d2379 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d138, d2379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14403 p hg
    simpa only [d138, d2379, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d138, d2379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14384 p hg
    simpa only [d138, d2379, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14405 (p : Pattern) (guard : d4902 p = 1) : d153 p ≤ (0 : Int) + d2380 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d153, d2380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14397 p hg
    simpa only [d153, d2380, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d153, d2380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d153, d2380, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14406 (p : Pattern) (guard : d4902 p = 1) : d154 p ≤ (0 : Int) + d2381 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d154, d2381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14405 p hg
    simpa only [d154, d2381, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d154, d2381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d154, d2381, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14407 (p : Pattern) (guard : d4902 p = 1) : d155 p ≤ (0 : Int) + d2382 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d155, d2382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14406 p hg
    simpa only [d155, d2382, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d155, d2382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d155, d2382, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14408 (p : Pattern) (guard : d4902 p = 1) : d156 p ≤ (0 : Int) + d2383 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d156, d2383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14404 p hg
    simpa only [d156, d2383, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d156, d2383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14407 p hg
    simpa only [d156, d2383, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14409 (p : Pattern) (guard : d4902 p = 1) : d157 p ≤ (0 : Int) + d2384 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d157, d2384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14401 p hg
    simpa only [d157, d2384, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d157, d2384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14408 p hg
    simpa only [d157, d2384, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14410 (p : Pattern) (guard : d4902 p = 1) : d158 p ≤ (0 : Int) + d2385 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d158, d2385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14394 p hg
    simpa only [d158, d2385, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d158, d2385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14409 p hg
    simpa only [d158, d2385, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14411 (p : Pattern) (guard : d4902 p = 1) : d159 p ≤ (0 : Int) + d2386 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d159, d2386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14357 p hg
    simpa only [d159, d2386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d159, d2386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d159, d2386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14412 (p : Pattern) (guard : d4902 p = 1) : d160 p ≤ (0 : Int) + d2387 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d160, d2387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14411 p hg
    simpa only [d160, d2387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d160, d2387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d160, d2387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14413 (p : Pattern) (guard : d4902 p = 1) : d161 p ≤ (0 : Int) + d2388 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d161, d2388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14412 p hg
    simpa only [d161, d2388, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d161, d2388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d161, d2388, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14414 (p : Pattern) (guard : d4902 p = 1) : d162 p ≤ (0 : Int) + d2389 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d162, d2389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14413 p hg
    simpa only [d162, d2389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d162, d2389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d162, d2389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14415 (p : Pattern) (guard : d4902 p = 1) : d163 p ≤ (0 : Int) + d2390 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d163, d2390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14409 p hg
    simpa only [d163, d2390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d163, d2390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14414 p hg
    simpa only [d163, d2390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14416 (p : Pattern) (guard : d4902 p = 1) : d164 p ≤ (0 : Int) + d2391 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d164, d2391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14410 p hg
    simpa only [d164, d2391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d164, d2391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14415 p hg
    simpa only [d164, d2391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14417 (p : Pattern) (guard : d4902 p = 1) : d105 p ≤ (0 : Int) + d2392 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14349 p hg
    simpa only [d2392, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14351 p hg
    simpa only [d2392, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14418 (p : Pattern) (guard : d4902 p = 1) : d111 p ≤ (0 : Int) + d2393 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d111, d2393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14417 p hg
    simpa only [d111, d2393, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d111, d2393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14355 p hg
    simpa only [d111, d2393, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14419 (p : Pattern) (guard : d4902 p = 1) : d114 p ≤ (0 : Int) + d2394 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d114, d2394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14418 p hg
    simpa only [d114, d2394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d114, d2394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14358 p hg
    simpa only [d114, d2394, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
