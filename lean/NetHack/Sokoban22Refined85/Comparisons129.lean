/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons128
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare18060 (p : Pattern) (guard : d4902 p = 1) : d2264 p ≤ (0 : Int) + d56 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2264, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18059 p hg
    simpa only [d2264, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2264, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18030 p hg
    simpa only [d2264, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18061 (p : Pattern) (guard : d4902 p = 1) : d2265 p ≤ (0 : Int) + d65 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2265, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18060 p hg
    simpa only [d2265, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2265, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18038 p hg
    simpa only [d2265, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18062 (p : Pattern) (guard : d4902 p = 1) : d2266 p ≤ (0 : Int) + d83 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2266, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18054 p hg
    simpa only [d2266, d83, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2266, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d2266, d83, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18063 (p : Pattern) (guard : d4902 p = 1) : d2267 p ≤ (0 : Int) + d84 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2267, d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18062 p hg
    simpa only [d2267, d84, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2267, d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d2267, d84, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18064 (p : Pattern) (guard : d4902 p = 1) : d2268 p ≤ (0 : Int) + d85 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2268, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18063 p hg
    simpa only [d2268, d85, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2268, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d2268, d85, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18065 (p : Pattern) (guard : d4902 p = 1) : d2269 p ≤ (0 : Int) + d86 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2269, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18061 p hg
    simpa only [d2269, d86, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2269, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18064 p hg
    simpa only [d2269, d86, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18066 (p : Pattern) (guard : d4902 p = 1) : d2270 p ≤ (0 : Int) + d87 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2270, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18058 p hg
    simpa only [d2270, d87, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2270, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18065 p hg
    simpa only [d2270, d87, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18067 (p : Pattern) (guard : d4902 p = 1) : d2271 p ≤ (0 : Int) + d88 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2271, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18051 p hg
    simpa only [d2271, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2271, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18066 p hg
    simpa only [d2271, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18068 (p : Pattern) (guard : d4902 p = 1) : d2272 p ≤ (0 : Int) + d16 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17990 p hg
    simpa only [d2272, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17996 p hg
    simpa only [d2272, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18069 (p : Pattern) (guard : d4902 p = 1) : d2273 p ≤ (0 : Int) + d22 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2273, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18068 p hg
    simpa only [d2273, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2273, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17997 p hg
    simpa only [d2273, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18070 (p : Pattern) (guard : d4902 p = 1) : d2274 p ≤ (0 : Int) + d29 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2274, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18069 p hg
    simpa only [d2274, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2274, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18002 p hg
    simpa only [d2274, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18071 (p : Pattern) (guard : d4902 p = 1) : d2275 p ≤ (0 : Int) + d82 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2275, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18070 p hg
    simpa only [d2275, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2275, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18057 p hg
    simpa only [d2275, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18072 (p : Pattern) (guard : d4902 p = 1) : d2276 p ≤ (0 : Int) + d87 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2276, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18071 p hg
    simpa only [d2276, d87, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2276, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18065 p hg
    simpa only [d2276, d87, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18073 (p : Pattern) (guard : d4902 p = 1) : d2277 p ≤ (0 : Int) + d89 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2277, d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18000 p hg
    simpa only [d2277, d89, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2277, d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18036 p hg
    simpa only [d2277, d89, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18074 (p : Pattern) (guard : d4902 p = 1) : d2278 p ≤ (0 : Int) + d90 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2278, d90, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18073 p hg
    simpa only [d2278, d90, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2278, d90, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18037 p hg
    simpa only [d2278, d90, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18075 (p : Pattern) (guard : d4902 p = 1) : d2279 p ≤ (0 : Int) + d91 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2279, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18037 p hg
    simpa only [d2279, d91, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2279, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d2279, d91, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18076 (p : Pattern) (guard : d4902 p = 1) : d2280 p ≤ (0 : Int) + d92 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2280, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18074 p hg
    simpa only [d2280, d92, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2280, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18075 p hg
    simpa only [d2280, d92, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18077 (p : Pattern) (guard : d4902 p = 1) : d2281 p ≤ (0 : Int) + d93 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2281, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18075 p hg
    simpa only [d2281, d93, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2281, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d2281, d93, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18078 (p : Pattern) (guard : d4902 p = 1) : d2282 p ≤ (0 : Int) + d94 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2282, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18076 p hg
    simpa only [d2282, d94, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2282, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18077 p hg
    simpa only [d2282, d94, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18079 (p : Pattern) (guard : d4902 p = 1) : d2283 p ≤ (0 : Int) + d95 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2283, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18077 p hg
    simpa only [d2283, d95, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2283, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d2283, d95, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18080 (p : Pattern) (guard : d4902 p = 1) : d2284 p ≤ (0 : Int) + d96 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2284, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18078 p hg
    simpa only [d2284, d96, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2284, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18079 p hg
    simpa only [d2284, d96, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18081 (p : Pattern) (guard : d4902 p = 1) : d2285 p ≤ (0 : Int) + d97 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2285, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18072 p hg
    simpa only [d2285, d97, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2285, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18080 p hg
    simpa only [d2285, d97, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18082 (p : Pattern) (guard : d4902 p = 1) : d2286 p ≤ (0 : Int) + d98 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2286, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18067 p hg
    simpa only [d2286, d98, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2286, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18081 p hg
    simpa only [d2286, d98, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18083 (p : Pattern) (guard : d4902 p = 1) : d2287 p ≤ (0 : Int) + d16 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17985 p hg
    simpa only [d2287, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17996 p hg
    simpa only [d2287, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18084 (p : Pattern) (guard : d4902 p = 1) : d2288 p ≤ (0 : Int) + d22 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2288, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18083 p hg
    simpa only [d2288, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2288, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17997 p hg
    simpa only [d2288, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18085 (p : Pattern) (guard : d4902 p = 1) : d2289 p ≤ (0 : Int) + d29 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2289, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18084 p hg
    simpa only [d2289, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2289, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18002 p hg
    simpa only [d2289, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18086 (p : Pattern) (guard : d4902 p = 1) : d2290 p ≤ (0 : Int) + d52 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2290, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18085 p hg
    simpa only [d2290, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2290, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18022 p hg
    simpa only [d2290, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18087 (p : Pattern) (guard : d4902 p = 1) : d2291 p ≤ (0 : Int) + d76 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2291, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18061 p hg
    simpa only [d2291, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2291, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18049 p hg
    simpa only [d2291, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18088 (p : Pattern) (guard : d4902 p = 1) : d2292 p ≤ (0 : Int) + d77 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2292, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18086 p hg
    simpa only [d2292, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2292, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18087 p hg
    simpa only [d2292, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18089 (p : Pattern) (guard : d4902 p = 1) : d2293 p ≤ (0 : Int) + d88 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2293, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18088 p hg
    simpa only [d2293, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2293, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18066 p hg
    simpa only [d2293, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18090 (p : Pattern) (guard : d4902 p = 1) : d2294 p ≤ (0 : Int) + d99 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2294, d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18066 p hg
    simpa only [d2294, d99, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2294, d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d2294, d99, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18091 (p : Pattern) (guard : d4902 p = 1) : d2295 p ≤ (0 : Int) + d100 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2295, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18089 p hg
    simpa only [d2295, d100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2295, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18090 p hg
    simpa only [d2295, d100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18092 (p : Pattern) (guard : d4902 p = 1) : d2296 p ≤ (0 : Int) + d101 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2296, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18082 p hg
    simpa only [d2296, d101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2296, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18091 p hg
    simpa only [d2296, d101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18093 (p : Pattern) (guard : d0 p = 1) : d320 p ≤ (0 : Int) + d14 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare18094 (p : Pattern) (guard : d4902 p = 1) : d2297 p ≤ (0 : Int) + d14 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4902, d2297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1207 p hg
    simpa only [d4902, d2297, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4902, d2297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18093 p hg
    simpa only [d4902, d2297, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18095 (p : Pattern) (guard : d4902 p = 1) : d2298 p ≤ (0 : Int) + d14 p := by
  cases selected : p 204 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18094 p hg
    simpa only [d2298, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17978 p hg
    simpa only [d2298, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18096 (p : Pattern) (guard : d4902 p = 1) : d2299 p ≤ (0 : Int) + d16 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2299, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18095 p hg
    simpa only [d2299, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2299, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17980 p hg
    simpa only [d2299, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18097 (p : Pattern) (guard : d4902 p = 1) : d2300 p ≤ (0 : Int) + d16 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18096 p hg
    simpa only [d2300, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17990 p hg
    simpa only [d2300, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18098 (p : Pattern) (guard : d4902 p = 1) : d2301 p ≤ (0 : Int) + d22 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2301, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18097 p hg
    simpa only [d2301, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2301, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17997 p hg
    simpa only [d2301, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18099 (p : Pattern) (guard : d4902 p = 1) : d2302 p ≤ (0 : Int) + d29 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2302, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18098 p hg
    simpa only [d2302, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2302, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18002 p hg
    simpa only [d2302, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18100 (p : Pattern) (guard : d4902 p = 1) : d2303 p ≤ (0 : Int) + d52 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2303, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18099 p hg
    simpa only [d2303, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2303, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18022 p hg
    simpa only [d2303, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18101 (p : Pattern) (guard : d4902 p = 1) : d2304 p ≤ (0 : Int) + d54 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2304, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17985 p hg
    simpa only [d2304, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2304, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18028 p hg
    simpa only [d2304, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18102 (p : Pattern) (guard : d4902 p = 1) : d2305 p ≤ (0 : Int) + d56 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2305, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18101 p hg
    simpa only [d2305, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2305, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18030 p hg
    simpa only [d2305, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18103 (p : Pattern) (guard : d4902 p = 1) : d2306 p ≤ (0 : Int) + d65 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2306, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18102 p hg
    simpa only [d2306, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2306, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18038 p hg
    simpa only [d2306, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18104 (p : Pattern) (guard : d4902 p = 1) : d2307 p ≤ (0 : Int) + d76 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2307, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18103 p hg
    simpa only [d2307, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2307, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18049 p hg
    simpa only [d2307, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18105 (p : Pattern) (guard : d4902 p = 1) : d2308 p ≤ (0 : Int) + d77 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2308, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18100 p hg
    simpa only [d2308, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2308, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18104 p hg
    simpa only [d2308, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18106 (p : Pattern) (guard : d4902 p = 1) : d2309 p ≤ (0 : Int) + d88 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2309, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18105 p hg
    simpa only [d2309, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2309, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18066 p hg
    simpa only [d2309, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18107 (p : Pattern) (guard : d4902 p = 1) : d2310 p ≤ (0 : Int) + d97 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2310, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18066 p hg
    simpa only [d2310, d97, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2310, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18080 p hg
    simpa only [d2310, d97, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18108 (p : Pattern) (guard : d4902 p = 1) : d2311 p ≤ (0 : Int) + d98 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2311, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18106 p hg
    simpa only [d2311, d98, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2311, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18107 p hg
    simpa only [d2311, d98, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18109 (p : Pattern) (guard : d4902 p = 1) : d2312 p ≤ (0 : Int) + d52 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2312, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18070 p hg
    simpa only [d2312, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2312, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18022 p hg
    simpa only [d2312, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18110 (p : Pattern) (guard : d4902 p = 1) : d2313 p ≤ (0 : Int) + d77 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2313, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18109 p hg
    simpa only [d2313, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2313, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18087 p hg
    simpa only [d2313, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18111 (p : Pattern) (guard : d4902 p = 1) : d2314 p ≤ (0 : Int) + d88 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2314, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18110 p hg
    simpa only [d2314, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2314, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18066 p hg
    simpa only [d2314, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18112 (p : Pattern) (guard : d4902 p = 1) : d2315 p ≤ (0 : Int) + d100 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2315, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18111 p hg
    simpa only [d2315, d100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2315, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18090 p hg
    simpa only [d2315, d100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18113 (p : Pattern) (guard : d4902 p = 1) : d2316 p ≤ (0 : Int) + d101 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2316, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18108 p hg
    simpa only [d2316, d101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2316, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18112 p hg
    simpa only [d2316, d101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18114 (p : Pattern) (guard : d4902 p = 1) : d2317 p ≤ (0 : Int) + d101 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18092 p hg
    simpa only [d2317, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18113 p hg
    simpa only [d2317, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18115 (p : Pattern) (guard : d0 p = 1) : d320 p ≤ (0 : Int) + d103 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare18116 (p : Pattern) (guard : d4902 p = 1) : d2318 p ≤ (0 : Int) + d103 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4902, d2318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1274 p hg
    simpa only [d4902, d2318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4902, d2318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18115 p hg
    simpa only [d4902, d2318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18117 (p : Pattern) (guard : d4902 p = 1) : d2319 p ≤ (0 : Int) + d103 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4902, d2319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1274 p hg
    simpa only [d4902, d2319, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4902, d2319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5749 p hg
    simpa only [d4902, d2319, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18118 (p : Pattern) (guard : d4902 p = 1) : d2320 p ≤ (0 : Int) + d103 p := by
  cases selected : p 204 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18116 p hg
    simpa only [d2320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18117 p hg
    simpa only [d2320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18119 (p : Pattern) (guard : d4902 p = 1) : d2321 p ≤ (0 : Int) + d104 p := by
  cases selected : p 204 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2321, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18117 p hg
    simpa only [d2321, d104, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2321, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d2321, d104, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18120 (p : Pattern) (guard : d4902 p = 1) : d2322 p ≤ (0 : Int) + d105 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2322, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18118 p hg
    simpa only [d2322, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2322, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18119 p hg
    simpa only [d2322, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18121 (p : Pattern) (guard : d0 p = 1) : d332 p ≤ (0 : Int) + d103 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare18122 (p : Pattern) (guard : d4902 p = 1) : d2323 p ≤ (0 : Int) + d103 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4902, d2323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1274 p hg
    simpa only [d4902, d2323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4902, d2323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18121 p hg
    simpa only [d4902, d2323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18123 (p : Pattern) (guard : d4902 p = 1) : d2324 p ≤ (0 : Int) + d103 p := by
  cases selected : p 204 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18122 p hg
    simpa only [d2324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18117 p hg
    simpa only [d2324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18124 (p : Pattern) (guard : d4902 p = 1) : d2325 p ≤ (0 : Int) + d105 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2325, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18123 p hg
    simpa only [d2325, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2325, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18119 p hg
    simpa only [d2325, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18125 (p : Pattern) (guard : d4902 p = 1) : d2326 p ≤ (0 : Int) + d105 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18120 p hg
    simpa only [d2326, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18124 p hg
    simpa only [d2326, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18126 (p : Pattern) (guard : d4902 p = 1) : d2327 p ≤ (0 : Int) + d105 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2327, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18117 p hg
    simpa only [d2327, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2327, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18119 p hg
    simpa only [d2327, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18127 (p : Pattern) (guard : d4902 p = 1) : d2328 p ≤ (0 : Int) + d107 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4902, d2328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2051 p hg
    simpa only [d4902, d2328, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4902, d2328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5753 p hg
    simpa only [d4902, d2328, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18128 (p : Pattern) (guard : d4902 p = 1) : d2329 p ≤ (0 : Int) + d108 p := by
  cases selected : p 204 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2329, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18127 p hg
    simpa only [d2329, d108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2329, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d2329, d108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18129 (p : Pattern) (guard : d4902 p = 1) : d2330 p ≤ (0 : Int) + d109 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2330, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18127 p hg
    simpa only [d2330, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2330, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18128 p hg
    simpa only [d2330, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18130 (p : Pattern) (guard : d4902 p = 1) : d2331 p ≤ (0 : Int) + d110 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2331, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18126 p hg
    simpa only [d2331, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2331, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18129 p hg
    simpa only [d2331, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18131 (p : Pattern) (guard : d4902 p = 1) : d2332 p ≤ (0 : Int) + d111 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2332, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18125 p hg
    simpa only [d2332, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2332, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18130 p hg
    simpa only [d2332, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18132 (p : Pattern) (guard : d4902 p = 1) : d2333 p ≤ (0 : Int) + d112 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2333, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18034 p hg
    simpa only [d2333, d112, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2333, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d2333, d112, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18133 (p : Pattern) (guard : d4902 p = 1) : d2334 p ≤ (0 : Int) + d113 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2334, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18130 p hg
    simpa only [d2334, d113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2334, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18132 p hg
    simpa only [d2334, d113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18134 (p : Pattern) (guard : d4902 p = 1) : d2335 p ≤ (0 : Int) + d114 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2335, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18131 p hg
    simpa only [d2335, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2335, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18133 p hg
    simpa only [d2335, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18135 (p : Pattern) (guard : d4902 p = 1) : d2336 p ≤ (0 : Int) + d116 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4902, d2336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d4902, d2336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4902, d2336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5764 p hg
    simpa only [d4902, d2336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18136 (p : Pattern) (guard : d4902 p = 1) : d2337 p ≤ (0 : Int) + d117 p := by
  cases selected : p 204 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2337, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18135 p hg
    simpa only [d2337, d117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2337, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d2337, d117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18137 (p : Pattern) (guard : d4902 p = 1) : d2338 p ≤ (0 : Int) + d118 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2338, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18117 p hg
    simpa only [d2338, d118, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2338, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18136 p hg
    simpa only [d2338, d118, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18138 (p : Pattern) (guard : d4902 p = 1) : d2339 p ≤ (0 : Int) + d120 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4902, d2339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3159 p hg
    simpa only [d4902, d2339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4902, d2339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5854 p hg
    simpa only [d4902, d2339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18139 (p : Pattern) (guard : d4902 p = 1) : d2340 p ≤ (0 : Int) + d121 p := by
  cases selected : p 204 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2340, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18138 p hg
    simpa only [d2340, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2340, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d2340, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18140 (p : Pattern) (guard : d4902 p = 1) : d2341 p ≤ (0 : Int) + d122 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2341, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18117 p hg
    simpa only [d2341, d122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2341, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18139 p hg
    simpa only [d2341, d122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18141 (p : Pattern) (guard : d4902 p = 1) : d2342 p ≤ (0 : Int) + d123 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2342, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18137 p hg
    simpa only [d2342, d123, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2342, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18140 p hg
    simpa only [d2342, d123, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18142 (p : Pattern) (guard : d4902 p = 1) : d2343 p ≤ (0 : Int) + d124 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2343, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18117 p hg
    simpa only [d2343, d124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2343, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d2343, d124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18143 (p : Pattern) (guard : d4902 p = 1) : d2344 p ≤ (0 : Int) + d125 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2344, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18127 p hg
    simpa only [d2344, d125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2344, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d2344, d125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18144 (p : Pattern) (guard : d4902 p = 1) : d2345 p ≤ (0 : Int) + d126 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2345, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18142 p hg
    simpa only [d2345, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2345, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18143 p hg
    simpa only [d2345, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18145 (p : Pattern) (guard : d4902 p = 1) : d2346 p ≤ (0 : Int) + d127 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2346, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18141 p hg
    simpa only [d2346, d127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2346, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18144 p hg
    simpa only [d2346, d127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18146 (p : Pattern) (guard : d4902 p = 1) : d2347 p ≤ (0 : Int) + d128 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2347, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18044 p hg
    simpa only [d2347, d128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2347, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d2347, d128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18147 (p : Pattern) (guard : d4902 p = 1) : d2348 p ≤ (0 : Int) + d129 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2348, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18144 p hg
    simpa only [d2348, d129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2348, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18146 p hg
    simpa only [d2348, d129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18148 (p : Pattern) (guard : d4902 p = 1) : d2349 p ≤ (0 : Int) + d130 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2349, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18145 p hg
    simpa only [d2349, d130, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2349, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18147 p hg
    simpa only [d2349, d130, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18149 (p : Pattern) (guard : d4902 p = 1) : d2350 p ≤ (0 : Int) + d131 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2350, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18134 p hg
    simpa only [d2350, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2350, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18148 p hg
    simpa only [d2350, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18150 (p : Pattern) (guard : d0 p = 1) : d330 p ≤ (0 : Int) + d103 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare18151 (p : Pattern) (guard : d4902 p = 1) : d2351 p ≤ (0 : Int) + d103 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4902, d2351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1274 p hg
    simpa only [d4902, d2351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4902, d2351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18150 p hg
    simpa only [d4902, d2351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18152 (p : Pattern) (guard : d4902 p = 1) : d2352 p ≤ (0 : Int) + d103 p := by
  cases selected : p 204 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18151 p hg
    simpa only [d2352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18117 p hg
    simpa only [d2352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18153 (p : Pattern) (guard : d4902 p = 1) : d2353 p ≤ (0 : Int) + d105 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2353, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18152 p hg
    simpa only [d2353, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2353, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18119 p hg
    simpa only [d2353, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18154 (p : Pattern) (guard : d4902 p = 1) : d2354 p ≤ (0 : Int) + d132 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2354, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18135 p hg
    simpa only [d2354, d132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2354, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18136 p hg
    simpa only [d2354, d132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18155 (p : Pattern) (guard : d4902 p = 1) : d2355 p ≤ (0 : Int) + d133 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2355, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18153 p hg
    simpa only [d2355, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2355, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18154 p hg
    simpa only [d2355, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18156 (p : Pattern) (guard : d4902 p = 1) : d2356 p ≤ (0 : Int) + d134 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2356, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18129 p hg
    simpa only [d2356, d134, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2356, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18034 p hg
    simpa only [d2356, d134, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18157 (p : Pattern) (guard : d4902 p = 1) : d2357 p ≤ (0 : Int) + d135 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2357, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18155 p hg
    simpa only [d2357, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2357, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18156 p hg
    simpa only [d2357, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18158 (p : Pattern) (guard : d4902 p = 1) : d2358 p ≤ (0 : Int) + d136 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2358, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18129 p hg
    simpa only [d2358, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2358, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18036 p hg
    simpa only [d2358, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18159 (p : Pattern) (guard : d4902 p = 1) : d2359 p ≤ (0 : Int) + d137 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2359, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18158 p hg
    simpa only [d2359, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2359, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d2359, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18160 (p : Pattern) (guard : d4902 p = 1) : d2360 p ≤ (0 : Int) + d138 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2360, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18157 p hg
    simpa only [d2360, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2360, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18159 p hg
    simpa only [d2360, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18161 (p : Pattern) (guard : d4902 p = 1) : d2361 p ≤ (0 : Int) + d139 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2361, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18135 p hg
    simpa only [d2361, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2361, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d2361, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18162 (p : Pattern) (guard : d4902 p = 1) : d2362 p ≤ (0 : Int) + d140 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2362, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18140 p hg
    simpa only [d2362, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2362, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18161 p hg
    simpa only [d2362, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18163 (p : Pattern) (guard : d4902 p = 1) : d2363 p ≤ (0 : Int) + d141 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2363, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18143 p hg
    simpa only [d2363, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2363, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18044 p hg
    simpa only [d2363, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18164 (p : Pattern) (guard : d4902 p = 1) : d2364 p ≤ (0 : Int) + d142 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2364, d142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18162 p hg
    simpa only [d2364, d142, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2364, d142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18163 p hg
    simpa only [d2364, d142, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18165 (p : Pattern) (guard : d4902 p = 1) : d2365 p ≤ (0 : Int) + d143 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2365, d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18143 p hg
    simpa only [d2365, d143, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2365, d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18046 p hg
    simpa only [d2365, d143, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18166 (p : Pattern) (guard : d4902 p = 1) : d2366 p ≤ (0 : Int) + d144 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2366, d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18165 p hg
    simpa only [d2366, d144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2366, d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d2366, d144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18167 (p : Pattern) (guard : d4902 p = 1) : d2367 p ≤ (0 : Int) + d145 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2367, d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18164 p hg
    simpa only [d2367, d145, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2367, d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18166 p hg
    simpa only [d2367, d145, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18168 (p : Pattern) (guard : d4902 p = 1) : d2368 p ≤ (0 : Int) + d146 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2368, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18160 p hg
    simpa only [d2368, d146, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2368, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18167 p hg
    simpa only [d2368, d146, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18169 (p : Pattern) (guard : d4902 p = 1) : d2369 p ≤ (0 : Int) + d147 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2369, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18149 p hg
    simpa only [d2369, d147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2369, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18168 p hg
    simpa only [d2369, d147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18170 (p : Pattern) (guard : d4902 p = 1) : d2370 p ≤ (0 : Int) + d111 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2370, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18126 p hg
    simpa only [d2370, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2370, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18130 p hg
    simpa only [d2370, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18171 (p : Pattern) (guard : d4902 p = 1) : d2371 p ≤ (0 : Int) + d114 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2371, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18170 p hg
    simpa only [d2371, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2371, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18133 p hg
    simpa only [d2371, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18172 (p : Pattern) (guard : d4902 p = 1) : d2372 p ≤ (0 : Int) + d148 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2372, d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18138 p hg
    simpa only [d2372, d148, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2372, d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18139 p hg
    simpa only [d2372, d148, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18173 (p : Pattern) (guard : d4902 p = 1) : d2373 p ≤ (0 : Int) + d149 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2373, d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18154 p hg
    simpa only [d2373, d149, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2373, d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18172 p hg
    simpa only [d2373, d149, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18174 (p : Pattern) (guard : d4902 p = 1) : d2374 p ≤ (0 : Int) + d150 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2374, d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18173 p hg
    simpa only [d2374, d150, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2374, d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d2374, d150, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18175 (p : Pattern) (guard : d4902 p = 1) : d2375 p ≤ (0 : Int) + d151 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2375, d151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18174 p hg
    simpa only [d2375, d151, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2375, d151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d2375, d151, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18176 (p : Pattern) (guard : d4902 p = 1) : d2376 p ≤ (0 : Int) + d152 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2376, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18171 p hg
    simpa only [d2376, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2376, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18175 p hg
    simpa only [d2376, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18177 (p : Pattern) (guard : d4902 p = 1) : d2377 p ≤ (0 : Int) + d133 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2377, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18126 p hg
    simpa only [d2377, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2377, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18154 p hg
    simpa only [d2377, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18178 (p : Pattern) (guard : d4902 p = 1) : d2378 p ≤ (0 : Int) + d135 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2378, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18177 p hg
    simpa only [d2378, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2378, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18156 p hg
    simpa only [d2378, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18179 (p : Pattern) (guard : d4902 p = 1) : d2379 p ≤ (0 : Int) + d138 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2379, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18178 p hg
    simpa only [d2379, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2379, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18159 p hg
    simpa only [d2379, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18180 (p : Pattern) (guard : d4902 p = 1) : d2380 p ≤ (0 : Int) + d153 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2380, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18172 p hg
    simpa only [d2380, d153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2380, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d2380, d153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18181 (p : Pattern) (guard : d4902 p = 1) : d2381 p ≤ (0 : Int) + d154 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2381, d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18180 p hg
    simpa only [d2381, d154, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2381, d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d2381, d154, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18182 (p : Pattern) (guard : d4902 p = 1) : d2382 p ≤ (0 : Int) + d155 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2382, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18181 p hg
    simpa only [d2382, d155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2382, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d2382, d155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18183 (p : Pattern) (guard : d4902 p = 1) : d2383 p ≤ (0 : Int) + d156 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2383, d156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18179 p hg
    simpa only [d2383, d156, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2383, d156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18182 p hg
    simpa only [d2383, d156, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18184 (p : Pattern) (guard : d4902 p = 1) : d2384 p ≤ (0 : Int) + d157 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2384, d157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18176 p hg
    simpa only [d2384, d157, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2384, d157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18183 p hg
    simpa only [d2384, d157, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18185 (p : Pattern) (guard : d4902 p = 1) : d2385 p ≤ (0 : Int) + d158 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2385, d158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18169 p hg
    simpa only [d2385, d158, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2385, d158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18184 p hg
    simpa only [d2385, d158, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18186 (p : Pattern) (guard : d4902 p = 1) : d2386 p ≤ (0 : Int) + d159 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2386, d159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18132 p hg
    simpa only [d2386, d159, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2386, d159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d2386, d159, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18187 (p : Pattern) (guard : d4902 p = 1) : d2387 p ≤ (0 : Int) + d160 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2387, d160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18186 p hg
    simpa only [d2387, d160, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2387, d160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d2387, d160, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18188 (p : Pattern) (guard : d4902 p = 1) : d2388 p ≤ (0 : Int) + d161 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2388, d161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18187 p hg
    simpa only [d2388, d161, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2388, d161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d2388, d161, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18189 (p : Pattern) (guard : d4902 p = 1) : d2389 p ≤ (0 : Int) + d162 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2389, d162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18188 p hg
    simpa only [d2389, d162, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2389, d162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d2389, d162, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18190 (p : Pattern) (guard : d4902 p = 1) : d2390 p ≤ (0 : Int) + d163 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2390, d163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18184 p hg
    simpa only [d2390, d163, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2390, d163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18189 p hg
    simpa only [d2390, d163, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18191 (p : Pattern) (guard : d4902 p = 1) : d2391 p ≤ (0 : Int) + d164 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2391, d164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18185 p hg
    simpa only [d2391, d164, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2391, d164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18190 p hg
    simpa only [d2391, d164, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18192 (p : Pattern) (guard : d4902 p = 1) : d2392 p ≤ (0 : Int) + d105 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18124 p hg
    simpa only [d2392, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18126 p hg
    simpa only [d2392, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18193 (p : Pattern) (guard : d4902 p = 1) : d2393 p ≤ (0 : Int) + d111 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2393, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18192 p hg
    simpa only [d2393, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2393, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18130 p hg
    simpa only [d2393, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18194 (p : Pattern) (guard : d4902 p = 1) : d2394 p ≤ (0 : Int) + d114 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2394, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18193 p hg
    simpa only [d2394, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2394, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18133 p hg
    simpa only [d2394, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18195 (p : Pattern) (guard : d4902 p = 1) : d2395 p ≤ (0 : Int) + d131 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2395, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18194 p hg
    simpa only [d2395, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2395, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18148 p hg
    simpa only [d2395, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18196 (p : Pattern) (guard : d4902 p = 1) : d2396 p ≤ (0 : Int) + d146 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2396, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18179 p hg
    simpa only [d2396, d146, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2396, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18167 p hg
    simpa only [d2396, d146, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18197 (p : Pattern) (guard : d4902 p = 1) : d2397 p ≤ (0 : Int) + d147 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2397, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18195 p hg
    simpa only [d2397, d147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2397, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18196 p hg
    simpa only [d2397, d147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18198 (p : Pattern) (guard : d4902 p = 1) : d2398 p ≤ (0 : Int) + d158 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2398, d158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18197 p hg
    simpa only [d2398, d158, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2398, d158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18184 p hg
    simpa only [d2398, d158, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18199 (p : Pattern) (guard : d4902 p = 1) : d2399 p ≤ (0 : Int) + d165 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2399, d165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18184 p hg
    simpa only [d2399, d165, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2399, d165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d2399, d165, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
